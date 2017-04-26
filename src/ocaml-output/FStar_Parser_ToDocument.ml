open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app b printer t =
  let b0 = FStar_ST.read should_print_fs_typ_app in
  FStar_ST.write should_print_fs_typ_app b;
  (let res = printer t in FStar_ST.write should_print_fs_typ_app b0; res)
let should_unparen: Prims.bool FStar_ST.ref = FStar_Util.mk_ref true
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____44 =
      let uu____45 = FStar_ST.read should_unparen in
      Prims.op_Negation uu____45 in
    if uu____44
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____50 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map n1 f x = match x with | None  -> n1 | Some x' -> f x'
let prefix2:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
let op_Hat_Slash_Plus_Hat:
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body
let jump2: FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
let infix2:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1")
let infix0:
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1")
let break1: FStar_Pprint.document = FStar_Pprint.break_ (Prims.parse_int "1")
let separate_break_map sep f l =
  let uu____132 =
    let uu____133 =
      let uu____134 = FStar_Pprint.op_Hat_Hat sep break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____134 in
    FStar_Pprint.separate_map uu____133 f l in
  FStar_Pprint.group uu____132
let precede_break_separate_map prec sep f l =
  let uu____164 =
    let uu____165 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
    let uu____166 =
      let uu____167 = FStar_List.hd l in FStar_All.pipe_right uu____167 f in
    FStar_Pprint.precede uu____165 uu____166 in
  let uu____168 =
    let uu____169 = FStar_List.tl l in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____172 =
           let uu____173 =
             let uu____174 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____174 in
           FStar_Pprint.op_Hat_Hat sep uu____173 in
         FStar_Pprint.op_Hat_Hat break1 uu____172) uu____169 in
  FStar_Pprint.op_Hat_Hat uu____164 uu____168
let concat_break_map f l =
  let uu____194 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____196 = f x in FStar_Pprint.op_Hat_Hat uu____196 break1) l in
  FStar_Pprint.group uu____194
let parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let soft_parens_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
let braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let soft_braces_with_nesting: FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
let brackets_with_nesting: FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_brackets_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
let soft_begin_end_with_nesting:
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____218 = str "begin" in
    let uu____219 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____218 contents uu____219
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____299 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____299 closing)
let doc_of_fsdoc:
  (Prims.string* (Prims.string* Prims.string) Prims.list) ->
    FStar_Pprint.document
  =
  fun uu____307  ->
    match uu____307 with
    | (comment,keywords1) ->
        let uu____321 =
          let uu____322 =
            let uu____324 = str comment in
            let uu____325 =
              let uu____327 =
                let uu____329 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____332  ->
                       match uu____332 with
                       | (k,v1) ->
                           let uu____337 =
                             let uu____339 = str k in
                             let uu____340 =
                               let uu____342 =
                                 let uu____344 = str v1 in [uu____344] in
                               FStar_Pprint.rarrow :: uu____342 in
                             uu____339 :: uu____340 in
                           FStar_Pprint.concat uu____337) keywords1 in
                [uu____329] in
              FStar_Pprint.space :: uu____327 in
            uu____324 :: uu____325 in
          FStar_Pprint.concat uu____322 in
        FStar_Pprint.group uu____321
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____348 =
      let uu____349 = unparen e in uu____349.FStar_Parser_AST.tm in
    match uu____348 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____350 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____357 =
        let uu____358 = unparen t in uu____358.FStar_Parser_AST.tm in
      match uu____357 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____360 -> false
let is_tuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_tuple_data_lid'
let is_dtuple_constructor: FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_dtuple_data_lid'
let is_list_structure:
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        let uu____377 =
          let uu____378 = unparen e in uu____378.FStar_Parser_AST.tm in
        match uu____377 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____386::(e2,uu____388)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____400 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____409 =
      let uu____410 = unparen e in uu____410.FStar_Parser_AST.tm in
    match uu____409 with
    | FStar_Parser_AST.Construct (uu____412,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____418,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____430 = extract_from_list e2 in e1 :: uu____430
    | uu____432 ->
        let uu____433 =
          let uu____434 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____434 in
        failwith uu____433
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____439 =
      let uu____440 = unparen e in uu____440.FStar_Parser_AST.tm in
    match uu____439 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____442;
           FStar_Parser_AST.level = uu____443;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____445 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____449 =
      let uu____450 = unparen e in uu____450.FStar_Parser_AST.tm in
    match uu____449 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____453;
           FStar_Parser_AST.level = uu____454;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____456;
                                                        FStar_Parser_AST.level
                                                          = uu____457;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____459;
                                                   FStar_Parser_AST.level =
                                                     uu____460;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.tset_singleton)
          &&
          (FStar_Ident.lid_equals maybe_ref_lid FStar_Parser_Const.heap_ref)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____462;
                FStar_Parser_AST.level = uu____463;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____465;
           FStar_Parser_AST.level = uu____466;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____468 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____473 =
      let uu____474 = unparen e in uu____474.FStar_Parser_AST.tm in
    match uu____473 with
    | FStar_Parser_AST.Var uu____476 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____477;
           FStar_Parser_AST.range = uu____478;
           FStar_Parser_AST.level = uu____479;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____480;
                                                        FStar_Parser_AST.range
                                                          = uu____481;
                                                        FStar_Parser_AST.level
                                                          = uu____482;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____484;
                                                   FStar_Parser_AST.level =
                                                     uu____485;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____486;
                FStar_Parser_AST.range = uu____487;
                FStar_Parser_AST.level = uu____488;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____490;
           FStar_Parser_AST.level = uu____491;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____493 = extract_from_ref_set e1 in
        let uu____495 = extract_from_ref_set e2 in
        FStar_List.append uu____493 uu____495
    | uu____497 ->
        let uu____498 =
          let uu____499 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____499 in
        failwith uu____498
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____504 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____504
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____508 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____508
let is_general_prefix_op: Prims.string -> Prims.bool = fun op  -> op <> "~"
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term* (FStar_Parser_AST.term* FStar_Parser_AST.imp)
      Prims.list)
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____538 =
        let uu____539 = unparen e1 in uu____539.FStar_Parser_AST.tm in
      match uu____538 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____550 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____559 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____563 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____567 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity* token Prims.list)
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___99_577  ->
    match uu___99_577 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___100_589  ->
      match uu___100_589 with
      | FStar_Util.Inl c ->
          let uu____593 = FStar_String.get s (Prims.parse_int "0") in
          uu____593 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____611 =
  match uu____611 with
  | (assoc_levels,tokens) ->
      let uu____625 = FStar_List.tryFind (matches_token s) tokens in
      uu____625 <> None
let opinfix4 uu____643 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____658 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____677 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____694 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____709 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____726 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____741 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____756 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____775 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____790 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____805 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____820 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____835 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____850 = (Right, [FStar_Util.Inr "::"])
let level_associativity_spec:
  (associativity* (FStar_Char.char,Prims.string) FStar_Util.either
    Prims.list) Prims.list
  =
  [opinfix4 ();
  opinfix3 ();
  opinfix2 ();
  opinfix1 ();
  pipe_right ();
  opinfix0d ();
  opinfix0c ();
  opinfix0b ();
  opinfix0a ();
  colon_equals ();
  amp ();
  colon_colon ()]
let level_table:
  ((Prims.int* Prims.int* Prims.int)* (FStar_Char.char,Prims.string)
    FStar_Util.either Prims.list) Prims.list
  =
  let levels_from_associativity l uu___101_947 =
    match uu___101_947 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____965  ->
         match uu____965 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string -> (Prims.int* Prims.int* Prims.int)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1007 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1007 with
      | Some (assoc_levels,uu____1032) -> assoc_levels
      | uu____1053 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1109 =
      FStar_List.tryFind
        (fun uu____1127  ->
           match uu____1127 with
           | (uu____1136,tokens) -> tokens = (Prims.snd level)) level_table in
    match uu____1109 with
    | Some ((uu____1156,l1,uu____1158),uu____1159) -> max n1 l1
    | None  ->
        let uu____1185 =
          let uu____1186 =
            let uu____1187 = FStar_List.map token_to_string (Prims.snd level) in
            FStar_String.concat "," uu____1187 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1186 in
        failwith uu____1185 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels: Prims.string -> (Prims.int* Prims.int* Prims.int) =
  assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1212 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: Prims.string -> Prims.bool =
  fun op  ->
    let uu____1251 =
      FStar_List.tryFind (matches_level op) (operatorInfix0ad12 ()) in
    uu____1251 <> None
let is_operatorInfix34: Prims.string -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____1299 = FStar_List.tryFind (matches_level op) opinfix34 in
    uu____1299 <> None
let handleable_args_length: Prims.string -> Prims.int =
  fun op  ->
    if (is_general_prefix_op op) || (FStar_List.mem op ["-"; "~"])
    then Prims.parse_int "1"
    else
      (let uu____1326 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____1326
       then Prims.parse_int "2"
       else
         if FStar_List.mem op [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let comment_stack: (Prims.string* FStar_Range.range) Prims.list FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1374 = FStar_ST.read comment_stack in
    match uu____1374 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1395 = FStar_Range.range_before_pos crange print_pos in
        if uu____1395
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1404 =
              let uu____1405 =
                let uu____1406 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1406 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1405 in
            comments_before_pos uu____1404 print_pos lookahead_pos))
        else
          (let uu____1408 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1408)) in
  let uu____1409 =
    let uu____1412 =
      let uu____1413 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1413 in
    let uu____1414 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1412 uu____1414 in
  match uu____1409 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1420 = comments_before_pos comments pos pos in
          Prims.fst uu____1420
        else comments in
      let uu____1424 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1424
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1437 = FStar_ST.read comment_stack in
          match uu____1437 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1461 =
                    let uu____1462 =
                      let uu____1463 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1463 in
                    uu____1462 - lbegin in
                  max k uu____1461 in
                let doc2 =
                  let uu____1465 =
                    let uu____1466 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1467 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1466 uu____1467 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1465 in
                let uu____1468 =
                  let uu____1469 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1469 in
                place_comments_until_pos (Prims.parse_int "1") uu____1468
                  pos_end doc2))
          | uu____1470 ->
              let lnum =
                let uu____1475 =
                  let uu____1476 = FStar_Range.line_of_pos pos_end in
                  uu____1476 - lbegin in
                max (Prims.parse_int "1") uu____1475 in
              let uu____1477 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1477
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1526 x =
    match uu____1526 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1536 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1536
            doc1 in
        let uu____1537 =
          let uu____1538 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1538 in
        let uu____1539 =
          let uu____1540 =
            let uu____1541 = f x in FStar_Pprint.op_Hat_Hat sep uu____1541 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1540 in
        (uu____1537, uu____1539) in
  let uu____1542 =
    let uu____1546 = FStar_List.hd xs in
    let uu____1547 = FStar_List.tl xs in (uu____1546, uu____1547) in
  match uu____1542 with
  | (x,xs1) ->
      let init1 =
        let uu____1557 =
          let uu____1558 =
            let uu____1559 = extract_range x in
            FStar_Range.end_of_range uu____1559 in
          FStar_Range.line_of_pos uu____1558 in
        let uu____1560 =
          let uu____1561 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1561 in
        (uu____1557, uu____1560) in
      let uu____1562 = FStar_List.fold_left fold_fun init1 xs1 in
      Prims.snd uu____1562
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1808 =
      let uu____1809 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____1810 =
        let uu____1811 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____1812 =
          let uu____1813 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____1814 =
            let uu____1815 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____1815 in
          FStar_Pprint.op_Hat_Hat uu____1813 uu____1814 in
        FStar_Pprint.op_Hat_Hat uu____1811 uu____1812 in
      FStar_Pprint.op_Hat_Hat uu____1809 uu____1810 in
    FStar_Pprint.group uu____1808
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____1818 =
      let uu____1819 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____1819 in
    let uu____1820 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____1818 FStar_Pprint.space uu____1820
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____1821  ->
    match uu____1821 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____1842 =
                match uu____1842 with
                | (kwd1,arg) ->
                    let uu____1847 = str "@" in
                    let uu____1848 =
                      let uu____1849 = str kwd1 in
                      let uu____1850 =
                        let uu____1851 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1851 in
                      FStar_Pprint.op_Hat_Hat uu____1849 uu____1850 in
                    FStar_Pprint.op_Hat_Hat uu____1847 uu____1848 in
              let uu____1852 =
                let uu____1853 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____1853 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1852 in
        let uu____1856 =
          let uu____1857 =
            let uu____1858 =
              let uu____1859 =
                let uu____1860 = str doc1 in
                let uu____1861 =
                  let uu____1862 =
                    let uu____1863 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1863 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____1862 in
                FStar_Pprint.op_Hat_Hat uu____1860 uu____1861 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1859 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____1858 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____1857 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____1856
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____1866 =
          let uu____1867 = str "open" in
          let uu____1868 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1867 uu____1868 in
        FStar_Pprint.group uu____1866
    | FStar_Parser_AST.Include uid ->
        let uu____1870 =
          let uu____1871 = str "include" in
          let uu____1872 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____1871 uu____1872 in
        FStar_Pprint.group uu____1870
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____1875 =
          let uu____1876 = str "module" in
          let uu____1877 =
            let uu____1878 =
              let uu____1879 = p_uident uid1 in
              let uu____1880 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____1879 uu____1880 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1878 in
          FStar_Pprint.op_Hat_Hat uu____1876 uu____1877 in
        let uu____1881 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____1875 uu____1881
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____1883 =
          let uu____1884 = str "module" in
          let uu____1885 =
            let uu____1886 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1886 in
          FStar_Pprint.op_Hat_Hat uu____1884 uu____1885 in
        FStar_Pprint.group uu____1883
    | FStar_Parser_AST.Tycon
        (true ,(FStar_Parser_AST.TyconAbbrev (uid,tpars,None ,t),None )::[])
        ->
        let effect_prefix_doc =
          let uu____1905 = str "effect" in
          let uu____1906 =
            let uu____1907 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1907 in
          FStar_Pprint.op_Hat_Hat uu____1905 uu____1906 in
        let uu____1908 =
          let uu____1909 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____1909 FStar_Pprint.equals in
        let uu____1910 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1908 uu____1910
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____1920 = str "type" in
        let uu____1921 = str "and" in
        precede_break_separate_map uu____1920 uu____1921 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____1934 = str "let" in
          let uu____1935 =
            let uu____1936 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____1936 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____1934 uu____1935 in
        let uu____1937 =
          let uu____1938 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____1938 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____1937 p_letbinding lbs
          (fun uu____1941  ->
             match uu____1941 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____1948 =
          let uu____1949 = str "val" in
          let uu____1950 =
            let uu____1951 =
              let uu____1952 = p_lident lid in
              let uu____1953 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____1952 uu____1953 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1951 in
          FStar_Pprint.op_Hat_Hat uu____1949 uu____1950 in
        let uu____1954 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1948 uu____1954
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____1958 =
            let uu____1959 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____1959 FStar_Util.is_upper in
          if uu____1958
          then FStar_Pprint.empty
          else
            (let uu____1961 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____1961 FStar_Pprint.space) in
        let uu____1962 =
          let uu____1963 =
            let uu____1964 = p_ident id in
            let uu____1965 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____1964 uu____1965 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____1963 in
        let uu____1966 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____1962 uu____1966
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____1971 = str "exception" in
        let uu____1972 =
          let uu____1973 =
            let uu____1974 = p_uident uid in
            let uu____1975 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____1977 = str "of" in
                   let uu____1978 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____1977 uu____1978) t_opt in
            FStar_Pprint.op_Hat_Hat uu____1974 uu____1975 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1973 in
        FStar_Pprint.op_Hat_Hat uu____1971 uu____1972
    | FStar_Parser_AST.NewEffect ne ->
        let uu____1980 = str "new_effect" in
        let uu____1981 =
          let uu____1982 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1982 in
        FStar_Pprint.op_Hat_Hat uu____1980 uu____1981
    | FStar_Parser_AST.SubEffect se ->
        let uu____1984 = str "sub_effect" in
        let uu____1985 =
          let uu____1986 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____1986 in
        FStar_Pprint.op_Hat_Hat uu____1984 uu____1985
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____1989 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____1989 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____1990 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____1991) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___102_2000  ->
    match uu___102_2000 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2002 = str "#set-options" in
        let uu____2003 =
          let uu____2004 =
            let uu____2005 = str s in FStar_Pprint.dquotes uu____2005 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2004 in
        FStar_Pprint.op_Hat_Hat uu____2002 uu____2003
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2008 = str "#reset-options" in
        let uu____2009 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2011 =
                 let uu____2012 = str s in FStar_Pprint.dquotes uu____2012 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2011) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2008 uu____2009
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon* FStar_Parser_AST.fsdoc Prims.option) ->
    FStar_Pprint.document
  =
  fun uu____2018  ->
    match uu____2018 with
    | (typedecl,fsdoc_opt) ->
        let uu____2026 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2027 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2026 uu____2027
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___103_2028  ->
    match uu___103_2028 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2039 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2051 =
          let uu____2052 = p_typ t in prefix2 FStar_Pprint.equals uu____2052 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2078 =
          match uu____2078 with
          | (lid1,t,doc_opt) ->
              let uu____2088 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2088 in
        let p_fields uu____2097 =
          let uu____2098 =
            let uu____2099 =
              let uu____2100 =
                let uu____2101 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2101 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2100 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2099 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2098 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2137 =
          match uu____2137 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2153 =
                  let uu____2154 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2154 in
                FStar_Range.extend_to_end_of_line uu____2153 in
              let p_constructorBranch decl =
                let uu____2173 =
                  let uu____2174 =
                    let uu____2175 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2175 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2174 in
                FStar_Pprint.group uu____2173 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2187 =
          let uu____2188 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2188 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2195  ->
             let uu____2196 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2196)
and p_typeDeclPrefix:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd Prims.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = None)
          then
            let uu____2207 = p_ident lid in
            let uu____2208 =
              let uu____2209 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2209 in
            FStar_Pprint.op_Hat_Hat uu____2207 uu____2208
          else
            (let binders_doc =
               let uu____2212 = p_typars bs in
               let uu____2213 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2215 =
                        let uu____2216 =
                          let uu____2217 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2217 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2216 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2215) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2212 uu____2213 in
             let uu____2218 = p_ident lid in
             let uu____2219 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2218 binders_doc uu____2219)
and p_recordFieldDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term* FStar_Parser_AST.fsdoc
    Prims.option) -> FStar_Pprint.document
  =
  fun uu____2220  ->
    match uu____2220 with
    | (lid,t,doc_opt) ->
        let uu____2230 =
          let uu____2231 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2232 =
            let uu____2233 = p_lident lid in
            let uu____2234 =
              let uu____2235 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2235 in
            FStar_Pprint.op_Hat_Hat uu____2233 uu____2234 in
          FStar_Pprint.op_Hat_Hat uu____2231 uu____2232 in
        FStar_Pprint.group uu____2230
and p_constructorDecl:
  (FStar_Ident.ident* FStar_Parser_AST.term Prims.option*
    FStar_Parser_AST.fsdoc Prims.option* Prims.bool) -> FStar_Pprint.document
  =
  fun uu____2236  ->
    match uu____2236 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2254 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2255 =
          let uu____2256 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2257 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2259 =
                   let uu____2260 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2260 in
                 let uu____2261 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2259 uu____2261) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2256 uu____2257 in
        FStar_Pprint.op_Hat_Hat uu____2254 uu____2255
and p_letbinding:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2262  ->
    match uu____2262 with
    | (pat,e) ->
        let pat_doc =
          let uu____2268 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2275 =
                  let uu____2276 =
                    let uu____2277 =
                      let uu____2278 =
                        let uu____2279 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2279 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2278 in
                    FStar_Pprint.group uu____2277 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2276 in
                (pat1, uu____2275)
            | uu____2280 -> (pat, FStar_Pprint.empty) in
          match uu____2268 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2284);
                      FStar_Parser_AST.prange = uu____2285;_},pats)
                   ->
                   let uu____2291 = p_lident x in
                   let uu____2292 =
                     let uu____2293 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2293 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2291 uu____2292
                     FStar_Pprint.equals
               | uu____2294 ->
                   let uu____2295 =
                     let uu____2296 = p_tuplePattern pat1 in
                     let uu____2297 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2296 uu____2297 in
                   FStar_Pprint.group uu____2295) in
        let uu____2298 = p_term e in prefix2 pat_doc uu____2298
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___104_2299  ->
    match uu___104_2299 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls
and p_effectRedefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____2317 = p_uident uid in
        let uu____2318 = p_binders true bs in
        let uu____2319 =
          let uu____2320 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2320 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2317 uu____2318 uu____2319
and p_effectDefinition:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let uu____2327 =
            let uu____2328 =
              let uu____2329 =
                let uu____2330 = p_uident uid in
                let uu____2331 = p_binders true bs in
                let uu____2332 =
                  let uu____2333 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2333 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2330 uu____2331 uu____2332 in
              FStar_Pprint.group uu____2329 in
            let uu____2334 =
              let uu____2335 = str "with" in
              let uu____2336 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2335 uu____2336 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2328 uu____2334 in
          braces_with_nesting uu____2327
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false ,(FStar_Parser_AST.TyconAbbrev (lid,[],None ,e),None )::[]) ->
        let uu____2353 =
          let uu____2354 = p_lident lid in
          let uu____2355 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2354 uu____2355 in
        let uu____2356 = p_simpleTerm e in prefix2 uu____2353 uu____2356
    | uu____2357 ->
        let uu____2358 =
          let uu____2359 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2359 in
        failwith uu____2358
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2392 =
        match uu____2392 with
        | (kwd1,t) ->
            let uu____2397 =
              let uu____2398 = str kwd1 in
              let uu____2399 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2398 uu____2399 in
            let uu____2400 = p_simpleTerm t in prefix2 uu____2397 uu____2400 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2403 =
      let uu____2404 =
        let uu____2405 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2406 =
          let uu____2407 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2407 in
        FStar_Pprint.op_Hat_Hat uu____2405 uu____2406 in
      let uu____2408 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2404 uu____2408 in
    let uu____2409 =
      let uu____2410 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2410 in
    FStar_Pprint.op_Hat_Hat uu____2403 uu____2409
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___105_2411  ->
    match uu___105_2411 with
    | FStar_Parser_AST.Private  -> str "private"
    | FStar_Parser_AST.Abstract  -> str "abstract"
    | FStar_Parser_AST.Noeq  -> str "noeq"
    | FStar_Parser_AST.Unopteq  -> str "unopteq"
    | FStar_Parser_AST.Assumption  -> str "assume"
    | FStar_Parser_AST.DefaultEffect  -> str "default"
    | FStar_Parser_AST.TotalEffect  -> str "total"
    | FStar_Parser_AST.Effect_qual  -> FStar_Pprint.empty
    | FStar_Parser_AST.New  -> str "new"
    | FStar_Parser_AST.Inline  -> str "inline"
    | FStar_Parser_AST.Visible  -> FStar_Pprint.empty
    | FStar_Parser_AST.Unfold_for_unification_and_vcgen  -> str "unfold"
    | FStar_Parser_AST.Inline_for_extraction  -> str "inline_for_extraction"
    | FStar_Parser_AST.Irreducible  -> str "irreducible"
    | FStar_Parser_AST.NoExtract  -> str "noextract"
    | FStar_Parser_AST.Reifiable  -> str "reifiable"
    | FStar_Parser_AST.Reflectable  -> str "reflectable"
    | FStar_Parser_AST.Opaque  -> str "opaque"
    | FStar_Parser_AST.Logic  -> str "logic"
and p_qualifiers: FStar_Parser_AST.qualifiers -> FStar_Pprint.document =
  fun qs  ->
    let uu____2413 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2413
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___106_2414  ->
    match uu___106_2414 with
    | FStar_Parser_AST.Rec  ->
        let uu____2415 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2415
    | FStar_Parser_AST.Mutable  ->
        let uu____2416 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2416
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___107_2417  ->
    match uu___107_2417 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2421 =
          let uu____2422 =
            let uu____2423 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2423 in
          FStar_Pprint.separate_map uu____2422 p_tuplePattern pats in
        FStar_Pprint.group uu____2421
    | uu____2424 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2429 =
          let uu____2430 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2430 p_constructorPattern pats in
        FStar_Pprint.group uu____2429
    | uu____2431 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2434;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2438 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2439 = p_constructorPattern hd1 in
        let uu____2440 = p_constructorPattern tl1 in
        infix0 uu____2438 uu____2439 uu____2440
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2442;_},pats)
        ->
        let uu____2446 = p_quident uid in
        let uu____2447 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2446 uu____2447
    | uu____2448 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2452 =
          let uu____2455 =
            let uu____2456 = unparen t in uu____2456.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2455) in
        (match uu____2452 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2461;
               FStar_Parser_AST.blevel = uu____2462;
               FStar_Parser_AST.aqual = uu____2463;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2467 =
               let uu____2468 = p_ident lid in
               p_refinement aqual uu____2468 t1 phi in
             soft_parens_with_nesting uu____2467
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2470;
               FStar_Parser_AST.blevel = uu____2471;
               FStar_Parser_AST.aqual = uu____2472;_},phi))
             ->
             let uu____2474 =
               p_refinement None FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2474
         | uu____2475 ->
             let uu____2478 =
               let uu____2479 = p_tuplePattern pat in
               let uu____2480 =
                 let uu____2481 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2482 =
                   let uu____2483 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2483 in
                 FStar_Pprint.op_Hat_Hat uu____2481 uu____2482 in
               FStar_Pprint.op_Hat_Hat uu____2479 uu____2480 in
             soft_parens_with_nesting uu____2478)
    | FStar_Parser_AST.PatList pats ->
        let uu____2486 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2486 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2496 =
          match uu____2496 with
          | (lid,pat) ->
              let uu____2501 = p_qlident lid in
              let uu____2502 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2501 uu____2502 in
        let uu____2503 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2503
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2509 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2510 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2511 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2509 uu____2510 uu____2511
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2518 =
          let uu____2519 =
            let uu____2520 = str op in
            let uu____2521 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2520 uu____2521 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2519 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2518
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2527 = FStar_Pprint.optional p_aqual aqual in
        let uu____2528 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2527 uu____2528
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2530 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
      ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName _;
         FStar_Parser_AST.prange = _;_},_)|FStar_Parser_AST.PatTuple
      (_,false ) ->
        let uu____2538 = p_tuplePattern p in
        soft_parens_with_nesting uu____2538
    | uu____2539 ->
        let uu____2540 =
          let uu____2541 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2541 in
        failwith uu____2540
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2545 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2546 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2545 uu____2546
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2551 =
              let uu____2552 = unparen t in uu____2552.FStar_Parser_AST.tm in
            match uu____2551 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2555;
                   FStar_Parser_AST.blevel = uu____2556;
                   FStar_Parser_AST.aqual = uu____2557;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2559 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2559 t1 phi
            | uu____2560 ->
                let uu____2561 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2562 =
                  let uu____2563 = p_lident lid in
                  let uu____2564 =
                    let uu____2565 =
                      let uu____2566 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2567 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2566 uu____2567 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2565 in
                  FStar_Pprint.op_Hat_Hat uu____2563 uu____2564 in
                FStar_Pprint.op_Hat_Hat uu____2561 uu____2562 in
          if is_atomic
          then
            let uu____2568 =
              let uu____2569 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2569 in
            FStar_Pprint.group uu____2568
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2571 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2575 =
            let uu____2576 = unparen t in uu____2576.FStar_Parser_AST.tm in
          (match uu____2575 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2578;
                  FStar_Parser_AST.blevel = uu____2579;
                  FStar_Parser_AST.aqual = uu____2580;_},phi)
               ->
               if is_atomic
               then
                 let uu____2582 =
                   let uu____2583 =
                     let uu____2584 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2584 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2583 in
                 FStar_Pprint.group uu____2582
               else
                 (let uu____2586 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2586)
           | uu____2587 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier Prims.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2594 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2595 =
            let uu____2596 =
              let uu____2597 =
                let uu____2598 = p_appTerm t in
                let uu____2599 =
                  let uu____2600 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2600 in
                FStar_Pprint.op_Hat_Hat uu____2598 uu____2599 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2597 in
            FStar_Pprint.op_Hat_Hat binder uu____2596 in
          FStar_Pprint.op_Hat_Hat uu____2594 uu____2595
and p_binders:
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> FStar_Pprint.separate_map break1 (p_binder is_atomic) bs
and p_qlident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_quident: FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)
and p_ident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_uident: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_tvar: FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)
and p_lidentOrUnderscore: FStar_Ident.ident -> FStar_Pprint.document =
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id
and p_term: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2613 =
      let uu____2614 = unparen e in uu____2614.FStar_Parser_AST.tm in
    match uu____2613 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2617 =
          let uu____2618 =
            let uu____2619 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2619 FStar_Pprint.semi in
          FStar_Pprint.group uu____2618 in
        let uu____2620 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2617 uu____2620
    | uu____2621 ->
        let uu____2622 = p_noSeqTerm e in FStar_Pprint.group uu____2622
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2625 =
      let uu____2626 = unparen e in uu____2626.FStar_Parser_AST.tm in
    match uu____2625 with
    | FStar_Parser_AST.Ascribed (e1,t,None ) ->
        let uu____2630 =
          let uu____2631 = p_tmIff e1 in
          let uu____2632 =
            let uu____2633 =
              let uu____2634 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2634 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2633 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2631 uu____2632 in
        FStar_Pprint.group uu____2630
    | FStar_Parser_AST.Ascribed (e1,t,Some tac) ->
        let uu____2639 =
          let uu____2640 = p_tmIff e1 in
          let uu____2641 =
            let uu____2642 =
              let uu____2643 =
                let uu____2644 = p_typ t in
                let uu____2645 =
                  let uu____2646 = str "by" in
                  let uu____2647 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2646 uu____2647 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2644 uu____2645 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2643 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2642 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2640 uu____2641 in
        FStar_Pprint.group uu____2639
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".()<-" ->
        let uu____2653 =
          let uu____2654 =
            let uu____2655 =
              let uu____2656 = p_atomicTermNotQUident e1 in
              let uu____2657 =
                let uu____2658 =
                  let uu____2659 =
                    let uu____2660 = p_term e2 in
                    soft_parens_with_nesting uu____2660 in
                  let uu____2661 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2659 uu____2661 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2658 in
              FStar_Pprint.op_Hat_Hat uu____2656 uu____2657 in
            FStar_Pprint.group uu____2655 in
          let uu____2662 =
            let uu____2663 = p_noSeqTerm e3 in jump2 uu____2663 in
          FStar_Pprint.op_Hat_Hat uu____2654 uu____2662 in
        FStar_Pprint.group uu____2653
    | FStar_Parser_AST.Op (op,e1::e2::e3::[]) when op = ".[]<-" ->
        let uu____2669 =
          let uu____2670 =
            let uu____2671 =
              let uu____2672 = p_atomicTermNotQUident e1 in
              let uu____2673 =
                let uu____2674 =
                  let uu____2675 =
                    let uu____2676 = p_term e2 in
                    soft_brackets_with_nesting uu____2676 in
                  let uu____2677 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2675 uu____2677 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2674 in
              FStar_Pprint.op_Hat_Hat uu____2672 uu____2673 in
            FStar_Pprint.group uu____2671 in
          let uu____2678 =
            let uu____2679 = p_noSeqTerm e3 in jump2 uu____2679 in
          FStar_Pprint.op_Hat_Hat uu____2670 uu____2678 in
        FStar_Pprint.group uu____2669
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2685 =
          let uu____2686 = str "requires" in
          let uu____2687 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2686 uu____2687 in
        FStar_Pprint.group uu____2685
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2693 =
          let uu____2694 = str "ensures" in
          let uu____2695 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2694 uu____2695 in
        FStar_Pprint.group uu____2693
    | FStar_Parser_AST.Attributes es ->
        let uu____2698 =
          let uu____2699 = str "attributes" in
          let uu____2700 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2699 uu____2700 in
        FStar_Pprint.group uu____2698
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2704 = is_unit e3 in
        if uu____2704
        then
          let uu____2705 =
            let uu____2706 =
              let uu____2707 = str "if" in
              let uu____2708 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2707 uu____2708 in
            let uu____2709 =
              let uu____2710 = str "then" in
              let uu____2711 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2710 uu____2711 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2706 uu____2709 in
          FStar_Pprint.group uu____2705
        else
          (let e2_doc =
             let uu____2714 =
               let uu____2715 = unparen e2 in uu____2715.FStar_Parser_AST.tm in
             match uu____2714 with
             | FStar_Parser_AST.If (uu____2716,uu____2717,e31) when
                 is_unit e31 ->
                 let uu____2719 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2719
             | uu____2720 -> p_noSeqTerm e2 in
           let uu____2721 =
             let uu____2722 =
               let uu____2723 = str "if" in
               let uu____2724 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2723 uu____2724 in
             let uu____2725 =
               let uu____2726 =
                 let uu____2727 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2727 e2_doc in
               let uu____2728 =
                 let uu____2729 = str "else" in
                 let uu____2730 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2729 uu____2730 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2726 uu____2728 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2722 uu____2725 in
           FStar_Pprint.group uu____2721)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2743 =
          let uu____2744 =
            let uu____2745 = str "try" in
            let uu____2746 = p_noSeqTerm e1 in prefix2 uu____2745 uu____2746 in
          let uu____2747 =
            let uu____2748 = str "with" in
            let uu____2749 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2748 uu____2749 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2744 uu____2747 in
        FStar_Pprint.group uu____2743
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2766 =
          let uu____2767 =
            let uu____2768 = str "match" in
            let uu____2769 = p_noSeqTerm e1 in
            let uu____2770 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2768 uu____2769 uu____2770 in
          let uu____2771 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2767 uu____2771 in
        FStar_Pprint.group uu____2766
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____2778 =
          let uu____2779 =
            let uu____2780 = str "let open" in
            let uu____2781 = p_quident uid in
            let uu____2782 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2780 uu____2781 uu____2782 in
          let uu____2783 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2779 uu____2783 in
        FStar_Pprint.group uu____2778
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____2794 = str "let" in
          let uu____2795 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____2794 uu____2795 in
        let uu____2796 =
          let uu____2797 =
            let uu____2798 =
              let uu____2799 = str "and" in
              precede_break_separate_map let_doc uu____2799 p_letbinding lbs in
            let uu____2802 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____2798 uu____2802 in
          FStar_Pprint.group uu____2797 in
        let uu____2803 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2796 uu____2803
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____2806;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____2809;
                                                         FStar_Parser_AST.level
                                                           = uu____2810;_})
        when matches_var maybe_x x ->
        let uu____2824 =
          let uu____2825 = str "function" in
          let uu____2826 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2825 uu____2826 in
        FStar_Pprint.group uu____2824
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____2833 =
          let uu____2834 = p_lident id in
          let uu____2835 =
            let uu____2836 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____2836 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2834 uu____2835 in
        FStar_Pprint.group uu____2833
    | uu____2837 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2840 =
      let uu____2841 = unparen e in uu____2841.FStar_Parser_AST.tm in
    match uu____2840 with
    | FStar_Parser_AST.QForall (bs,trigger,e1)|FStar_Parser_AST.QExists
      (bs,trigger,e1) ->
        let uu____2857 =
          let uu____2858 =
            let uu____2859 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____2859 FStar_Pprint.space in
          let uu____2860 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____2858 uu____2860 FStar_Pprint.dot in
        let uu____2861 =
          let uu____2862 = p_trigger trigger in
          let uu____2863 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____2862 uu____2863 in
        prefix2 uu____2857 uu____2861
    | uu____2864 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2866 =
      let uu____2867 = unparen e in uu____2867.FStar_Parser_AST.tm in
    match uu____2866 with
    | FStar_Parser_AST.QForall uu____2868 -> str "forall"
    | FStar_Parser_AST.QExists uu____2875 -> str "exists"
    | uu____2882 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___108_2883  ->
    match uu___108_2883 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____2890 =
          let uu____2891 =
            let uu____2892 = str "pattern" in
            let uu____2893 =
              let uu____2894 =
                let uu____2895 = p_disjunctivePats pats in jump2 uu____2895 in
              let uu____2896 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____2894 uu____2896 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2892 uu____2893 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2891 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____2890
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2900 = str "\\/" in
    FStar_Pprint.separate_map uu____2900 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____2904 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____2904
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2906 =
      let uu____2907 = unparen e in uu____2907.FStar_Parser_AST.tm in
    match uu____2906 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____2912 =
          let uu____2913 = str "fun" in
          let uu____2914 =
            let uu____2915 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____2915 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____2913 uu____2914 in
        let uu____2916 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____2912 uu____2916
    | uu____2917 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern* FStar_Parser_AST.term Prims.option*
    FStar_Parser_AST.term) -> FStar_Pprint.document
  =
  fun uu____2920  ->
    match uu____2920 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____2933 =
            let uu____2934 = unparen e in uu____2934.FStar_Parser_AST.tm in
          match uu____2933 with
          | FStar_Parser_AST.Match _|FStar_Parser_AST.TryWith _ ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____2940);
                 FStar_Parser_AST.prange = uu____2941;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____2943);
                                                               FStar_Parser_AST.range
                                                                 = uu____2944;
                                                               FStar_Parser_AST.level
                                                                 = uu____2945;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____2959 -> (fun x  -> x) in
        let uu____2961 =
          let uu____2962 =
            let uu____2963 =
              let uu____2964 =
                let uu____2965 =
                  let uu____2966 = p_disjunctivePattern pat in
                  let uu____2967 =
                    let uu____2968 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____2968 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____2966 uu____2967 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2965 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2964 in
            FStar_Pprint.group uu____2963 in
          let uu____2969 =
            let uu____2970 = p_term e in maybe_paren uu____2970 in
          op_Hat_Slash_Plus_Hat uu____2962 uu____2969 in
        FStar_Pprint.group uu____2961
and p_maybeWhen: FStar_Parser_AST.term Prims.option -> FStar_Pprint.document
  =
  fun uu___109_2971  ->
    match uu___109_2971 with
    | None  -> FStar_Pprint.empty
    | Some e ->
        let uu____2974 = str "when" in
        let uu____2975 =
          let uu____2976 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____2976 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____2974 uu____2975
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2978 =
      let uu____2979 = unparen e in uu____2979.FStar_Parser_AST.tm in
    match uu____2978 with
    | FStar_Parser_AST.Op ("<==>",e1::e2::[]) ->
        let uu____2983 = str "<==>" in
        let uu____2984 = p_tmImplies e1 in
        let uu____2985 = p_tmIff e2 in
        infix0 uu____2983 uu____2984 uu____2985
    | uu____2986 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2988 =
      let uu____2989 = unparen e in uu____2989.FStar_Parser_AST.tm in
    match uu____2988 with
    | FStar_Parser_AST.Op ("==>",e1::e2::[]) ->
        let uu____2993 = str "==>" in
        let uu____2994 = p_tmArrow p_tmFormula e1 in
        let uu____2995 = p_tmImplies e2 in
        infix0 uu____2993 uu____2994 uu____2995
    | uu____2996 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3001 =
        let uu____3002 = unparen e in uu____3002.FStar_Parser_AST.tm in
      match uu____3001 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3007 =
            let uu____3008 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3010 = p_binder false b in
                   let uu____3011 =
                     let uu____3012 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3012 in
                   FStar_Pprint.op_Hat_Hat uu____3010 uu____3011) bs in
            let uu____3013 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3008 uu____3013 in
          FStar_Pprint.group uu____3007
      | uu____3014 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3016 =
      let uu____3017 = unparen e in uu____3017.FStar_Parser_AST.tm in
    match uu____3016 with
    | FStar_Parser_AST.Op ("\\/",e1::e2::[]) ->
        let uu____3021 = str "\\/" in
        let uu____3022 = p_tmFormula e1 in
        let uu____3023 = p_tmConjunction e2 in
        infix0 uu____3021 uu____3022 uu____3023
    | uu____3024 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3026 =
      let uu____3027 = unparen e in uu____3027.FStar_Parser_AST.tm in
    match uu____3026 with
    | FStar_Parser_AST.Op ("/\\",e1::e2::[]) ->
        let uu____3031 = str "/\\" in
        let uu____3032 = p_tmConjunction e1 in
        let uu____3033 = p_tmTuple e2 in
        infix0 uu____3031 uu____3032 uu____3033
    | uu____3034 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3037 =
      let uu____3038 = unparen e in uu____3038.FStar_Parser_AST.tm in
    match uu____3037 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3047 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3047
          (fun uu____3050  ->
             match uu____3050 with | (e1,uu____3054) -> p_tmEq e1) args
    | uu____3055 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3060 =
             let uu____3061 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3061 in
           FStar_Pprint.group uu____3060)
and p_tmEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ())) in
    p_tmEq' n1 e
and p_tmEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3086 =
        let uu____3087 = unparen e in uu____3087.FStar_Parser_AST.tm in
      match uu____3086 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || (op = "=")) || (op = "|>") ->
          let uu____3092 = levels op in
          (match uu____3092 with
           | (left1,mine,right1) ->
               let uu____3099 =
                 let uu____3100 = str op in
                 let uu____3101 = p_tmEq' left1 e1 in
                 let uu____3102 = p_tmEq' right1 e2 in
                 infix0 uu____3100 uu____3101 uu____3102 in
               paren_if curr mine uu____3099)
      | FStar_Parser_AST.Op (":=",e1::e2::[]) ->
          let uu____3106 =
            let uu____3107 = p_tmEq e1 in
            let uu____3108 =
              let uu____3109 =
                let uu____3110 =
                  let uu____3111 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3111 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3110 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3109 in
            FStar_Pprint.op_Hat_Hat uu____3107 uu____3108 in
          FStar_Pprint.group uu____3106
      | uu____3112 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3142 =
        let uu____3143 = unparen e in uu____3143.FStar_Parser_AST.tm in
      match uu____3142 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3146)::(e2,uu____3148)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3158 = is_list e in Prims.op_Negation uu____3158)
          ->
          let op = "::" in
          let uu____3160 = levels op in
          (match uu____3160 with
           | (left1,mine,right1) ->
               let uu____3167 =
                 let uu____3168 = str op in
                 let uu____3169 = p_tmNoEq' left1 e1 in
                 let uu____3170 = p_tmNoEq' right1 e2 in
                 infix0 uu____3168 uu____3169 uu____3170 in
               paren_if curr mine uu____3167)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3176 = levels op in
          (match uu____3176 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3187 = p_binder false b in
                 let uu____3188 =
                   let uu____3189 =
                     let uu____3190 = str "&" in
                     FStar_Pprint.op_Hat_Hat uu____3190 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3189 in
                 FStar_Pprint.op_Hat_Hat uu____3187 uu____3188 in
               let uu____3191 =
                 let uu____3192 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3193 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3192 uu____3193 in
               paren_if curr mine uu____3191)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let uu____3198 = levels op in
          (match uu____3198 with
           | (left1,mine,right1) ->
               let uu____3205 =
                 let uu____3206 = str op in
                 let uu____3207 = p_tmNoEq' left1 e1 in
                 let uu____3208 = p_tmNoEq' right1 e2 in
                 infix0 uu____3206 uu____3207 uu____3208 in
               paren_if curr mine uu____3205)
      | FStar_Parser_AST.Op ("-",e1::[]) ->
          let uu____3211 = levels "-" in
          (match uu____3211 with
           | (left1,mine,right1) ->
               let uu____3218 = p_tmNoEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3218)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3221 =
            let uu____3222 = p_lidentOrUnderscore lid in
            let uu____3223 =
              let uu____3224 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3224 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3222 uu____3223 in
          FStar_Pprint.group uu____3221
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3237 =
            let uu____3238 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3239 =
              let uu____3240 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3240 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3238 uu____3239 in
          braces_with_nesting uu____3237
      | FStar_Parser_AST.Op ("~",e1::[]) ->
          let uu____3245 =
            let uu____3246 = str "~" in
            let uu____3247 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3246 uu____3247 in
          FStar_Pprint.group uu____3245
      | uu____3248 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3250 = p_appTerm e in
    let uu____3251 =
      let uu____3252 =
        let uu____3253 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3253 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3252 in
    FStar_Pprint.op_Hat_Hat uu____3250 uu____3251
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3258 =
            let uu____3259 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3259 t phi in
          soft_parens_with_nesting uu____3258
      | FStar_Parser_AST.TAnnotated uu____3260 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable _
        |FStar_Parser_AST.TVariable _|FStar_Parser_AST.NoName _ ->
          let uu____3266 =
            let uu____3267 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3267 in
          failwith uu____3266
and p_simpleDef:
  (FStar_Ident.lid* FStar_Parser_AST.term) -> FStar_Pprint.document =
  fun uu____3268  ->
    match uu____3268 with
    | (lid,e) ->
        let uu____3273 =
          let uu____3274 = p_qlident lid in
          let uu____3275 =
            let uu____3276 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3276 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3274 uu____3275 in
        FStar_Pprint.group uu____3273
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3278 =
      let uu____3279 = unparen e in uu____3279.FStar_Parser_AST.tm in
    match uu____3278 with
    | FStar_Parser_AST.App uu____3280 when is_general_application e ->
        let uu____3284 = head_and_args e in
        (match uu____3284 with
         | (head1,args) ->
             let uu____3298 =
               let uu____3304 = FStar_ST.read should_print_fs_typ_app in
               if uu____3304
               then
                 let uu____3312 =
                   FStar_Util.take
                     (fun uu____3323  ->
                        match uu____3323 with
                        | (uu____3326,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3312 with
                 | (fs_typ_args,args1) ->
                     let uu____3347 =
                       let uu____3348 = p_indexingTerm head1 in
                       let uu____3349 =
                         let uu____3350 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3350 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3348 uu____3349 in
                     (uu____3347, args1)
               else
                 (let uu____3357 = p_indexingTerm head1 in (uu____3357, args)) in
             (match uu____3298 with
              | (head_doc,args1) ->
                  let uu____3369 =
                    let uu____3370 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3370 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3369))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (Prims.op_Negation (is_dtuple_constructor lid))
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3390 =
               let uu____3391 = p_quident lid in
               let uu____3392 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3391 uu____3392 in
             FStar_Pprint.group uu____3390
         | hd1::tl1 ->
             let uu____3402 =
               let uu____3403 =
                 let uu____3404 =
                   let uu____3405 = p_quident lid in
                   let uu____3406 = p_argTerm hd1 in
                   prefix2 uu____3405 uu____3406 in
                 FStar_Pprint.group uu____3404 in
               let uu____3407 =
                 let uu____3408 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3408 in
               FStar_Pprint.op_Hat_Hat uu____3403 uu____3407 in
             FStar_Pprint.group uu____3402)
    | uu____3411 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3415;
         FStar_Parser_AST.range = uu____3416;
         FStar_Parser_AST.level = uu____3417;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (Prims.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3421 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3421 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3423 = str "#" in
        let uu____3424 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3423 uu____3424
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term* FStar_Parser_AST.imp) -> FStar_Pprint.document =
  fun uu____3426  ->
    match uu____3426 with | (e,uu____3430) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3435 =
        let uu____3436 = unparen e in uu____3436.FStar_Parser_AST.tm in
      match uu____3435 with
      | FStar_Parser_AST.Op (".()",e1::e2::[]) ->
          let uu____3440 =
            let uu____3441 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3442 =
              let uu____3443 =
                let uu____3444 = p_term e2 in
                soft_parens_with_nesting uu____3444 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3443 in
            FStar_Pprint.op_Hat_Hat uu____3441 uu____3442 in
          FStar_Pprint.group uu____3440
      | FStar_Parser_AST.Op (".[]",e1::e2::[]) ->
          let uu____3448 =
            let uu____3449 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3450 =
              let uu____3451 =
                let uu____3452 = p_term e2 in
                soft_brackets_with_nesting uu____3452 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3451 in
            FStar_Pprint.op_Hat_Hat uu____3449 uu____3450 in
          FStar_Pprint.group uu____3448
      | uu____3453 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3456 =
      let uu____3457 = unparen e in uu____3457.FStar_Parser_AST.tm in
    match uu____3456 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3460 = p_quident lid in
        let uu____3461 =
          let uu____3462 =
            let uu____3463 = p_term e1 in soft_parens_with_nesting uu____3463 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3462 in
        FStar_Pprint.op_Hat_Hat uu____3460 uu____3461
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3468 = str op in
        let uu____3469 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3468 uu____3469
    | uu____3470 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3472 =
      let uu____3473 = unparen e in uu____3473.FStar_Parser_AST.tm in
    match uu____3472 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c -> p_constant c
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3482 = str op in
        let uu____3483 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3482 uu____3483
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3486 =
          let uu____3487 =
            let uu____3488 = str op in
            let uu____3489 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3488 uu____3489 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3487 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3486
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3498 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3499 =
          let uu____3500 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3501 = FStar_List.map Prims.fst args in
          FStar_Pprint.separate_map uu____3500 p_tmEq uu____3501 in
        let uu____3505 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3498 uu____3499 uu____3505
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3508 =
          let uu____3509 = p_atomicTermNotQUident e1 in
          let uu____3510 =
            let uu____3511 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3511 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3509 uu____3510 in
        FStar_Pprint.group uu____3508
    | uu____3512 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3514 =
      let uu____3515 = unparen e in uu____3515.FStar_Parser_AST.tm in
    match uu____3514 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3519 = p_quident constr_lid in
        let uu____3520 =
          let uu____3521 =
            let uu____3522 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3522 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3521 in
        FStar_Pprint.op_Hat_Hat uu____3519 uu____3520
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3524 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3524 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3526 = p_term e1 in soft_parens_with_nesting uu____3526
    | uu____3527 when is_array e ->
        let es = extract_from_list e in
        let uu____3530 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3531 =
          let uu____3532 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3532 p_noSeqTerm es in
        let uu____3533 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3530 uu____3531 uu____3533
    | uu____3534 when is_list e ->
        let uu____3535 =
          let uu____3536 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3537 = extract_from_list e in
          separate_map_or_flow uu____3536 p_noSeqTerm uu____3537 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3535 FStar_Pprint.rbracket
    | uu____3539 when is_lex_list e ->
        let uu____3540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3541 =
          let uu____3542 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3543 = extract_from_list e in
          separate_map_or_flow uu____3542 p_noSeqTerm uu____3543 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3540 uu____3541 FStar_Pprint.rbracket
    | uu____3545 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3548 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3549 =
          let uu____3550 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3550 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3548 uu____3549 FStar_Pprint.rbrace
    | FStar_Parser_AST.Wild 
      |FStar_Parser_AST.Const _
       |FStar_Parser_AST.Op _
        |FStar_Parser_AST.Tvar _
         |FStar_Parser_AST.Uvar _
          |FStar_Parser_AST.Var _
           |FStar_Parser_AST.Name _
            |FStar_Parser_AST.Construct _
             |FStar_Parser_AST.Abs _
              |FStar_Parser_AST.App _
               |FStar_Parser_AST.Let _
                |FStar_Parser_AST.LetOpen _
                 |FStar_Parser_AST.Seq _
                  |FStar_Parser_AST.If _
                   |FStar_Parser_AST.Match _
                    |FStar_Parser_AST.TryWith _
                     |FStar_Parser_AST.Ascribed _
                      |FStar_Parser_AST.Record _
                       |FStar_Parser_AST.Project _
                        |FStar_Parser_AST.Product _
                         |FStar_Parser_AST.Sum _
                          |FStar_Parser_AST.QForall _
                           |FStar_Parser_AST.QExists _
                            |FStar_Parser_AST.Refine _
                             |FStar_Parser_AST.NamedTyp _
                              |FStar_Parser_AST.Requires _
                               |FStar_Parser_AST.Ensures _
                                |FStar_Parser_AST.Assign _
                                 |FStar_Parser_AST.Attributes _
        -> let uu____3579 = p_term e in soft_parens_with_nesting uu____3579
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3583 =
          let uu____3584 = str s in
          let uu____3585 =
            let uu____3586 = p_term e1 in soft_parens_with_nesting uu____3586 in
          FStar_Pprint.op_Hat_Hat uu____3584 uu____3585 in
        FStar_Pprint.group uu____3583
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___112_3587  ->
    match uu___112_3587 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3591 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3591
    | FStar_Const.Const_string (bytes,uu____3593) ->
        let uu____3596 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____3596
    | FStar_Const.Const_bytearray (bytes,uu____3598) ->
        let uu____3601 =
          let uu____3602 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____3602 in
        let uu____3603 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____3601 uu____3603
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___110_3615 =
          match uu___110_3615 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___111_3619 =
          match uu___111_3619 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____3623  ->
               match uu____3623 with
               | (s,w) ->
                   let uu____3628 = signedness s in
                   let uu____3629 = width w in
                   FStar_Pprint.op_Hat_Hat uu____3628 uu____3629)
            sign_width_opt in
        let uu____3630 = str repr in
        FStar_Pprint.op_Hat_Hat uu____3630 ending
    | FStar_Const.Const_range r ->
        let uu____3632 = FStar_Range.string_of_range r in str uu____3632
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____3634 = p_quident lid in
        let uu____3635 =
          let uu____3636 =
            let uu____3637 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3637 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3636 in
        FStar_Pprint.op_Hat_Hat uu____3634 uu____3635
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3639 = str "u#" in
    let uu____3640 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____3639 uu____3640
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3642 =
      let uu____3643 = unparen u in uu____3643.FStar_Parser_AST.tm in
    match uu____3642 with
    | FStar_Parser_AST.Op ("+",u1::u2::[]) ->
        let uu____3647 =
          let uu____3648 = p_universeFrom u1 in
          let uu____3649 =
            let uu____3650 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____3650 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3648 uu____3649 in
        FStar_Pprint.group uu____3647
    | FStar_Parser_AST.App uu____3651 ->
        let uu____3655 = head_and_args u in
        (match uu____3655 with
         | (head1,args) ->
             let uu____3669 =
               let uu____3670 = unparen head1 in
               uu____3670.FStar_Parser_AST.tm in
             (match uu____3669 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____3672 =
                    let uu____3673 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____3674 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____3677  ->
                           match uu____3677 with
                           | (u1,uu____3681) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____3673 uu____3674 in
                  FStar_Pprint.group uu____3672
              | uu____3682 ->
                  let uu____3683 =
                    let uu____3684 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____3684 in
                  failwith uu____3683))
    | uu____3685 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3687 =
      let uu____3688 = unparen u in uu____3688.FStar_Parser_AST.tm in
    match uu____3687 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____3700 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____3702 = p_universeFrom u1 in
        soft_parens_with_nesting uu____3702
    | FStar_Parser_AST.Op ("+",_::_::[])|FStar_Parser_AST.App _ ->
        let uu____3707 = p_universeFrom u in
        soft_parens_with_nesting uu____3707
    | uu____3708 ->
        let uu____3709 =
          let uu____3710 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____3710 in
        failwith uu____3709
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____3712 =
      let uu____3713 = unparen u in uu____3713.FStar_Parser_AST.tm in
    match uu____3712 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____3715 ->
        let uu____3716 =
          let uu____3717 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____3717 in
        failwith uu____3716
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
         (_,decls,_) ->
           let uu____3739 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____3739
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string* FStar_Range.range) Prims.list -> FStar_Pprint.document =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____3758  ->
         match uu____3758 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string* FStar_Range.range) Prims.list ->
      (FStar_Pprint.document* (Prims.string* FStar_Range.range) Prims.list)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (_,decls)|FStar_Parser_AST.Interface
          (_,decls,_) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____3805 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____3812;
                 FStar_Parser_AST.doc = uu____3813;
                 FStar_Parser_AST.quals = uu____3814;
                 FStar_Parser_AST.attrs = uu____3815;_}::uu____3816 ->
                 let d0 = FStar_List.hd ds in
                 let uu____3820 =
                   let uu____3822 =
                     let uu____3824 = FStar_List.tl ds in d :: uu____3824 in
                   d0 :: uu____3822 in
                 (uu____3820, (d0.FStar_Parser_AST.drange))
             | uu____3827 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____3805 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____3850 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____3850 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____3872 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____3872, comments1))))))