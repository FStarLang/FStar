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
    let uu____38 =
      let uu____39 = FStar_ST.read should_unparen in
      Prims.op_Negation uu____39 in
    if uu____38
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____42 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map n1 f x =
  match x with
  | FStar_Pervasives_Native.None  -> n1
  | FStar_Pervasives_Native.Some x' -> f x'
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
  let uu____128 =
    let uu____129 =
      let uu____130 = FStar_Pprint.op_Hat_Hat sep break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____130 in
    FStar_Pprint.separate_map uu____129 f l in
  FStar_Pprint.group uu____128
let precede_break_separate_map prec sep f l =
  let uu____162 =
    let uu____163 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
    let uu____164 =
      let uu____165 = FStar_List.hd l in FStar_All.pipe_right uu____165 f in
    FStar_Pprint.precede uu____163 uu____164 in
  let uu____166 =
    let uu____167 = FStar_List.tl l in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____171 =
           let uu____172 =
             let uu____173 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____173 in
           FStar_Pprint.op_Hat_Hat sep uu____172 in
         FStar_Pprint.op_Hat_Hat break1 uu____171) uu____167 in
  FStar_Pprint.op_Hat_Hat uu____162 uu____166
let concat_break_map f l =
  let uu____195 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____197 = f x in FStar_Pprint.op_Hat_Hat uu____197 break1) l in
  FStar_Pprint.group uu____195
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
    let uu____219 = str "begin" in
    let uu____220 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____219 contents uu____220
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____302 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____302 closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____315  ->
    match uu____315 with
    | (comment,keywords1) ->
        let uu____340 =
          let uu____341 =
            let uu____344 = str comment in
            let uu____345 =
              let uu____348 =
                let uu____351 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____356  ->
                       match uu____356 with
                       | (k,v1) ->
                           let uu____363 =
                             let uu____366 = str k in
                             let uu____367 =
                               let uu____370 =
                                 let uu____373 = str v1 in [uu____373] in
                               FStar_Pprint.rarrow :: uu____370 in
                             uu____366 :: uu____367 in
                           FStar_Pprint.concat uu____363) keywords1 in
                [uu____351] in
              FStar_Pprint.space :: uu____348 in
            uu____344 :: uu____345 in
          FStar_Pprint.concat uu____341 in
        FStar_Pprint.group uu____340
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____377 =
      let uu____378 = unparen e in uu____378.FStar_Parser_AST.tm in
    match uu____377 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____379 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____386 =
        let uu____387 = unparen t in uu____387.FStar_Parser_AST.tm in
      match uu____386 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____389 -> false
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
        let uu____406 =
          let uu____407 = unparen e in uu____407.FStar_Parser_AST.tm in
        match uu____406 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____420::(e2,uu____422)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____445 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____455 =
      let uu____456 = unparen e in uu____456.FStar_Parser_AST.tm in
    match uu____455 with
    | FStar_Parser_AST.Construct (uu____459,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____470,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____491 = extract_from_list e2 in e1 :: uu____491
    | uu____494 ->
        let uu____495 =
          let uu____496 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____496 in
        failwith uu____495
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____502 =
      let uu____503 = unparen e in uu____503.FStar_Parser_AST.tm in
    match uu____502 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____505;
           FStar_Parser_AST.level = uu____506;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____508 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____512 =
      let uu____513 = unparen e in uu____513.FStar_Parser_AST.tm in
    match uu____512 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____516;
           FStar_Parser_AST.level = uu____517;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____519;
                                                        FStar_Parser_AST.level
                                                          = uu____520;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____522;
                                                   FStar_Parser_AST.level =
                                                     uu____523;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____525;
                FStar_Parser_AST.level = uu____526;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____528;
           FStar_Parser_AST.level = uu____529;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____531 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____537 =
      let uu____538 = unparen e in uu____538.FStar_Parser_AST.tm in
    match uu____537 with
    | FStar_Parser_AST.Var uu____541 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____542;
           FStar_Parser_AST.range = uu____543;
           FStar_Parser_AST.level = uu____544;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____545;
                                                        FStar_Parser_AST.range
                                                          = uu____546;
                                                        FStar_Parser_AST.level
                                                          = uu____547;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____549;
                                                   FStar_Parser_AST.level =
                                                     uu____550;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____551;
                FStar_Parser_AST.range = uu____552;
                FStar_Parser_AST.level = uu____553;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____555;
           FStar_Parser_AST.level = uu____556;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____558 = extract_from_ref_set e1 in
        let uu____561 = extract_from_ref_set e2 in
        FStar_List.append uu____558 uu____561
    | uu____564 ->
        let uu____565 =
          let uu____566 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____566 in
        failwith uu____565
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____572 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____572
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____576 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____576
let is_general_prefix_op: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0") in
    ((op_starting_char = '!') || (op_starting_char = '?')) ||
      ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~"))
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____623 =
        let uu____624 = unparen e1 in uu____624.FStar_Parser_AST.tm in
      match uu____623 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____642 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____656 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____660 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____664 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___95_681  ->
    match uu___95_681 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___96_697  ->
      match uu___96_697 with
      | FStar_Util.Inl c ->
          let uu____703 = FStar_String.get s (Prims.parse_int "0") in
          uu____703 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____726 =
  match uu____726 with
  | (assoc_levels,tokens) ->
      let uu____751 = FStar_List.tryFind (matches_token s) tokens in
      uu____751 <> FStar_Pervasives_Native.None
let opinfix4 uu____784 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____811 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____846 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____877 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____904 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____935 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____962 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____989 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____1024 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____1051 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____1078 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____1105 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____1132 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____1159 = (Right, [FStar_Util.Inr "::"])
let level_associativity_spec:
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
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
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  let levels_from_associativity l uu___97_1346 =
    match uu___97_1346 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1380  ->
         match uu____1380 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1455 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1455 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1503) ->
          assoc_levels
      | uu____1544 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1634 =
      FStar_List.tryFind
        (fun uu____1669  ->
           match uu____1669 with
           | (uu____1686,tokens) ->
               tokens = (FStar_Pervasives_Native.snd level)) level_table in
    match uu____1634 with
    | FStar_Pervasives_Native.Some ((uu____1724,l1,uu____1726),uu____1727) ->
        max n1 l1
    | FStar_Pervasives_Native.None  ->
        let uu____1778 =
          let uu____1779 =
            let uu____1780 =
              FStar_List.map token_to_string
                (FStar_Pervasives_Native.snd level) in
            FStar_String.concat "," uu____1780 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1779 in
        failwith uu____1778 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1825 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1899 =
      let uu____1912 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1912 (operatorInfix0ad12 ()) in
    uu____1899 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2015 =
      let uu____2028 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2028 opinfix34 in
    uu____2015 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2089 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2089
    then Prims.parse_int "1"
    else
      (let uu____2091 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2091
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op op args =
  match FStar_List.length args with
  | _0_27 when _0_27 = (Prims.parse_int "0") -> true
  | _0_28 when _0_28 = (Prims.parse_int "1") ->
      (is_general_prefix_op op) ||
        (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
  | _0_29 when _0_29 = (Prims.parse_int "2") ->
      ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
        (FStar_List.mem (FStar_Ident.text_of_id op)
           ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
  | _0_30 when _0_30 = (Prims.parse_int "3") ->
      FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
  | uu____2110 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____2166 = FStar_ST.read comment_stack in
    match uu____2166 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____2200 = FStar_Range.range_before_pos crange print_pos in
        if uu____2200
        then
          (FStar_ST.write comment_stack cs;
           (let uu____2212 =
              let uu____2213 =
                let uu____2214 = str comment in
                FStar_Pprint.op_Hat_Hat uu____2214 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____2213 in
            comments_before_pos uu____2212 print_pos lookahead_pos))
        else
          (let uu____2216 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____2216)) in
  let uu____2217 =
    let uu____2222 =
      let uu____2223 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____2223 in
    let uu____2224 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____2222 uu____2224 in
  match uu____2217 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____2230 = comments_before_pos comments pos pos in
          FStar_Pervasives_Native.fst uu____2230
        else comments in
      let uu____2236 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____2236
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2249 = FStar_ST.read comment_stack in
          match uu____2249 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____2283 =
                    let uu____2284 =
                      let uu____2285 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2285 in
                    uu____2284 - lbegin in
                  max k uu____2283 in
                let doc2 =
                  let uu____2287 =
                    let uu____2288 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2289 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2288 uu____2289 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2287 in
                let uu____2290 =
                  let uu____2291 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2291 in
                place_comments_until_pos (Prims.parse_int "1") uu____2290
                  pos_end doc2))
          | uu____2292 ->
              let lnum =
                let uu____2300 =
                  let uu____2301 = FStar_Range.line_of_pos pos_end in
                  uu____2301 - lbegin in
                max (Prims.parse_int "1") uu____2300 in
              let uu____2302 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2302
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____2357 x =
    match uu____2357 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____2371 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____2371
            doc1 in
        let uu____2372 =
          let uu____2373 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____2373 in
        let uu____2374 =
          let uu____2375 =
            let uu____2376 = f x in FStar_Pprint.op_Hat_Hat sep uu____2376 in
          FStar_Pprint.op_Hat_Hat doc2 uu____2375 in
        (uu____2372, uu____2374) in
  let uu____2377 =
    let uu____2384 = FStar_List.hd xs in
    let uu____2385 = FStar_List.tl xs in (uu____2384, uu____2385) in
  match uu____2377 with
  | (x,xs1) ->
      let init1 =
        let uu____2401 =
          let uu____2402 =
            let uu____2403 = extract_range x in
            FStar_Range.end_of_range uu____2403 in
          FStar_Range.line_of_pos uu____2402 in
        let uu____2404 =
          let uu____2405 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____2405 in
        (uu____2401, uu____2404) in
      let uu____2406 = FStar_List.fold_left fold_fun init1 xs1 in
      FStar_Pervasives_Native.snd uu____2406
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____2693 =
      let uu____2694 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____2695 =
        let uu____2696 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____2697 =
          let uu____2698 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____2699 =
            let uu____2700 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____2700 in
          FStar_Pprint.op_Hat_Hat uu____2698 uu____2699 in
        FStar_Pprint.op_Hat_Hat uu____2696 uu____2697 in
      FStar_Pprint.op_Hat_Hat uu____2694 uu____2695 in
    FStar_Pprint.group uu____2693
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____2703 =
      let uu____2704 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____2704 in
    let uu____2705 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____2703 FStar_Pprint.space uu____2705
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____2706  ->
    match uu____2706 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____2740 =
                match uu____2740 with
                | (kwd1,arg) ->
                    let uu____2747 = str "@" in
                    let uu____2748 =
                      let uu____2749 = str kwd1 in
                      let uu____2750 =
                        let uu____2751 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2751 in
                      FStar_Pprint.op_Hat_Hat uu____2749 uu____2750 in
                    FStar_Pprint.op_Hat_Hat uu____2747 uu____2748 in
              let uu____2752 =
                let uu____2753 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____2753 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2752 in
        let uu____2758 =
          let uu____2759 =
            let uu____2760 =
              let uu____2761 =
                let uu____2762 = str doc1 in
                let uu____2763 =
                  let uu____2764 =
                    let uu____2765 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2765 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2764 in
                FStar_Pprint.op_Hat_Hat uu____2762 uu____2763 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2761 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2760 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2759 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2758
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____2768 =
          let uu____2769 = str "open" in
          let uu____2770 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2769 uu____2770 in
        FStar_Pprint.group uu____2768
    | FStar_Parser_AST.Include uid ->
        let uu____2772 =
          let uu____2773 = str "include" in
          let uu____2774 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2773 uu____2774 in
        FStar_Pprint.group uu____2772
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____2777 =
          let uu____2778 = str "module" in
          let uu____2779 =
            let uu____2780 =
              let uu____2781 = p_uident uid1 in
              let uu____2782 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2781 uu____2782 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2780 in
          FStar_Pprint.op_Hat_Hat uu____2778 uu____2779 in
        let uu____2783 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____2777 uu____2783
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____2785 =
          let uu____2786 = str "module" in
          let uu____2787 =
            let uu____2788 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2788 in
          FStar_Pprint.op_Hat_Hat uu____2786 uu____2787 in
        FStar_Pprint.group uu____2785
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____2821 = str "effect" in
          let uu____2822 =
            let uu____2823 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2823 in
          FStar_Pprint.op_Hat_Hat uu____2821 uu____2822 in
        let uu____2824 =
          let uu____2825 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____2825 FStar_Pprint.equals in
        let uu____2826 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2824 uu____2826
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____2844 = str "type" in
        let uu____2845 = str "and" in
        precede_break_separate_map uu____2844 uu____2845 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____2867 = str "let" in
          let uu____2868 =
            let uu____2869 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____2869 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____2867 uu____2868 in
        let uu____2870 =
          let uu____2871 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____2871 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____2870 p_letbinding lbs
          (fun uu____2876  ->
             match uu____2876 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2885 =
          let uu____2886 = str "val" in
          let uu____2887 =
            let uu____2888 =
              let uu____2889 = p_lident lid in
              let uu____2890 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2889 uu____2890 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2888 in
          FStar_Pprint.op_Hat_Hat uu____2886 uu____2887 in
        let uu____2891 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2885 uu____2891
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2895 =
            let uu____2896 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2896 FStar_Util.is_upper in
          if uu____2895
          then FStar_Pprint.empty
          else
            (let uu____2898 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2898 FStar_Pprint.space) in
        let uu____2899 =
          let uu____2900 =
            let uu____2901 = p_ident id in
            let uu____2902 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2901 uu____2902 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2900 in
        let uu____2903 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2899 uu____2903
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2910 = str "exception" in
        let uu____2911 =
          let uu____2912 =
            let uu____2913 = p_uident uid in
            let uu____2914 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2916 = str "of" in
                   let uu____2917 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2916 uu____2917) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2913 uu____2914 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2912 in
        FStar_Pprint.op_Hat_Hat uu____2910 uu____2911
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2919 = str "new_effect" in
        let uu____2920 =
          let uu____2921 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2921 in
        FStar_Pprint.op_Hat_Hat uu____2919 uu____2920
    | FStar_Parser_AST.SubEffect se ->
        let uu____2923 = str "sub_effect" in
        let uu____2924 =
          let uu____2925 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2925 in
        FStar_Pprint.op_Hat_Hat uu____2923 uu____2924
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2928 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2928 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2929 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2930) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___98_2947  ->
    match uu___98_2947 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2949 = str "#set-options" in
        let uu____2950 =
          let uu____2951 =
            let uu____2952 = str s in FStar_Pprint.dquotes uu____2952 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2951 in
        FStar_Pprint.op_Hat_Hat uu____2949 uu____2950
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2956 = str "#reset-options" in
        let uu____2957 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2959 =
                 let uu____2960 = str s in FStar_Pprint.dquotes uu____2960 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2959) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2956 uu____2957
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2965  ->
    match uu____2965 with
    | (typedecl,fsdoc_opt) ->
        let uu____2978 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2979 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2978 uu____2979
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___99_2980  ->
    match uu___99_2980 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2995 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3011 =
          let uu____3012 = p_typ t in prefix2 FStar_Pprint.equals uu____3012 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3056 =
          match uu____3056 with
          | (lid1,t,doc_opt) ->
              let uu____3072 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3072 in
        let p_fields uu____3086 =
          let uu____3087 =
            let uu____3088 =
              let uu____3089 =
                let uu____3090 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3090 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3089 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3088 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3087 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3154 =
          match uu____3154 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3180 =
                  let uu____3181 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3181 in
                FStar_Range.extend_to_end_of_line uu____3180 in
              let p_constructorBranch decl =
                let uu____3213 =
                  let uu____3214 =
                    let uu____3215 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3215 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3214 in
                FStar_Pprint.group uu____3213 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3235 =
          let uu____3236 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3236 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3249  ->
             let uu____3250 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3250)
and p_typeDeclPrefix:
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____3265 = p_ident lid in
            let uu____3266 =
              let uu____3267 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3267 in
            FStar_Pprint.op_Hat_Hat uu____3265 uu____3266
          else
            (let binders_doc =
               let uu____3270 = p_typars bs in
               let uu____3271 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3273 =
                        let uu____3274 =
                          let uu____3275 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3275 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3274 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3273) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3270 uu____3271 in
             let uu____3276 = p_ident lid in
             let uu____3277 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3276 binders_doc uu____3277)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3278  ->
    match uu____3278 with
    | (lid,t,doc_opt) ->
        let uu____3294 =
          let uu____3295 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3296 =
            let uu____3297 = p_lident lid in
            let uu____3298 =
              let uu____3299 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3299 in
            FStar_Pprint.op_Hat_Hat uu____3297 uu____3298 in
          FStar_Pprint.op_Hat_Hat uu____3295 uu____3296 in
        FStar_Pprint.group uu____3294
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3300  ->
    match uu____3300 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3328 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3329 =
          let uu____3330 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3331 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3333 =
                   let uu____3334 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3334 in
                 let uu____3335 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3333 uu____3335) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3330 uu____3331 in
        FStar_Pprint.op_Hat_Hat uu____3328 uu____3329
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3336  ->
    match uu____3336 with
    | (pat,e) ->
        let pat_doc =
          let uu____3344 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____3355 =
                  let uu____3356 =
                    let uu____3357 =
                      let uu____3358 =
                        let uu____3359 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3359 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3358 in
                    FStar_Pprint.group uu____3357 in
                  FStar_Pprint.op_Hat_Hat break1 uu____3356 in
                (pat1, uu____3355)
            | uu____3360 -> (pat, FStar_Pprint.empty) in
          match uu____3344 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____3364);
                      FStar_Parser_AST.prange = uu____3365;_},pats)
                   ->
                   let uu____3375 = p_lident x in
                   let uu____3376 =
                     let uu____3377 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____3377 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____3375 uu____3376
                     FStar_Pprint.equals
               | uu____3378 ->
                   let uu____3379 =
                     let uu____3380 = p_tuplePattern pat1 in
                     let uu____3381 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____3380 uu____3381 in
                   FStar_Pprint.group uu____3379) in
        let uu____3382 = p_term e in prefix2 pat_doc uu____3382
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___100_3383  ->
    match uu___100_3383 with
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
        let uu____3408 = p_uident uid in
        let uu____3409 = p_binders true bs in
        let uu____3410 =
          let uu____3411 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3411 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3408 uu____3409 uu____3410
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
          let uu____3420 =
            let uu____3421 =
              let uu____3422 =
                let uu____3423 = p_uident uid in
                let uu____3424 = p_binders true bs in
                let uu____3425 =
                  let uu____3426 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3426 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3423 uu____3424 uu____3425 in
              FStar_Pprint.group uu____3422 in
            let uu____3427 =
              let uu____3428 = str "with" in
              let uu____3429 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3428 uu____3429 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3421 uu____3427 in
          braces_with_nesting uu____3420
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3459 =
          let uu____3460 = p_lident lid in
          let uu____3461 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3460 uu____3461 in
        let uu____3462 = p_simpleTerm e in prefix2 uu____3459 uu____3462
    | uu____3463 ->
        let uu____3464 =
          let uu____3465 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3465 in
        failwith uu____3464
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____3520 =
        match uu____3520 with
        | (kwd1,t) ->
            let uu____3527 =
              let uu____3528 = str kwd1 in
              let uu____3529 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3528 uu____3529 in
            let uu____3530 = p_simpleTerm t in prefix2 uu____3527 uu____3530 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____3535 =
      let uu____3536 =
        let uu____3537 = p_quident lift.FStar_Parser_AST.msource in
        let uu____3538 =
          let uu____3539 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3539 in
        FStar_Pprint.op_Hat_Hat uu____3537 uu____3538 in
      let uu____3540 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____3536 uu____3540 in
    let uu____3541 =
      let uu____3542 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3542 in
    FStar_Pprint.op_Hat_Hat uu____3535 uu____3541
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___101_3543  ->
    match uu___101_3543 with
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
    let uu____3545 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____3545
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___102_3546  ->
    match uu___102_3546 with
    | FStar_Parser_AST.Rec  ->
        let uu____3547 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3547
    | FStar_Parser_AST.Mutable  ->
        let uu____3548 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3548
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___103_3549  ->
    match uu___103_3549 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____3554 =
          let uu____3555 =
            let uu____3556 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____3556 in
          FStar_Pprint.separate_map uu____3555 p_tuplePattern pats in
        FStar_Pprint.group uu____3554
    | uu____3557 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____3564 =
          let uu____3565 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____3565 p_constructorPattern pats in
        FStar_Pprint.group uu____3564
    | uu____3566 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____3569;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____3574 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____3575 = p_constructorPattern hd1 in
        let uu____3576 = p_constructorPattern tl1 in
        infix0 uu____3574 uu____3575 uu____3576
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____3578;_},pats)
        ->
        let uu____3584 = p_quident uid in
        let uu____3585 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____3584 uu____3585
    | uu____3586 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____3590 =
          let uu____3595 =
            let uu____3596 = unparen t in uu____3596.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____3595) in
        (match uu____3590 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____3601;
               FStar_Parser_AST.blevel = uu____3602;
               FStar_Parser_AST.aqual = uu____3603;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____3609 =
               let uu____3610 = p_ident lid in
               p_refinement aqual uu____3610 t1 phi in
             soft_parens_with_nesting uu____3609
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____3612;
               FStar_Parser_AST.blevel = uu____3613;
               FStar_Parser_AST.aqual = uu____3614;_},phi))
             ->
             let uu____3616 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____3616
         | uu____3617 ->
             let uu____3622 =
               let uu____3623 = p_tuplePattern pat in
               let uu____3624 =
                 let uu____3625 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____3626 =
                   let uu____3627 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3627 in
                 FStar_Pprint.op_Hat_Hat uu____3625 uu____3626 in
               FStar_Pprint.op_Hat_Hat uu____3623 uu____3624 in
             soft_parens_with_nesting uu____3622)
    | FStar_Parser_AST.PatList pats ->
        let uu____3631 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3631 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____3646 =
          match uu____3646 with
          | (lid,pat) ->
              let uu____3653 = p_qlident lid in
              let uu____3654 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____3653 uu____3654 in
        let uu____3655 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____3655
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____3665 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3666 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____3667 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3665 uu____3666 uu____3667
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____3678 =
          let uu____3679 =
            let uu____3680 = str (FStar_Ident.text_of_id op) in
            let uu____3681 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3680 uu____3681 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3679 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3678
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____3689 = FStar_Pprint.optional p_aqual aqual in
        let uu____3690 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____3689 uu____3690
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____3692 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____3695;
           FStar_Parser_AST.prange = uu____3696;_},uu____3697)
        ->
        let uu____3702 = p_tuplePattern p in
        soft_parens_with_nesting uu____3702
    | FStar_Parser_AST.PatTuple (uu____3703,false ) ->
        let uu____3708 = p_tuplePattern p in
        soft_parens_with_nesting uu____3708
    | uu____3709 ->
        let uu____3710 =
          let uu____3711 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____3711 in
        failwith uu____3710
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____3715 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____3716 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____3715 uu____3716
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____3721 =
              let uu____3722 = unparen t in uu____3722.FStar_Parser_AST.tm in
            match uu____3721 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____3725;
                   FStar_Parser_AST.blevel = uu____3726;
                   FStar_Parser_AST.aqual = uu____3727;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____3729 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____3729 t1 phi
            | uu____3730 ->
                let uu____3731 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____3732 =
                  let uu____3733 = p_lident lid in
                  let uu____3734 =
                    let uu____3735 =
                      let uu____3736 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____3737 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____3736 uu____3737 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3735 in
                  FStar_Pprint.op_Hat_Hat uu____3733 uu____3734 in
                FStar_Pprint.op_Hat_Hat uu____3731 uu____3732 in
          if is_atomic
          then
            let uu____3738 =
              let uu____3739 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3739 in
            FStar_Pprint.group uu____3738
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____3741 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____3747 =
            let uu____3748 = unparen t in uu____3748.FStar_Parser_AST.tm in
          (match uu____3747 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____3750;
                  FStar_Parser_AST.blevel = uu____3751;
                  FStar_Parser_AST.aqual = uu____3752;_},phi)
               ->
               if is_atomic
               then
                 let uu____3754 =
                   let uu____3755 =
                     let uu____3756 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____3756 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3755 in
                 FStar_Pprint.group uu____3754
               else
                 (let uu____3758 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____3758)
           | uu____3759 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____3767 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____3768 =
            let uu____3769 =
              let uu____3770 =
                let uu____3771 = p_appTerm t in
                let uu____3772 =
                  let uu____3773 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____3773 in
                FStar_Pprint.op_Hat_Hat uu____3771 uu____3772 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3770 in
            FStar_Pprint.op_Hat_Hat binder uu____3769 in
          FStar_Pprint.op_Hat_Hat uu____3767 uu____3768
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
    let uu____3787 =
      let uu____3788 = unparen e in uu____3788.FStar_Parser_AST.tm in
    match uu____3787 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____3791 =
          let uu____3792 =
            let uu____3793 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3793 FStar_Pprint.semi in
          FStar_Pprint.group uu____3792 in
        let uu____3794 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____3791 uu____3794
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____3798 =
          let uu____3799 =
            let uu____3800 =
              let uu____3801 = p_lident x in
              let uu____3802 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____3801 uu____3802 in
            let uu____3803 =
              let uu____3804 = p_noSeqTerm e1 in
              let uu____3805 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____3804 uu____3805 in
            op_Hat_Slash_Plus_Hat uu____3800 uu____3803 in
          FStar_Pprint.group uu____3799 in
        let uu____3806 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____3798 uu____3806
    | uu____3807 ->
        let uu____3808 = p_noSeqTerm e in FStar_Pprint.group uu____3808
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3811 =
      let uu____3812 = unparen e in uu____3812.FStar_Parser_AST.tm in
    match uu____3811 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____3817 =
          let uu____3818 = p_tmIff e1 in
          let uu____3819 =
            let uu____3820 =
              let uu____3821 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3821 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____3820 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3818 uu____3819 in
        FStar_Pprint.group uu____3817
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____3827 =
          let uu____3828 = p_tmIff e1 in
          let uu____3829 =
            let uu____3830 =
              let uu____3831 =
                let uu____3832 = p_typ t in
                let uu____3833 =
                  let uu____3834 = str "by" in
                  let uu____3835 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____3834 uu____3835 in
                FStar_Pprint.op_Hat_Slash_Hat uu____3832 uu____3833 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3831 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____3830 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3828 uu____3829 in
        FStar_Pprint.group uu____3827
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____3836;_},e1::e2::e3::[])
        ->
        let uu____3842 =
          let uu____3843 =
            let uu____3844 =
              let uu____3845 = p_atomicTermNotQUident e1 in
              let uu____3846 =
                let uu____3847 =
                  let uu____3848 =
                    let uu____3849 = p_term e2 in
                    soft_parens_with_nesting uu____3849 in
                  let uu____3850 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____3848 uu____3850 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3847 in
              FStar_Pprint.op_Hat_Hat uu____3845 uu____3846 in
            FStar_Pprint.group uu____3844 in
          let uu____3851 =
            let uu____3852 = p_noSeqTerm e3 in jump2 uu____3852 in
          FStar_Pprint.op_Hat_Hat uu____3843 uu____3851 in
        FStar_Pprint.group uu____3842
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____3853;_},e1::e2::e3::[])
        ->
        let uu____3859 =
          let uu____3860 =
            let uu____3861 =
              let uu____3862 = p_atomicTermNotQUident e1 in
              let uu____3863 =
                let uu____3864 =
                  let uu____3865 =
                    let uu____3866 = p_term e2 in
                    soft_brackets_with_nesting uu____3866 in
                  let uu____3867 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____3865 uu____3867 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3864 in
              FStar_Pprint.op_Hat_Hat uu____3862 uu____3863 in
            FStar_Pprint.group uu____3861 in
          let uu____3868 =
            let uu____3869 = p_noSeqTerm e3 in jump2 uu____3869 in
          FStar_Pprint.op_Hat_Hat uu____3860 uu____3868 in
        FStar_Pprint.group uu____3859
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____3879 =
          let uu____3880 = str "requires" in
          let uu____3881 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3880 uu____3881 in
        FStar_Pprint.group uu____3879
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____3891 =
          let uu____3892 = str "ensures" in
          let uu____3893 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3892 uu____3893 in
        FStar_Pprint.group uu____3891
    | FStar_Parser_AST.Attributes es ->
        let uu____3897 =
          let uu____3898 = str "attributes" in
          let uu____3899 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____3898 uu____3899 in
        FStar_Pprint.group uu____3897
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____3903 = is_unit e3 in
        if uu____3903
        then
          let uu____3904 =
            let uu____3905 =
              let uu____3906 = str "if" in
              let uu____3907 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____3906 uu____3907 in
            let uu____3908 =
              let uu____3909 = str "then" in
              let uu____3910 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____3909 uu____3910 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3905 uu____3908 in
          FStar_Pprint.group uu____3904
        else
          (let e2_doc =
             let uu____3913 =
               let uu____3914 = unparen e2 in uu____3914.FStar_Parser_AST.tm in
             match uu____3913 with
             | FStar_Parser_AST.If (uu____3915,uu____3916,e31) when
                 is_unit e31 ->
                 let uu____3918 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____3918
             | uu____3919 -> p_noSeqTerm e2 in
           let uu____3920 =
             let uu____3921 =
               let uu____3922 = str "if" in
               let uu____3923 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____3922 uu____3923 in
             let uu____3924 =
               let uu____3925 =
                 let uu____3926 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____3926 e2_doc in
               let uu____3927 =
                 let uu____3928 = str "else" in
                 let uu____3929 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____3928 uu____3929 in
               FStar_Pprint.op_Hat_Slash_Hat uu____3925 uu____3927 in
             FStar_Pprint.op_Hat_Slash_Hat uu____3921 uu____3924 in
           FStar_Pprint.group uu____3920)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____3952 =
          let uu____3953 =
            let uu____3954 = str "try" in
            let uu____3955 = p_noSeqTerm e1 in prefix2 uu____3954 uu____3955 in
          let uu____3956 =
            let uu____3957 = str "with" in
            let uu____3958 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____3957 uu____3958 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3953 uu____3956 in
        FStar_Pprint.group uu____3952
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____3989 =
          let uu____3990 =
            let uu____3991 = str "match" in
            let uu____3992 = p_noSeqTerm e1 in
            let uu____3993 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____3991 uu____3992 uu____3993 in
          let uu____3994 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____3990 uu____3994 in
        FStar_Pprint.group uu____3989
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4005 =
          let uu____4006 =
            let uu____4007 = str "let open" in
            let uu____4008 = p_quident uid in
            let uu____4009 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4007 uu____4008 uu____4009 in
          let uu____4010 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4006 uu____4010 in
        FStar_Pprint.group uu____4005
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4027 = str "let" in
          let uu____4028 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4027 uu____4028 in
        let uu____4029 =
          let uu____4030 =
            let uu____4031 =
              let uu____4032 = str "and" in
              precede_break_separate_map let_doc uu____4032 p_letbinding lbs in
            let uu____4037 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4031 uu____4037 in
          FStar_Pprint.group uu____4030 in
        let uu____4038 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4029 uu____4038
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4041;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4044;
                                                         FStar_Parser_AST.level
                                                           = uu____4045;_})
        when matches_var maybe_x x ->
        let uu____4072 =
          let uu____4073 = str "function" in
          let uu____4074 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4073 uu____4074 in
        FStar_Pprint.group uu____4072
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4085 =
          let uu____4086 = p_lident id in
          let uu____4087 =
            let uu____4088 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4088 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4086 uu____4087 in
        FStar_Pprint.group uu____4085
    | uu____4089 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4092 =
      let uu____4093 = unparen e in uu____4093.FStar_Parser_AST.tm in
    match uu____4092 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4109 =
          let uu____4110 =
            let uu____4111 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4111 FStar_Pprint.space in
          let uu____4112 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4110 uu____4112 FStar_Pprint.dot in
        let uu____4113 =
          let uu____4114 = p_trigger trigger in
          let uu____4115 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4114 uu____4115 in
        prefix2 uu____4109 uu____4113
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4131 =
          let uu____4132 =
            let uu____4133 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4133 FStar_Pprint.space in
          let uu____4134 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4132 uu____4134 FStar_Pprint.dot in
        let uu____4135 =
          let uu____4136 = p_trigger trigger in
          let uu____4137 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4136 uu____4137 in
        prefix2 uu____4131 uu____4135
    | uu____4138 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4140 =
      let uu____4141 = unparen e in uu____4141.FStar_Parser_AST.tm in
    match uu____4140 with
    | FStar_Parser_AST.QForall uu____4142 -> str "forall"
    | FStar_Parser_AST.QExists uu____4155 -> str "exists"
    | uu____4168 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___104_4169  ->
    match uu___104_4169 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4181 =
          let uu____4182 =
            let uu____4183 = str "pattern" in
            let uu____4184 =
              let uu____4185 =
                let uu____4186 = p_disjunctivePats pats in jump2 uu____4186 in
              let uu____4187 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4185 uu____4187 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4183 uu____4184 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4182 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4181
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4193 = str "\\/" in
    FStar_Pprint.separate_map uu____4193 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4199 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4199
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4201 =
      let uu____4202 = unparen e in uu____4202.FStar_Parser_AST.tm in
    match uu____4201 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4209 =
          let uu____4210 = str "fun" in
          let uu____4211 =
            let uu____4212 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4212 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4210 uu____4211 in
        let uu____4213 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4209 uu____4213
    | uu____4214 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4217  ->
    match uu____4217 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4236 =
            let uu____4237 = unparen e in uu____4237.FStar_Parser_AST.tm in
          match uu____4236 with
          | FStar_Parser_AST.Match uu____4240 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4255 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4271);
                 FStar_Parser_AST.prange = uu____4272;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4274);
                                                               FStar_Parser_AST.range
                                                                 = uu____4275;
                                                               FStar_Parser_AST.level
                                                                 = uu____4276;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4303 -> (fun x  -> x) in
        let uu____4305 =
          let uu____4306 =
            let uu____4307 =
              let uu____4308 =
                let uu____4309 =
                  let uu____4310 = p_disjunctivePattern pat in
                  let uu____4311 =
                    let uu____4312 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4312 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4310 uu____4311 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4309 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4308 in
            FStar_Pprint.group uu____4307 in
          let uu____4313 =
            let uu____4314 = p_term e in maybe_paren uu____4314 in
          op_Hat_Slash_Plus_Hat uu____4306 uu____4313 in
        FStar_Pprint.group uu____4305
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___105_4315  ->
    match uu___105_4315 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4319 = str "when" in
        let uu____4320 =
          let uu____4321 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4321 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4319 uu____4320
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4323 =
      let uu____4324 = unparen e in uu____4324.FStar_Parser_AST.tm in
    match uu____4323 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4325;_},e1::e2::[])
        ->
        let uu____4330 = str "<==>" in
        let uu____4331 = p_tmImplies e1 in
        let uu____4332 = p_tmIff e2 in
        infix0 uu____4330 uu____4331 uu____4332
    | uu____4333 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4335 =
      let uu____4336 = unparen e in uu____4336.FStar_Parser_AST.tm in
    match uu____4335 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4337;_},e1::e2::[])
        ->
        let uu____4342 = str "==>" in
        let uu____4343 = p_tmArrow p_tmFormula e1 in
        let uu____4344 = p_tmImplies e2 in
        infix0 uu____4342 uu____4343 uu____4344
    | uu____4345 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4350 =
        let uu____4351 = unparen e in uu____4351.FStar_Parser_AST.tm in
      match uu____4350 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4358 =
            let uu____4359 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____4361 = p_binder false b in
                   let uu____4362 =
                     let uu____4363 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4363 in
                   FStar_Pprint.op_Hat_Hat uu____4361 uu____4362) bs in
            let uu____4364 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4359 uu____4364 in
          FStar_Pprint.group uu____4358
      | uu____4365 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4367 =
      let uu____4368 = unparen e in uu____4368.FStar_Parser_AST.tm in
    match uu____4367 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4369;_},e1::e2::[])
        ->
        let uu____4374 = str "\\/" in
        let uu____4375 = p_tmFormula e1 in
        let uu____4376 = p_tmConjunction e2 in
        infix0 uu____4374 uu____4375 uu____4376
    | uu____4377 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4379 =
      let uu____4380 = unparen e in uu____4380.FStar_Parser_AST.tm in
    match uu____4379 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4381;_},e1::e2::[])
        ->
        let uu____4386 = str "/\\" in
        let uu____4387 = p_tmConjunction e1 in
        let uu____4388 = p_tmTuple e2 in
        infix0 uu____4386 uu____4387 uu____4388
    | uu____4389 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4392 =
      let uu____4393 = unparen e in uu____4393.FStar_Parser_AST.tm in
    match uu____4392 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4408 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4408
          (fun uu____4413  ->
             match uu____4413 with | (e1,uu____4419) -> p_tmEq e1) args
    | uu____4420 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4425 =
             let uu____4426 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4426 in
           FStar_Pprint.group uu____4425)
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
      let uu____4471 =
        let uu____4472 = unparen e in uu____4472.FStar_Parser_AST.tm in
      match uu____4471 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____4479 = levels op1 in
          (match uu____4479 with
           | (left1,mine,right1) ->
               let uu____4489 =
                 let uu____4490 = FStar_All.pipe_left str op1 in
                 let uu____4491 = p_tmEq' left1 e1 in
                 let uu____4492 = p_tmEq' right1 e2 in
                 infix0 uu____4490 uu____4491 uu____4492 in
               paren_if curr mine uu____4489)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4493;_},e1::e2::[])
          ->
          let uu____4498 =
            let uu____4499 = p_tmEq e1 in
            let uu____4500 =
              let uu____4501 =
                let uu____4502 =
                  let uu____4503 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4503 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4502 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4501 in
            FStar_Pprint.op_Hat_Hat uu____4499 uu____4500 in
          FStar_Pprint.group uu____4498
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4504;_},e1::[])
          ->
          let uu____4508 = levels "-" in
          (match uu____4508 with
           | (left1,mine,right1) ->
               let uu____4518 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4518)
      | uu____4519 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____4574 =
        let uu____4575 = unparen e in uu____4575.FStar_Parser_AST.tm in
      match uu____4574 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____4578)::(e2,uu____4580)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____4599 = is_list e in Prims.op_Negation uu____4599)
          ->
          let op = "::" in
          let uu____4601 = levels op in
          (match uu____4601 with
           | (left1,mine,right1) ->
               let uu____4611 =
                 let uu____4612 = str op in
                 let uu____4613 = p_tmNoEq' left1 e1 in
                 let uu____4614 = p_tmNoEq' right1 e2 in
                 infix0 uu____4612 uu____4613 uu____4614 in
               paren_if curr mine uu____4611)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____4622 = levels op in
          (match uu____4622 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____4636 = p_binder false b in
                 let uu____4637 =
                   let uu____4638 =
                     let uu____4639 = str op in
                     FStar_Pprint.op_Hat_Hat uu____4639 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4638 in
                 FStar_Pprint.op_Hat_Hat uu____4636 uu____4637 in
               let uu____4640 =
                 let uu____4641 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____4642 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____4641 uu____4642 in
               paren_if curr mine uu____4640)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____4649 = levels op1 in
          (match uu____4649 with
           | (left1,mine,right1) ->
               let uu____4659 =
                 let uu____4660 = str op1 in
                 let uu____4661 = p_tmNoEq' left1 e1 in
                 let uu____4662 = p_tmNoEq' right1 e2 in
                 infix0 uu____4660 uu____4661 uu____4662 in
               paren_if curr mine uu____4659)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____4665 =
            let uu____4666 = p_lidentOrUnderscore lid in
            let uu____4667 =
              let uu____4668 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4668 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4666 uu____4667 in
          FStar_Pprint.group uu____4665
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____4689 =
            let uu____4690 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____4691 =
              let uu____4692 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____4692 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____4690 uu____4691 in
          braces_with_nesting uu____4689
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____4697;_},e1::[])
          ->
          let uu____4701 =
            let uu____4702 = str "~" in
            let uu____4703 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4702 uu____4703 in
          FStar_Pprint.group uu____4701
      | uu____4704 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4706 = p_appTerm e in
    let uu____4707 =
      let uu____4708 =
        let uu____4709 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____4709 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4708 in
    FStar_Pprint.op_Hat_Hat uu____4706 uu____4707
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____4714 =
            let uu____4715 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____4715 t phi in
          soft_parens_with_nesting uu____4714
      | FStar_Parser_AST.TAnnotated uu____4716 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____4721 ->
          let uu____4722 =
            let uu____4723 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4723 in
          failwith uu____4722
      | FStar_Parser_AST.TVariable uu____4724 ->
          let uu____4725 =
            let uu____4726 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4726 in
          failwith uu____4725
      | FStar_Parser_AST.NoName uu____4727 ->
          let uu____4728 =
            let uu____4729 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4729 in
          failwith uu____4728
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____4730  ->
    match uu____4730 with
    | (lid,e) ->
        let uu____4737 =
          let uu____4738 = p_qlident lid in
          let uu____4739 =
            let uu____4740 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____4740 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4738 uu____4739 in
        FStar_Pprint.group uu____4737
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4742 =
      let uu____4743 = unparen e in uu____4743.FStar_Parser_AST.tm in
    match uu____4742 with
    | FStar_Parser_AST.App uu____4744 when is_general_application e ->
        let uu____4751 = head_and_args e in
        (match uu____4751 with
         | (head1,args) ->
             let uu____4776 =
               let uu____4787 = FStar_ST.read should_print_fs_typ_app in
               if uu____4787
               then
                 let uu____4798 =
                   FStar_Util.take
                     (fun uu____4819  ->
                        match uu____4819 with
                        | (uu____4824,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____4798 with
                 | (fs_typ_args,args1) ->
                     let uu____4862 =
                       let uu____4863 = p_indexingTerm head1 in
                       let uu____4864 =
                         let uu____4865 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____4865 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____4863 uu____4864 in
                     (uu____4862, args1)
               else
                 (let uu____4877 = p_indexingTerm head1 in (uu____4877, args)) in
             (match uu____4776 with
              | (head_doc,args1) ->
                  let uu____4898 =
                    let uu____4899 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____4899 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____4898))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____4918 = is_dtuple_constructor lid in
           Prims.op_Negation uu____4918)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____4936 =
               let uu____4937 = p_quident lid in
               let uu____4938 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____4937 uu____4938 in
             FStar_Pprint.group uu____4936
         | hd1::tl1 ->
             let uu____4955 =
               let uu____4956 =
                 let uu____4957 =
                   let uu____4958 = p_quident lid in
                   let uu____4959 = p_argTerm hd1 in
                   prefix2 uu____4958 uu____4959 in
                 FStar_Pprint.group uu____4957 in
               let uu____4960 =
                 let uu____4961 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____4961 in
               FStar_Pprint.op_Hat_Hat uu____4956 uu____4960 in
             FStar_Pprint.group uu____4955)
    | uu____4966 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____4975 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____4975 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____4977 = str "#" in
        let uu____4978 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____4977 uu____4978
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____4980  ->
    match uu____4980 with | (e,uu____4986) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____4991 =
        let uu____4992 = unparen e in uu____4992.FStar_Parser_AST.tm in
      match uu____4991 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____4993;_},e1::e2::[])
          ->
          let uu____4998 =
            let uu____4999 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5000 =
              let uu____5001 =
                let uu____5002 = p_term e2 in
                soft_parens_with_nesting uu____5002 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5001 in
            FStar_Pprint.op_Hat_Hat uu____4999 uu____5000 in
          FStar_Pprint.group uu____4998
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5003;_},e1::e2::[])
          ->
          let uu____5008 =
            let uu____5009 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5010 =
              let uu____5011 =
                let uu____5012 = p_term e2 in
                soft_brackets_with_nesting uu____5012 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5011 in
            FStar_Pprint.op_Hat_Hat uu____5009 uu____5010 in
          FStar_Pprint.group uu____5008
      | uu____5013 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5016 =
      let uu____5017 = unparen e in uu____5017.FStar_Parser_AST.tm in
    match uu____5016 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5020 = p_quident lid in
        let uu____5021 =
          let uu____5022 =
            let uu____5023 = p_term e1 in soft_parens_with_nesting uu____5023 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5022 in
        FStar_Pprint.op_Hat_Hat uu____5020 uu____5021
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5029 = str (FStar_Ident.text_of_id op) in
        let uu____5030 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5029 uu____5030
    | uu____5031 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5033 =
      let uu____5034 = unparen e in uu____5034.FStar_Parser_AST.tm in
    match uu____5033 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____5039 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5046 = str (FStar_Ident.text_of_id op) in
        let uu____5047 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5046 uu____5047
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5051 =
          let uu____5052 =
            let uu____5053 = str (FStar_Ident.text_of_id op) in
            let uu____5054 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5053 uu____5054 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5052 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5051
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5069 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5070 =
          let uu____5071 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5072 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5071 p_tmEq uu____5072 in
        let uu____5079 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5069 uu____5070 uu____5079
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5082 =
          let uu____5083 = p_atomicTermNotQUident e1 in
          let uu____5084 =
            let uu____5085 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5085 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5083 uu____5084 in
        FStar_Pprint.group uu____5082
    | uu____5086 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5088 =
      let uu____5089 = unparen e in uu____5089.FStar_Parser_AST.tm in
    match uu____5088 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5093 = p_quident constr_lid in
        let uu____5094 =
          let uu____5095 =
            let uu____5096 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5096 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5095 in
        FStar_Pprint.op_Hat_Hat uu____5093 uu____5094
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5098 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5098 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5100 = p_term e1 in soft_parens_with_nesting uu____5100
    | uu____5101 when is_array e ->
        let es = extract_from_list e in
        let uu____5105 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5106 =
          let uu____5107 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5107 p_noSeqTerm es in
        let uu____5108 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5105 uu____5106 uu____5108
    | uu____5109 when is_list e ->
        let uu____5110 =
          let uu____5111 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5112 = extract_from_list e in
          separate_map_or_flow uu____5111 p_noSeqTerm uu____5112 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5110 FStar_Pprint.rbracket
    | uu____5115 when is_lex_list e ->
        let uu____5116 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5117 =
          let uu____5118 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5119 = extract_from_list e in
          separate_map_or_flow uu____5118 p_noSeqTerm uu____5119 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5116 uu____5117 FStar_Pprint.rbracket
    | uu____5122 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5126 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5127 =
          let uu____5128 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5128 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5126 uu____5127 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5132 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5133 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5132 uu____5133
    | FStar_Parser_AST.Op (op,args) when
        let uu____5140 = handleable_op op args in
        Prims.op_Negation uu____5140 ->
        let uu____5141 =
          let uu____5142 =
            let uu____5143 =
              let uu____5144 =
                let uu____5145 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5145
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5144 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5143 in
          Prims.strcat "Operation " uu____5142 in
        failwith uu____5141
    | FStar_Parser_AST.Uvar uu____5146 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5147 = p_term e in soft_parens_with_nesting uu____5147
    | FStar_Parser_AST.Const uu____5148 ->
        let uu____5149 = p_term e in soft_parens_with_nesting uu____5149
    | FStar_Parser_AST.Op uu____5150 ->
        let uu____5157 = p_term e in soft_parens_with_nesting uu____5157
    | FStar_Parser_AST.Tvar uu____5158 ->
        let uu____5159 = p_term e in soft_parens_with_nesting uu____5159
    | FStar_Parser_AST.Var uu____5160 ->
        let uu____5161 = p_term e in soft_parens_with_nesting uu____5161
    | FStar_Parser_AST.Name uu____5162 ->
        let uu____5163 = p_term e in soft_parens_with_nesting uu____5163
    | FStar_Parser_AST.Construct uu____5164 ->
        let uu____5175 = p_term e in soft_parens_with_nesting uu____5175
    | FStar_Parser_AST.Abs uu____5176 ->
        let uu____5183 = p_term e in soft_parens_with_nesting uu____5183
    | FStar_Parser_AST.App uu____5184 ->
        let uu____5191 = p_term e in soft_parens_with_nesting uu____5191
    | FStar_Parser_AST.Let uu____5192 ->
        let uu____5205 = p_term e in soft_parens_with_nesting uu____5205
    | FStar_Parser_AST.LetOpen uu____5206 ->
        let uu____5211 = p_term e in soft_parens_with_nesting uu____5211
    | FStar_Parser_AST.Seq uu____5212 ->
        let uu____5217 = p_term e in soft_parens_with_nesting uu____5217
    | FStar_Parser_AST.Bind uu____5218 ->
        let uu____5225 = p_term e in soft_parens_with_nesting uu____5225
    | FStar_Parser_AST.If uu____5226 ->
        let uu____5233 = p_term e in soft_parens_with_nesting uu____5233
    | FStar_Parser_AST.Match uu____5234 ->
        let uu____5249 = p_term e in soft_parens_with_nesting uu____5249
    | FStar_Parser_AST.TryWith uu____5250 ->
        let uu____5265 = p_term e in soft_parens_with_nesting uu____5265
    | FStar_Parser_AST.Ascribed uu____5266 ->
        let uu____5275 = p_term e in soft_parens_with_nesting uu____5275
    | FStar_Parser_AST.Record uu____5276 ->
        let uu____5289 = p_term e in soft_parens_with_nesting uu____5289
    | FStar_Parser_AST.Project uu____5290 ->
        let uu____5295 = p_term e in soft_parens_with_nesting uu____5295
    | FStar_Parser_AST.Product uu____5296 ->
        let uu____5303 = p_term e in soft_parens_with_nesting uu____5303
    | FStar_Parser_AST.Sum uu____5304 ->
        let uu____5311 = p_term e in soft_parens_with_nesting uu____5311
    | FStar_Parser_AST.QForall uu____5312 ->
        let uu____5325 = p_term e in soft_parens_with_nesting uu____5325
    | FStar_Parser_AST.QExists uu____5326 ->
        let uu____5339 = p_term e in soft_parens_with_nesting uu____5339
    | FStar_Parser_AST.Refine uu____5340 ->
        let uu____5345 = p_term e in soft_parens_with_nesting uu____5345
    | FStar_Parser_AST.NamedTyp uu____5346 ->
        let uu____5351 = p_term e in soft_parens_with_nesting uu____5351
    | FStar_Parser_AST.Requires uu____5352 ->
        let uu____5359 = p_term e in soft_parens_with_nesting uu____5359
    | FStar_Parser_AST.Ensures uu____5360 ->
        let uu____5367 = p_term e in soft_parens_with_nesting uu____5367
    | FStar_Parser_AST.Assign uu____5368 ->
        let uu____5373 = p_term e in soft_parens_with_nesting uu____5373
    | FStar_Parser_AST.Attributes uu____5374 ->
        let uu____5377 = p_term e in soft_parens_with_nesting uu____5377
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___108_5378  ->
    match uu___108_5378 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5382 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5382
    | FStar_Const.Const_string (bytes,uu____5384) ->
        let uu____5389 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____5389
    | FStar_Const.Const_bytearray (bytes,uu____5391) ->
        let uu____5396 =
          let uu____5397 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5397 in
        let uu____5398 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5396 uu____5398
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___106_5416 =
          match uu___106_5416 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___107_5420 =
          match uu___107_5420 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5426  ->
               match uu____5426 with
               | (s,w) ->
                   let uu____5433 = signedness s in
                   let uu____5434 = width w in
                   FStar_Pprint.op_Hat_Hat uu____5433 uu____5434)
            sign_width_opt in
        let uu____5435 = str repr in
        FStar_Pprint.op_Hat_Hat uu____5435 ending
    | FStar_Const.Const_range r ->
        let uu____5437 = FStar_Range.string_of_range r in str uu____5437
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5439 = p_quident lid in
        let uu____5440 =
          let uu____5441 =
            let uu____5442 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5442 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5441 in
        FStar_Pprint.op_Hat_Hat uu____5439 uu____5440
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5444 = str "u#" in
    let uu____5445 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____5444 uu____5445
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5447 =
      let uu____5448 = unparen u in uu____5448.FStar_Parser_AST.tm in
    match uu____5447 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5449;_},u1::u2::[])
        ->
        let uu____5454 =
          let uu____5455 = p_universeFrom u1 in
          let uu____5456 =
            let uu____5457 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5457 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5455 uu____5456 in
        FStar_Pprint.group uu____5454
    | FStar_Parser_AST.App uu____5458 ->
        let uu____5465 = head_and_args u in
        (match uu____5465 with
         | (head1,args) ->
             let uu____5490 =
               let uu____5491 = unparen head1 in
               uu____5491.FStar_Parser_AST.tm in
             (match uu____5490 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____5493 =
                    let uu____5494 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____5495 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____5500  ->
                           match uu____5500 with
                           | (u1,uu____5506) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____5494 uu____5495 in
                  FStar_Pprint.group uu____5493
              | uu____5507 ->
                  let uu____5508 =
                    let uu____5509 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____5509 in
                  failwith uu____5508))
    | uu____5510 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5512 =
      let uu____5513 = unparen u in uu____5513.FStar_Parser_AST.tm in
    match uu____5512 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____5536 = p_universeFrom u1 in
        soft_parens_with_nesting uu____5536
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5537;_},uu____5538::uu____5539::[])
        ->
        let uu____5542 = p_universeFrom u in
        soft_parens_with_nesting uu____5542
    | FStar_Parser_AST.App uu____5543 ->
        let uu____5550 = p_universeFrom u in
        soft_parens_with_nesting uu____5550
    | uu____5551 ->
        let uu____5552 =
          let uu____5553 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____5553 in
        failwith uu____5552
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let pat_to_document: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p
let binder_to_document: FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____5571,decls) ->
           let uu____5577 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____5577
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____5586,decls,uu____5588) ->
           let uu____5593 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____5593
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____5622  ->
         match uu____5622 with | (comment,range) -> str comment) comments
let modul_with_comments_to_document:
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____5662,decls) -> decls
        | FStar_Parser_AST.Interface (uu____5668,decls,uu____5670) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____5696 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____5709;
                 FStar_Parser_AST.doc = uu____5710;
                 FStar_Parser_AST.quals = uu____5711;
                 FStar_Parser_AST.attrs = uu____5712;_}::uu____5713 ->
                 let d0 = FStar_List.hd ds in
                 let uu____5719 =
                   let uu____5722 =
                     let uu____5725 = FStar_List.tl ds in d :: uu____5725 in
                   d0 :: uu____5722 in
                 (uu____5719, (d0.FStar_Parser_AST.drange))
             | uu____5730 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____5696 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____5763 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____5763 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____5790 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____5790, comments1))))))