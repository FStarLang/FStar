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
    let uu____50 =
      let uu____51 = FStar_ST.read should_unparen in
      Prims.op_Negation uu____51 in
    if uu____50
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____56 -> t)
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
  let uu____159 =
    let uu____160 =
      let uu____161 = FStar_Pprint.op_Hat_Hat sep break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____161 in
    FStar_Pprint.separate_map uu____160 f l in
  FStar_Pprint.group uu____159
let precede_break_separate_map prec sep f l =
  let uu____196 =
    let uu____197 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
    let uu____198 =
      let uu____199 = FStar_List.hd l in FStar_All.pipe_right uu____199 f in
    FStar_Pprint.precede uu____197 uu____198 in
  let uu____200 =
    let uu____201 = FStar_List.tl l in
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____206 =
           let uu____207 =
             let uu____208 = f x in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____208 in
           FStar_Pprint.op_Hat_Hat sep uu____207 in
         FStar_Pprint.op_Hat_Hat break1 uu____206) uu____201 in
  FStar_Pprint.op_Hat_Hat uu____196 uu____200
let concat_break_map f l =
  let uu____231 =
    FStar_Pprint.concat_map
      (fun x  ->
         let uu____235 = f x in FStar_Pprint.op_Hat_Hat uu____235 break1) l in
  FStar_Pprint.group uu____231
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
    let uu____264 = str "begin" in
    let uu____265 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____264 contents uu____265
let separate_map_or_flow sep f l =
  if (FStar_List.length l) < (Prims.parse_int "10")
  then FStar_Pprint.separate_map sep f l
  else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map n1 b void_ opening sep closing f xs =
  if xs = []
  then void_
  else
    (let uu____361 = FStar_Pprint.separate_map sep f xs in
     FStar_Pprint.soft_surround n1 b opening uu____361 closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____370  ->
    match uu____370 with
    | (comment,keywords1) ->
        let uu____384 =
          let uu____385 =
            let uu____387 = str comment in
            let uu____388 =
              let uu____390 =
                let uu____392 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____399  ->
                       match uu____399 with
                       | (k,v1) ->
                           let uu____404 =
                             let uu____406 = str k in
                             let uu____407 =
                               let uu____409 =
                                 let uu____411 = str v1 in [uu____411] in
                               FStar_Pprint.rarrow :: uu____409 in
                             uu____406 :: uu____407 in
                           FStar_Pprint.concat uu____404) keywords1 in
                [uu____392] in
              FStar_Pprint.space :: uu____390 in
            uu____387 :: uu____388 in
          FStar_Pprint.concat uu____385 in
        FStar_Pprint.group uu____384
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____416 =
      let uu____417 = unparen e in uu____417.FStar_Parser_AST.tm in
    match uu____416 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____418 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____427 =
        let uu____428 = unparen t in uu____428.FStar_Parser_AST.tm in
      match uu____427 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____430 -> false
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
        let uu____452 =
          let uu____453 = unparen e in uu____453.FStar_Parser_AST.tm in
        match uu____452 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____461::(e2,uu____463)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____475 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____487 =
      let uu____488 = unparen e in uu____488.FStar_Parser_AST.tm in
    match uu____487 with
    | FStar_Parser_AST.Construct (uu____490,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____496,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____508 = extract_from_list e2 in e1 :: uu____508
    | uu____510 ->
        let uu____511 =
          let uu____512 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____512 in
        failwith uu____511
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____518 =
      let uu____519 = unparen e in uu____519.FStar_Parser_AST.tm in
    match uu____518 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____521;
           FStar_Parser_AST.level = uu____522;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____524 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____529 =
      let uu____530 = unparen e in uu____530.FStar_Parser_AST.tm in
    match uu____529 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____533;
           FStar_Parser_AST.level = uu____534;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____536;
                                                        FStar_Parser_AST.level
                                                          = uu____537;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____539;
                                                   FStar_Parser_AST.level =
                                                     uu____540;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____542;
                FStar_Parser_AST.level = uu____543;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____545;
           FStar_Parser_AST.level = uu____546;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____548 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____554 =
      let uu____555 = unparen e in uu____555.FStar_Parser_AST.tm in
    match uu____554 with
    | FStar_Parser_AST.Var uu____557 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____558;
           FStar_Parser_AST.range = uu____559;
           FStar_Parser_AST.level = uu____560;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____561;
                                                        FStar_Parser_AST.range
                                                          = uu____562;
                                                        FStar_Parser_AST.level
                                                          = uu____563;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____565;
                                                   FStar_Parser_AST.level =
                                                     uu____566;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____567;
                FStar_Parser_AST.range = uu____568;
                FStar_Parser_AST.level = uu____569;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____571;
           FStar_Parser_AST.level = uu____572;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____574 = extract_from_ref_set e1 in
        let uu____576 = extract_from_ref_set e2 in
        FStar_List.append uu____574 uu____576
    | uu____578 ->
        let uu____579 =
          let uu____580 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____580 in
        failwith uu____579
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____586 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____586
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____591 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____591
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
      let uu____624 =
        let uu____625 = unparen e1 in uu____625.FStar_Parser_AST.tm in
      match uu____624 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____636 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____646 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____651 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____656 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___93_667  ->
    match uu___93_667 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___94_681  ->
      match uu___94_681 with
      | FStar_Util.Inl c ->
          let uu____685 = FStar_String.get s (Prims.parse_int "0") in
          uu____685 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level s uu____706 =
  match uu____706 with
  | (assoc_levels,tokens) ->
      let uu____720 = FStar_List.tryFind (matches_token s) tokens in
      uu____720 <> FStar_Pervasives_Native.None
let opinfix4 uu____739 = (Right, [FStar_Util.Inr "**"])
let opinfix3 uu____755 =
  (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
let opinfix2 uu____775 = (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-'])
let minus_lvl uu____793 = (Left, [FStar_Util.Inr "-"])
let opinfix1 uu____809 = (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^'])
let pipe_right uu____827 = (Left, [FStar_Util.Inr "|>"])
let opinfix0d uu____843 = (Left, [FStar_Util.Inl '$'])
let opinfix0c uu____859 =
  (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
let equal uu____879 = (Left, [FStar_Util.Inr "="])
let opinfix0b uu____895 = (Left, [FStar_Util.Inl '&'])
let opinfix0a uu____911 = (Left, [FStar_Util.Inl '|'])
let colon_equals uu____927 = (NonAssoc, [FStar_Util.Inr ":="])
let amp uu____943 = (Right, [FStar_Util.Inr "&"])
let colon_colon uu____959 = (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___95_1056 =
    match uu___95_1056 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1078  ->
         match uu____1078 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1122 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1122 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1147) ->
          assoc_levels
      | uu____1168 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level l =
  let find_level_and_max n1 level =
    let uu____1228 =
      FStar_List.tryFind
        (fun uu____1249  ->
           match uu____1249 with
           | (uu____1258,tokens) ->
               tokens = (FStar_Pervasives_Native.snd level)) level_table in
    match uu____1228 with
    | FStar_Pervasives_Native.Some ((uu____1278,l1,uu____1280),uu____1281) ->
        max n1 l1
    | FStar_Pervasives_Native.None  ->
        let uu____1307 =
          let uu____1308 =
            let uu____1309 =
              FStar_List.map token_to_string
                (FStar_Pervasives_Native.snd level) in
            FStar_String.concat "," uu____1309 in
          FStar_Util.format1 "Undefined associativity level %s" uu____1308 in
        failwith uu____1307 in
  FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12 uu____1336 =
  [opinfix0a ();
  opinfix0b ();
  opinfix0c ();
  opinfix0d ();
  opinfix1 ();
  opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____1376 =
      let uu____1383 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1383 (operatorInfix0ad12 ()) in
    uu____1376 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____1440 =
      let uu____1447 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____1447 opinfix34 in
    uu____1440 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____1483 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____1483
    then Prims.parse_int "1"
    else
      (let uu____1485 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____1485
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
  | uu____1507 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment printer tm tmrange =
  let rec comments_before_pos acc print_pos lookahead_pos =
    let uu____1557 = FStar_ST.read comment_stack in
    match uu____1557 with
    | [] -> (acc, false)
    | (comment,crange)::cs ->
        let uu____1578 = FStar_Range.range_before_pos crange print_pos in
        if uu____1578
        then
          (FStar_ST.write comment_stack cs;
           (let uu____1587 =
              let uu____1588 =
                let uu____1589 = str comment in
                FStar_Pprint.op_Hat_Hat uu____1589 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat acc uu____1588 in
            comments_before_pos uu____1587 print_pos lookahead_pos))
        else
          (let uu____1591 = FStar_Range.range_before_pos crange lookahead_pos in
           (acc, uu____1591)) in
  let uu____1592 =
    let uu____1595 =
      let uu____1596 = FStar_Range.start_of_range tmrange in
      FStar_Range.end_of_line uu____1596 in
    let uu____1597 = FStar_Range.end_of_range tmrange in
    comments_before_pos FStar_Pprint.empty uu____1595 uu____1597 in
  match uu____1592 with
  | (comments,has_lookahead) ->
      let printed_e = printer tm in
      let comments1 =
        if has_lookahead
        then
          let pos = FStar_Range.end_of_range tmrange in
          let uu____1603 = comments_before_pos comments pos pos in
          FStar_Pervasives_Native.fst uu____1603
        else comments in
      let uu____1607 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
      FStar_Pprint.group uu____1607
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____1624 = FStar_ST.read comment_stack in
          match uu____1624 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____1648 =
                    let uu____1649 =
                      let uu____1650 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____1650 in
                    uu____1649 - lbegin in
                  max k uu____1648 in
                let doc2 =
                  let uu____1652 =
                    let uu____1653 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____1654 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____1653 uu____1654 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____1652 in
                let uu____1655 =
                  let uu____1656 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____1656 in
                place_comments_until_pos (Prims.parse_int "1") uu____1655
                  pos_end doc2))
          | uu____1657 ->
              let lnum =
                let uu____1662 =
                  let uu____1663 = FStar_Range.line_of_pos pos_end in
                  uu____1663 - lbegin in
                max (Prims.parse_int "1") uu____1662 in
              let uu____1664 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____1664
let separate_map_with_comments prefix1 sep f xs extract_range =
  let fold_fun uu____1719 x =
    match uu____1719 with
    | (last_line,doc1) ->
        let r = extract_range x in
        let doc2 =
          let uu____1729 = FStar_Range.start_of_range r in
          place_comments_until_pos (Prims.parse_int "1") last_line uu____1729
            doc1 in
        let uu____1730 =
          let uu____1731 = FStar_Range.end_of_range r in
          FStar_Range.line_of_pos uu____1731 in
        let uu____1732 =
          let uu____1733 =
            let uu____1734 = f x in FStar_Pprint.op_Hat_Hat sep uu____1734 in
          FStar_Pprint.op_Hat_Hat doc2 uu____1733 in
        (uu____1730, uu____1732) in
  let uu____1735 =
    let uu____1739 = FStar_List.hd xs in
    let uu____1740 = FStar_List.tl xs in (uu____1739, uu____1740) in
  match uu____1735 with
  | (x,xs1) ->
      let init1 =
        let uu____1750 =
          let uu____1751 =
            let uu____1752 = extract_range x in
            FStar_Range.end_of_range uu____1752 in
          FStar_Range.line_of_pos uu____1751 in
        let uu____1753 =
          let uu____1754 = f x in FStar_Pprint.op_Hat_Hat prefix1 uu____1754 in
        (uu____1750, uu____1753) in
      let uu____1755 = FStar_List.fold_left fold_fun init1 xs1 in
      FStar_Pervasives_Native.snd uu____1755
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____1999 =
      let uu____2000 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____2001 =
        let uu____2002 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____2003 =
          let uu____2004 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____2005 =
            let uu____2006 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____2006 in
          FStar_Pprint.op_Hat_Hat uu____2004 uu____2005 in
        FStar_Pprint.op_Hat_Hat uu____2002 uu____2003 in
      FStar_Pprint.op_Hat_Hat uu____2000 uu____2001 in
    FStar_Pprint.group uu____1999
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____2009 =
      let uu____2010 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____2010 in
    let uu____2011 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____2009 FStar_Pprint.space uu____2011
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____2012  ->
    match uu____2012 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____2033 =
                match uu____2033 with
                | (kwd1,arg) ->
                    let uu____2038 = str "@" in
                    let uu____2039 =
                      let uu____2040 = str kwd1 in
                      let uu____2041 =
                        let uu____2042 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2042 in
                      FStar_Pprint.op_Hat_Hat uu____2040 uu____2041 in
                    FStar_Pprint.op_Hat_Hat uu____2038 uu____2039 in
              let uu____2043 =
                let uu____2044 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____2044 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2043 in
        let uu____2047 =
          let uu____2048 =
            let uu____2049 =
              let uu____2050 =
                let uu____2051 = str doc1 in
                let uu____2052 =
                  let uu____2053 =
                    let uu____2054 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2054 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2053 in
                FStar_Pprint.op_Hat_Hat uu____2051 uu____2052 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2050 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2049 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2048 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2047
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____2057 =
          let uu____2058 = str "open" in
          let uu____2059 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2058 uu____2059 in
        FStar_Pprint.group uu____2057
    | FStar_Parser_AST.Include uid ->
        let uu____2061 =
          let uu____2062 = str "include" in
          let uu____2063 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2062 uu____2063 in
        FStar_Pprint.group uu____2061
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____2066 =
          let uu____2067 = str "module" in
          let uu____2068 =
            let uu____2069 =
              let uu____2070 = p_uident uid1 in
              let uu____2071 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2070 uu____2071 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2069 in
          FStar_Pprint.op_Hat_Hat uu____2067 uu____2068 in
        let uu____2072 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____2066 uu____2072
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____2074 =
          let uu____2075 = str "module" in
          let uu____2076 =
            let uu____2077 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2077 in
          FStar_Pprint.op_Hat_Hat uu____2075 uu____2076 in
        FStar_Pprint.group uu____2074
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____2096 = str "effect" in
          let uu____2097 =
            let uu____2098 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2098 in
          FStar_Pprint.op_Hat_Hat uu____2096 uu____2097 in
        let uu____2099 =
          let uu____2100 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____2100 FStar_Pprint.equals in
        let uu____2101 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2099 uu____2101
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____2111 = str "type" in
        let uu____2112 = str "and" in
        precede_break_separate_map uu____2111 uu____2112 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____2125 = str "let" in
          let uu____2126 =
            let uu____2127 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____2127 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____2125 uu____2126 in
        let uu____2128 =
          let uu____2129 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____2129 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____2128 p_letbinding lbs
          (fun uu____2135  ->
             match uu____2135 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2142 =
          let uu____2143 = str "val" in
          let uu____2144 =
            let uu____2145 =
              let uu____2146 = p_lident lid in
              let uu____2147 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2146 uu____2147 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2145 in
          FStar_Pprint.op_Hat_Hat uu____2143 uu____2144 in
        let uu____2148 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2142 uu____2148
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2152 =
            let uu____2153 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2153 FStar_Util.is_upper in
          if uu____2152
          then FStar_Pprint.empty
          else
            (let uu____2155 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2155 FStar_Pprint.space) in
        let uu____2156 =
          let uu____2157 =
            let uu____2158 = p_ident id in
            let uu____2159 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2158 uu____2159 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2157 in
        let uu____2160 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2156 uu____2160
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2165 = str "exception" in
        let uu____2166 =
          let uu____2167 =
            let uu____2168 = p_uident uid in
            let uu____2169 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2174 = str "of" in
                   let uu____2175 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2174 uu____2175) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2168 uu____2169 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2167 in
        FStar_Pprint.op_Hat_Hat uu____2165 uu____2166
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2177 = str "new_effect" in
        let uu____2178 =
          let uu____2179 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2179 in
        FStar_Pprint.op_Hat_Hat uu____2177 uu____2178
    | FStar_Parser_AST.SubEffect se ->
        let uu____2181 = str "sub_effect" in
        let uu____2182 =
          let uu____2183 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2183 in
        FStar_Pprint.op_Hat_Hat uu____2181 uu____2182
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2186 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2186 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2187 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2188) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___96_2197  ->
    match uu___96_2197 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2199 = str "#set-options" in
        let uu____2200 =
          let uu____2201 =
            let uu____2202 = str s in FStar_Pprint.dquotes uu____2202 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2201 in
        FStar_Pprint.op_Hat_Hat uu____2199 uu____2200
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2205 = str "#reset-options" in
        let uu____2206 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2210 =
                 let uu____2211 = str s in FStar_Pprint.dquotes uu____2211 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2210) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2205 uu____2206
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2217  ->
    match uu____2217 with
    | (typedecl,fsdoc_opt) ->
        let uu____2225 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2226 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2225 uu____2226
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___97_2227  ->
    match uu___97_2227 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2238 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2250 =
          let uu____2251 = p_typ t in prefix2 FStar_Pprint.equals uu____2251 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2277 =
          match uu____2277 with
          | (lid1,t,doc_opt) ->
              let uu____2287 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2287 in
        let p_fields uu____2296 =
          let uu____2297 =
            let uu____2298 =
              let uu____2299 =
                let uu____2300 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2300 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2299 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2298 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2297 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2336 =
          match uu____2336 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2352 =
                  let uu____2353 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2353 in
                FStar_Range.extend_to_end_of_line uu____2352 in
              let p_constructorBranch decl =
                let uu____2373 =
                  let uu____2374 =
                    let uu____2375 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2375 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2374 in
                FStar_Pprint.group uu____2373 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2387 =
          let uu____2388 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2388 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2397  ->
             let uu____2398 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2398)
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
            let uu____2409 = p_ident lid in
            let uu____2410 =
              let uu____2411 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2411 in
            FStar_Pprint.op_Hat_Hat uu____2409 uu____2410
          else
            (let binders_doc =
               let uu____2414 = p_typars bs in
               let uu____2415 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2419 =
                        let uu____2420 =
                          let uu____2421 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2421 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2420 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2419) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2414 uu____2415 in
             let uu____2422 = p_ident lid in
             let uu____2423 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2422 binders_doc uu____2423)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____2424  ->
    match uu____2424 with
    | (lid,t,doc_opt) ->
        let uu____2434 =
          let uu____2435 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2436 =
            let uu____2437 = p_lident lid in
            let uu____2438 =
              let uu____2439 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2439 in
            FStar_Pprint.op_Hat_Hat uu____2437 uu____2438 in
          FStar_Pprint.op_Hat_Hat uu____2435 uu____2436 in
        FStar_Pprint.group uu____2434
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____2440  ->
    match uu____2440 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2458 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2459 =
          let uu____2460 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2461 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2466 =
                   let uu____2467 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2467 in
                 let uu____2468 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2466 uu____2468) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2460 uu____2461 in
        FStar_Pprint.op_Hat_Hat uu____2458 uu____2459
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2469  ->
    match uu____2469 with
    | (pat,e) ->
        let pat_doc =
          let uu____2475 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2482 =
                  let uu____2483 =
                    let uu____2484 =
                      let uu____2485 =
                        let uu____2486 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2486 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2485 in
                    FStar_Pprint.group uu____2484 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2483 in
                (pat1, uu____2482)
            | uu____2487 -> (pat, FStar_Pprint.empty) in
          match uu____2475 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2491);
                      FStar_Parser_AST.prange = uu____2492;_},pats)
                   ->
                   let uu____2498 = p_lident x in
                   let uu____2499 =
                     let uu____2500 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2500 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2498 uu____2499
                     FStar_Pprint.equals
               | uu____2501 ->
                   let uu____2502 =
                     let uu____2503 = p_tuplePattern pat1 in
                     let uu____2504 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2503 uu____2504 in
                   FStar_Pprint.group uu____2502) in
        let uu____2505 = p_term e in prefix2 pat_doc uu____2505
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___98_2506  ->
    match uu___98_2506 with
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
        let uu____2524 = p_uident uid in
        let uu____2525 = p_binders true bs in
        let uu____2526 =
          let uu____2527 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2527 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2524 uu____2525 uu____2526
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
          let uu____2534 =
            let uu____2535 =
              let uu____2536 =
                let uu____2537 = p_uident uid in
                let uu____2538 = p_binders true bs in
                let uu____2539 =
                  let uu____2540 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2540 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2537 uu____2538 uu____2539 in
              FStar_Pprint.group uu____2536 in
            let uu____2541 =
              let uu____2542 = str "with" in
              let uu____2543 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2542 uu____2543 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2535 uu____2541 in
          braces_with_nesting uu____2534
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____2560 =
          let uu____2561 = p_lident lid in
          let uu____2562 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2561 uu____2562 in
        let uu____2563 = p_simpleTerm e in prefix2 uu____2560 uu____2563
    | uu____2564 ->
        let uu____2565 =
          let uu____2566 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2566 in
        failwith uu____2565
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2599 =
        match uu____2599 with
        | (kwd1,t) ->
            let uu____2604 =
              let uu____2605 = str kwd1 in
              let uu____2606 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2605 uu____2606 in
            let uu____2607 = p_simpleTerm t in prefix2 uu____2604 uu____2607 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2610 =
      let uu____2611 =
        let uu____2612 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2613 =
          let uu____2614 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2614 in
        FStar_Pprint.op_Hat_Hat uu____2612 uu____2613 in
      let uu____2615 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2611 uu____2615 in
    let uu____2616 =
      let uu____2617 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2617 in
    FStar_Pprint.op_Hat_Hat uu____2610 uu____2616
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___99_2618  ->
    match uu___99_2618 with
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
    let uu____2620 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2620
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___100_2621  ->
    match uu___100_2621 with
    | FStar_Parser_AST.Rec  ->
        let uu____2622 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2622
    | FStar_Parser_AST.Mutable  ->
        let uu____2623 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2623
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___101_2624  ->
    match uu___101_2624 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2628 =
          let uu____2629 =
            let uu____2630 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2630 in
          FStar_Pprint.separate_map uu____2629 p_tuplePattern pats in
        FStar_Pprint.group uu____2628
    | uu____2631 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2636 =
          let uu____2637 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2637 p_constructorPattern pats in
        FStar_Pprint.group uu____2636
    | uu____2638 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2641;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2645 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2646 = p_constructorPattern hd1 in
        let uu____2647 = p_constructorPattern tl1 in
        infix0 uu____2645 uu____2646 uu____2647
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2649;_},pats)
        ->
        let uu____2653 = p_quident uid in
        let uu____2654 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2653 uu____2654
    | uu____2655 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2659 =
          let uu____2662 =
            let uu____2663 = unparen t in uu____2663.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2662) in
        (match uu____2659 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2668;
               FStar_Parser_AST.blevel = uu____2669;
               FStar_Parser_AST.aqual = uu____2670;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2674 =
               let uu____2675 = p_ident lid in
               p_refinement aqual uu____2675 t1 phi in
             soft_parens_with_nesting uu____2674
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2677;
               FStar_Parser_AST.blevel = uu____2678;
               FStar_Parser_AST.aqual = uu____2679;_},phi))
             ->
             let uu____2681 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2681
         | uu____2682 ->
             let uu____2685 =
               let uu____2686 = p_tuplePattern pat in
               let uu____2687 =
                 let uu____2688 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2689 =
                   let uu____2690 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2690 in
                 FStar_Pprint.op_Hat_Hat uu____2688 uu____2689 in
               FStar_Pprint.op_Hat_Hat uu____2686 uu____2687 in
             soft_parens_with_nesting uu____2685)
    | FStar_Parser_AST.PatList pats ->
        let uu____2693 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2693 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2703 =
          match uu____2703 with
          | (lid,pat) ->
              let uu____2708 = p_qlident lid in
              let uu____2709 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2708 uu____2709 in
        let uu____2710 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2710
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2716 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2717 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2718 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2716 uu____2717 uu____2718
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2726 =
          let uu____2727 =
            let uu____2728 = str (FStar_Ident.text_of_id op) in
            let uu____2729 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2728 uu____2729 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2727 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2726
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2735 = FStar_Pprint.optional p_aqual aqual in
        let uu____2736 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2735 uu____2736
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2738 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2740;
           FStar_Parser_AST.prange = uu____2741;_},uu____2742)
        ->
        let uu____2745 = p_tuplePattern p in
        soft_parens_with_nesting uu____2745
    | FStar_Parser_AST.PatTuple (uu____2746,false ) ->
        let uu____2749 = p_tuplePattern p in
        soft_parens_with_nesting uu____2749
    | uu____2750 ->
        let uu____2751 =
          let uu____2752 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2752 in
        failwith uu____2751
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2756 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2757 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2756 uu____2757
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2762 =
              let uu____2763 = unparen t in uu____2763.FStar_Parser_AST.tm in
            match uu____2762 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2766;
                   FStar_Parser_AST.blevel = uu____2767;
                   FStar_Parser_AST.aqual = uu____2768;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2770 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2770 t1 phi
            | uu____2771 ->
                let uu____2772 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2773 =
                  let uu____2774 = p_lident lid in
                  let uu____2775 =
                    let uu____2776 =
                      let uu____2777 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2778 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2777 uu____2778 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2776 in
                  FStar_Pprint.op_Hat_Hat uu____2774 uu____2775 in
                FStar_Pprint.op_Hat_Hat uu____2772 uu____2773 in
          if is_atomic
          then
            let uu____2779 =
              let uu____2780 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2780 in
            FStar_Pprint.group uu____2779
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2782 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2786 =
            let uu____2787 = unparen t in uu____2787.FStar_Parser_AST.tm in
          (match uu____2786 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2789;
                  FStar_Parser_AST.blevel = uu____2790;
                  FStar_Parser_AST.aqual = uu____2791;_},phi)
               ->
               if is_atomic
               then
                 let uu____2793 =
                   let uu____2794 =
                     let uu____2795 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2795 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2794 in
                 FStar_Pprint.group uu____2793
               else
                 (let uu____2797 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2797)
           | uu____2798 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2805 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2806 =
            let uu____2807 =
              let uu____2808 =
                let uu____2809 = p_appTerm t in
                let uu____2810 =
                  let uu____2811 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2811 in
                FStar_Pprint.op_Hat_Hat uu____2809 uu____2810 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2808 in
            FStar_Pprint.op_Hat_Hat binder uu____2807 in
          FStar_Pprint.op_Hat_Hat uu____2805 uu____2806
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
    let uu____2824 =
      let uu____2825 = unparen e in uu____2825.FStar_Parser_AST.tm in
    match uu____2824 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2828 =
          let uu____2829 =
            let uu____2830 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2830 FStar_Pprint.semi in
          FStar_Pprint.group uu____2829 in
        let uu____2831 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2828 uu____2831
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2835 =
          let uu____2836 =
            let uu____2837 =
              let uu____2838 = p_lident x in
              let uu____2839 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2838 uu____2839 in
            let uu____2840 =
              let uu____2841 = p_noSeqTerm e1 in
              let uu____2842 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2841 uu____2842 in
            op_Hat_Slash_Plus_Hat uu____2837 uu____2840 in
          FStar_Pprint.group uu____2836 in
        let uu____2843 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2835 uu____2843
    | uu____2844 ->
        let uu____2845 = p_noSeqTerm e in FStar_Pprint.group uu____2845
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2848 =
      let uu____2849 = unparen e in uu____2849.FStar_Parser_AST.tm in
    match uu____2848 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____2853 =
          let uu____2854 = p_tmIff e1 in
          let uu____2855 =
            let uu____2856 =
              let uu____2857 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2857 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2856 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2854 uu____2855 in
        FStar_Pprint.group uu____2853
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____2862 =
          let uu____2863 = p_tmIff e1 in
          let uu____2864 =
            let uu____2865 =
              let uu____2866 =
                let uu____2867 = p_typ t in
                let uu____2868 =
                  let uu____2869 = str "by" in
                  let uu____2870 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2869 uu____2870 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2867 uu____2868 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2866 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2865 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2863 uu____2864 in
        FStar_Pprint.group uu____2862
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2871;_},e1::e2::e3::[])
        ->
        let uu____2876 =
          let uu____2877 =
            let uu____2878 =
              let uu____2879 = p_atomicTermNotQUident e1 in
              let uu____2880 =
                let uu____2881 =
                  let uu____2882 =
                    let uu____2883 = p_term e2 in
                    soft_parens_with_nesting uu____2883 in
                  let uu____2884 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2882 uu____2884 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2881 in
              FStar_Pprint.op_Hat_Hat uu____2879 uu____2880 in
            FStar_Pprint.group uu____2878 in
          let uu____2885 =
            let uu____2886 = p_noSeqTerm e3 in jump2 uu____2886 in
          FStar_Pprint.op_Hat_Hat uu____2877 uu____2885 in
        FStar_Pprint.group uu____2876
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2887;_},e1::e2::e3::[])
        ->
        let uu____2892 =
          let uu____2893 =
            let uu____2894 =
              let uu____2895 = p_atomicTermNotQUident e1 in
              let uu____2896 =
                let uu____2897 =
                  let uu____2898 =
                    let uu____2899 = p_term e2 in
                    soft_brackets_with_nesting uu____2899 in
                  let uu____2900 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2898 uu____2900 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2897 in
              FStar_Pprint.op_Hat_Hat uu____2895 uu____2896 in
            FStar_Pprint.group uu____2894 in
          let uu____2901 =
            let uu____2902 = p_noSeqTerm e3 in jump2 uu____2902 in
          FStar_Pprint.op_Hat_Hat uu____2893 uu____2901 in
        FStar_Pprint.group uu____2892
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2909 =
          let uu____2910 = str "requires" in
          let uu____2911 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2910 uu____2911 in
        FStar_Pprint.group uu____2909
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2918 =
          let uu____2919 = str "ensures" in
          let uu____2920 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2919 uu____2920 in
        FStar_Pprint.group uu____2918
    | FStar_Parser_AST.Attributes es ->
        let uu____2923 =
          let uu____2924 = str "attributes" in
          let uu____2925 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2924 uu____2925 in
        FStar_Pprint.group uu____2923
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2929 = is_unit e3 in
        if uu____2929
        then
          let uu____2930 =
            let uu____2931 =
              let uu____2932 = str "if" in
              let uu____2933 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2932 uu____2933 in
            let uu____2934 =
              let uu____2935 = str "then" in
              let uu____2936 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2935 uu____2936 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2931 uu____2934 in
          FStar_Pprint.group uu____2930
        else
          (let e2_doc =
             let uu____2939 =
               let uu____2940 = unparen e2 in uu____2940.FStar_Parser_AST.tm in
             match uu____2939 with
             | FStar_Parser_AST.If (uu____2941,uu____2942,e31) when
                 is_unit e31 ->
                 let uu____2944 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2944
             | uu____2945 -> p_noSeqTerm e2 in
           let uu____2946 =
             let uu____2947 =
               let uu____2948 = str "if" in
               let uu____2949 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2948 uu____2949 in
             let uu____2950 =
               let uu____2951 =
                 let uu____2952 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2952 e2_doc in
               let uu____2953 =
                 let uu____2954 = str "else" in
                 let uu____2955 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2954 uu____2955 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2951 uu____2953 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2947 uu____2950 in
           FStar_Pprint.group uu____2946)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2968 =
          let uu____2969 =
            let uu____2970 = str "try" in
            let uu____2971 = p_noSeqTerm e1 in prefix2 uu____2970 uu____2971 in
          let uu____2972 =
            let uu____2973 = str "with" in
            let uu____2974 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2973 uu____2974 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2969 uu____2972 in
        FStar_Pprint.group uu____2968
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2991 =
          let uu____2992 =
            let uu____2993 = str "match" in
            let uu____2994 = p_noSeqTerm e1 in
            let uu____2995 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2993 uu____2994 uu____2995 in
          let uu____2996 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2992 uu____2996 in
        FStar_Pprint.group uu____2991
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____3003 =
          let uu____3004 =
            let uu____3005 = str "let open" in
            let uu____3006 = p_quident uid in
            let uu____3007 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____3005 uu____3006 uu____3007 in
          let uu____3008 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3004 uu____3008 in
        FStar_Pprint.group uu____3003
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____3019 = str "let" in
          let uu____3020 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____3019 uu____3020 in
        let uu____3021 =
          let uu____3022 =
            let uu____3023 =
              let uu____3024 = str "and" in
              precede_break_separate_map let_doc uu____3024 p_letbinding lbs in
            let uu____3027 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____3023 uu____3027 in
          FStar_Pprint.group uu____3022 in
        let uu____3028 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____3021 uu____3028
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____3031;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____3034;
                                                         FStar_Parser_AST.level
                                                           = uu____3035;_})
        when matches_var maybe_x x ->
        let uu____3049 =
          let uu____3050 = str "function" in
          let uu____3051 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____3050 uu____3051 in
        FStar_Pprint.group uu____3049
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____3058 =
          let uu____3059 = p_lident id in
          let uu____3060 =
            let uu____3061 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____3061 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3059 uu____3060 in
        FStar_Pprint.group uu____3058
    | uu____3062 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3065 =
      let uu____3066 = unparen e in uu____3066.FStar_Parser_AST.tm in
    match uu____3065 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____3076 =
          let uu____3077 =
            let uu____3078 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____3078 FStar_Pprint.space in
          let uu____3079 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3077 uu____3079 FStar_Pprint.dot in
        let uu____3080 =
          let uu____3081 = p_trigger trigger in
          let uu____3082 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____3081 uu____3082 in
        prefix2 uu____3076 uu____3080
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____3092 =
          let uu____3093 =
            let uu____3094 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____3094 FStar_Pprint.space in
          let uu____3095 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3093 uu____3095 FStar_Pprint.dot in
        let uu____3096 =
          let uu____3097 = p_trigger trigger in
          let uu____3098 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____3097 uu____3098 in
        prefix2 uu____3092 uu____3096
    | uu____3099 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3101 =
      let uu____3102 = unparen e in uu____3102.FStar_Parser_AST.tm in
    match uu____3101 with
    | FStar_Parser_AST.QForall uu____3103 -> str "forall"
    | FStar_Parser_AST.QExists uu____3110 -> str "exists"
    | uu____3117 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___102_3118  ->
    match uu___102_3118 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____3125 =
          let uu____3126 =
            let uu____3127 = str "pattern" in
            let uu____3128 =
              let uu____3129 =
                let uu____3130 = p_disjunctivePats pats in jump2 uu____3130 in
              let uu____3131 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____3129 uu____3131 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3127 uu____3128 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3126 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____3125
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3135 = str "\\/" in
    FStar_Pprint.separate_map uu____3135 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3139 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____3139
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3141 =
      let uu____3142 = unparen e in uu____3142.FStar_Parser_AST.tm in
    match uu____3141 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____3147 =
          let uu____3148 = str "fun" in
          let uu____3149 =
            let uu____3150 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____3150 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____3148 uu____3149 in
        let uu____3151 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____3147 uu____3151
    | uu____3152 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3155  ->
    match uu____3155 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3168 =
            let uu____3169 = unparen e in uu____3169.FStar_Parser_AST.tm in
          match uu____3168 with
          | FStar_Parser_AST.Match uu____3172 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3180 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3189);
                 FStar_Parser_AST.prange = uu____3190;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3192);
                                                               FStar_Parser_AST.range
                                                                 = uu____3193;
                                                               FStar_Parser_AST.level
                                                                 = uu____3194;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3208 -> (fun x  -> x) in
        let uu____3210 =
          let uu____3211 =
            let uu____3212 =
              let uu____3213 =
                let uu____3214 =
                  let uu____3215 = p_disjunctivePattern pat in
                  let uu____3216 =
                    let uu____3217 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3217 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3215 uu____3216 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3214 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3213 in
            FStar_Pprint.group uu____3212 in
          let uu____3218 =
            let uu____3219 = p_term e in maybe_paren uu____3219 in
          op_Hat_Slash_Plus_Hat uu____3211 uu____3218 in
        FStar_Pprint.group uu____3210
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___103_3220  ->
    match uu___103_3220 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____3223 = str "when" in
        let uu____3224 =
          let uu____3225 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3225 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3223 uu____3224
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3227 =
      let uu____3228 = unparen e in uu____3228.FStar_Parser_AST.tm in
    match uu____3227 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3229;_},e1::e2::[])
        ->
        let uu____3233 = str "<==>" in
        let uu____3234 = p_tmImplies e1 in
        let uu____3235 = p_tmIff e2 in
        infix0 uu____3233 uu____3234 uu____3235
    | uu____3236 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3238 =
      let uu____3239 = unparen e in uu____3239.FStar_Parser_AST.tm in
    match uu____3238 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3240;_},e1::e2::[])
        ->
        let uu____3244 = str "==>" in
        let uu____3245 = p_tmArrow p_tmFormula e1 in
        let uu____3246 = p_tmImplies e2 in
        infix0 uu____3244 uu____3245 uu____3246
    | uu____3247 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3252 =
        let uu____3253 = unparen e in uu____3253.FStar_Parser_AST.tm in
      match uu____3252 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3258 =
            let uu____3259 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3264 = p_binder false b in
                   let uu____3265 =
                     let uu____3266 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3266 in
                   FStar_Pprint.op_Hat_Hat uu____3264 uu____3265) bs in
            let uu____3267 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3259 uu____3267 in
          FStar_Pprint.group uu____3258
      | uu____3268 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3270 =
      let uu____3271 = unparen e in uu____3271.FStar_Parser_AST.tm in
    match uu____3270 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3272;_},e1::e2::[])
        ->
        let uu____3276 = str "\\/" in
        let uu____3277 = p_tmFormula e1 in
        let uu____3278 = p_tmConjunction e2 in
        infix0 uu____3276 uu____3277 uu____3278
    | uu____3279 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3281 =
      let uu____3282 = unparen e in uu____3282.FStar_Parser_AST.tm in
    match uu____3281 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3283;_},e1::e2::[])
        ->
        let uu____3287 = str "/\\" in
        let uu____3288 = p_tmConjunction e1 in
        let uu____3289 = p_tmTuple e2 in
        infix0 uu____3287 uu____3288 uu____3289
    | uu____3290 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3293 =
      let uu____3294 = unparen e in uu____3294.FStar_Parser_AST.tm in
    match uu____3293 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3303 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3303
          (fun uu____3309  ->
             match uu____3309 with | (e1,uu____3313) -> p_tmEq e1) args
    | uu____3314 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3319 =
             let uu____3320 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3320 in
           FStar_Pprint.group uu____3319)
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
      let uu____3345 =
        let uu____3346 = unparen e in uu____3346.FStar_Parser_AST.tm in
      match uu____3345 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3352 = levels op1 in
          (match uu____3352 with
           | (left1,mine,right1) ->
               let uu____3359 =
                 let uu____3360 = FStar_All.pipe_left str op1 in
                 let uu____3361 = p_tmEq' left1 e1 in
                 let uu____3362 = p_tmEq' right1 e2 in
                 infix0 uu____3360 uu____3361 uu____3362 in
               paren_if curr mine uu____3359)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3363;_},e1::e2::[])
          ->
          let uu____3367 =
            let uu____3368 = p_tmEq e1 in
            let uu____3369 =
              let uu____3370 =
                let uu____3371 =
                  let uu____3372 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3372 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3371 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3370 in
            FStar_Pprint.op_Hat_Hat uu____3368 uu____3369 in
          FStar_Pprint.group uu____3367
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3373;_},e1::[])
          ->
          let uu____3376 = levels "-" in
          (match uu____3376 with
           | (left1,mine,right1) ->
               let uu____3383 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3383)
      | uu____3384 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3414 =
        let uu____3415 = unparen e in uu____3415.FStar_Parser_AST.tm in
      match uu____3414 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3418)::(e2,uu____3420)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3431 = is_list e in Prims.op_Negation uu____3431)
          ->
          let op = "::" in
          let uu____3433 = levels op in
          (match uu____3433 with
           | (left1,mine,right1) ->
               let uu____3440 =
                 let uu____3441 = str op in
                 let uu____3442 = p_tmNoEq' left1 e1 in
                 let uu____3443 = p_tmNoEq' right1 e2 in
                 infix0 uu____3441 uu____3442 uu____3443 in
               paren_if curr mine uu____3440)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3449 = levels op in
          (match uu____3449 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3460 = p_binder false b in
                 let uu____3461 =
                   let uu____3462 =
                     let uu____3463 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3463 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3462 in
                 FStar_Pprint.op_Hat_Hat uu____3460 uu____3461 in
               let uu____3464 =
                 let uu____3465 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3466 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3465 uu____3466 in
               paren_if curr mine uu____3464)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3472 = levels op1 in
          (match uu____3472 with
           | (left1,mine,right1) ->
               let uu____3479 =
                 let uu____3480 = str op1 in
                 let uu____3481 = p_tmNoEq' left1 e1 in
                 let uu____3482 = p_tmNoEq' right1 e2 in
                 infix0 uu____3480 uu____3481 uu____3482 in
               paren_if curr mine uu____3479)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3485 =
            let uu____3486 = p_lidentOrUnderscore lid in
            let uu____3487 =
              let uu____3488 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3488 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3486 uu____3487 in
          FStar_Pprint.group uu____3485
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3501 =
            let uu____3502 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3503 =
              let uu____3504 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3504 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3502 uu____3503 in
          braces_with_nesting uu____3501
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3507;_},e1::[])
          ->
          let uu____3510 =
            let uu____3511 = str "~" in
            let uu____3512 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3511 uu____3512 in
          FStar_Pprint.group uu____3510
      | uu____3513 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3515 = p_appTerm e in
    let uu____3516 =
      let uu____3517 =
        let uu____3518 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3518 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3517 in
    FStar_Pprint.op_Hat_Hat uu____3515 uu____3516
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3523 =
            let uu____3524 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3524 t phi in
          soft_parens_with_nesting uu____3523
      | FStar_Parser_AST.TAnnotated uu____3525 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3528 ->
          let uu____3529 =
            let uu____3530 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3530 in
          failwith uu____3529
      | FStar_Parser_AST.TVariable uu____3531 ->
          let uu____3532 =
            let uu____3533 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3533 in
          failwith uu____3532
      | FStar_Parser_AST.NoName uu____3534 ->
          let uu____3535 =
            let uu____3536 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3536 in
          failwith uu____3535
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____3537  ->
    match uu____3537 with
    | (lid,e) ->
        let uu____3542 =
          let uu____3543 = p_qlident lid in
          let uu____3544 =
            let uu____3545 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3545 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3543 uu____3544 in
        FStar_Pprint.group uu____3542
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3547 =
      let uu____3548 = unparen e in uu____3548.FStar_Parser_AST.tm in
    match uu____3547 with
    | FStar_Parser_AST.App uu____3549 when is_general_application e ->
        let uu____3553 = head_and_args e in
        (match uu____3553 with
         | (head1,args) ->
             let uu____3567 =
               let uu____3573 = FStar_ST.read should_print_fs_typ_app in
               if uu____3573
               then
                 let uu____3581 =
                   FStar_Util.take
                     (fun uu____3595  ->
                        match uu____3595 with
                        | (uu____3598,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3581 with
                 | (fs_typ_args,args1) ->
                     let uu____3619 =
                       let uu____3620 = p_indexingTerm head1 in
                       let uu____3621 =
                         let uu____3622 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3622 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3620 uu____3621 in
                     (uu____3619, args1)
               else
                 (let uu____3629 = p_indexingTerm head1 in (uu____3629, args)) in
             (match uu____3567 with
              | (head_doc,args1) ->
                  let uu____3641 =
                    let uu____3642 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3642 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3641))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____3654 = is_dtuple_constructor lid in
           Prims.op_Negation uu____3654)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3664 =
               let uu____3665 = p_quident lid in
               let uu____3666 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3665 uu____3666 in
             FStar_Pprint.group uu____3664
         | hd1::tl1 ->
             let uu____3676 =
               let uu____3677 =
                 let uu____3678 =
                   let uu____3679 = p_quident lid in
                   let uu____3680 = p_argTerm hd1 in
                   prefix2 uu____3679 uu____3680 in
                 FStar_Pprint.group uu____3678 in
               let uu____3681 =
                 let uu____3682 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3682 in
               FStar_Pprint.op_Hat_Hat uu____3677 uu____3681 in
             FStar_Pprint.group uu____3676)
    | uu____3685 -> p_indexingTerm e
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
         (let uu____3692 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3692 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3694 = str "#" in
        let uu____3695 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3694 uu____3695
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____3697  ->
    match uu____3697 with | (e,uu____3701) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3706 =
        let uu____3707 = unparen e in uu____3707.FStar_Parser_AST.tm in
      match uu____3706 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3708;_},e1::e2::[])
          ->
          let uu____3712 =
            let uu____3713 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3714 =
              let uu____3715 =
                let uu____3716 = p_term e2 in
                soft_parens_with_nesting uu____3716 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3715 in
            FStar_Pprint.op_Hat_Hat uu____3713 uu____3714 in
          FStar_Pprint.group uu____3712
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3717;_},e1::e2::[])
          ->
          let uu____3721 =
            let uu____3722 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3723 =
              let uu____3724 =
                let uu____3725 = p_term e2 in
                soft_brackets_with_nesting uu____3725 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3724 in
            FStar_Pprint.op_Hat_Hat uu____3722 uu____3723 in
          FStar_Pprint.group uu____3721
      | uu____3726 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3729 =
      let uu____3730 = unparen e in uu____3730.FStar_Parser_AST.tm in
    match uu____3729 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3733 = p_quident lid in
        let uu____3734 =
          let uu____3735 =
            let uu____3736 = p_term e1 in soft_parens_with_nesting uu____3736 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3735 in
        FStar_Pprint.op_Hat_Hat uu____3733 uu____3734
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3741 = str (FStar_Ident.text_of_id op) in
        let uu____3742 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3741 uu____3742
    | uu____3743 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3745 =
      let uu____3746 = unparen e in uu____3746.FStar_Parser_AST.tm in
    match uu____3745 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3751 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3757 = str (FStar_Ident.text_of_id op) in
        let uu____3758 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3757 uu____3758
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3761 =
          let uu____3762 =
            let uu____3763 = str (FStar_Ident.text_of_id op) in
            let uu____3764 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3763 uu____3764 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3762 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3761
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3773 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3774 =
          let uu____3775 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3776 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____3775 p_tmEq uu____3776 in
        let uu____3780 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3773 uu____3774 uu____3780
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3783 =
          let uu____3784 = p_atomicTermNotQUident e1 in
          let uu____3785 =
            let uu____3786 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3786 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3784 uu____3785 in
        FStar_Pprint.group uu____3783
    | uu____3787 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3789 =
      let uu____3790 = unparen e in uu____3790.FStar_Parser_AST.tm in
    match uu____3789 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3794 = p_quident constr_lid in
        let uu____3795 =
          let uu____3796 =
            let uu____3797 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3797 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3796 in
        FStar_Pprint.op_Hat_Hat uu____3794 uu____3795
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3799 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3799 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3801 = p_term e1 in soft_parens_with_nesting uu____3801
    | uu____3802 when is_array e ->
        let es = extract_from_list e in
        let uu____3805 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3806 =
          let uu____3807 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3807 p_noSeqTerm es in
        let uu____3808 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3805 uu____3806 uu____3808
    | uu____3809 when is_list e ->
        let uu____3810 =
          let uu____3811 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3812 = extract_from_list e in
          separate_map_or_flow uu____3811 p_noSeqTerm uu____3812 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3810 FStar_Pprint.rbracket
    | uu____3814 when is_lex_list e ->
        let uu____3815 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3816 =
          let uu____3817 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3818 = extract_from_list e in
          separate_map_or_flow uu____3817 p_noSeqTerm uu____3818 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3815 uu____3816 FStar_Pprint.rbracket
    | uu____3820 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3823 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3824 =
          let uu____3825 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3825 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3823 uu____3824 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3829 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____3830 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____3829 uu____3830
    | FStar_Parser_AST.Op (op,args) when
        let uu____3835 = handleable_op op args in
        Prims.op_Negation uu____3835 ->
        let uu____3836 =
          let uu____3837 =
            let uu____3838 =
              let uu____3839 =
                let uu____3840 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3840
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3839 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3838 in
          Prims.strcat "Operation " uu____3837 in
        failwith uu____3836
    | FStar_Parser_AST.Uvar uu____3847 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3848 = p_term e in soft_parens_with_nesting uu____3848
    | FStar_Parser_AST.Const uu____3849 ->
        let uu____3850 = p_term e in soft_parens_with_nesting uu____3850
    | FStar_Parser_AST.Op uu____3851 ->
        let uu____3855 = p_term e in soft_parens_with_nesting uu____3855
    | FStar_Parser_AST.Tvar uu____3856 ->
        let uu____3857 = p_term e in soft_parens_with_nesting uu____3857
    | FStar_Parser_AST.Var uu____3858 ->
        let uu____3859 = p_term e in soft_parens_with_nesting uu____3859
    | FStar_Parser_AST.Name uu____3860 ->
        let uu____3861 = p_term e in soft_parens_with_nesting uu____3861
    | FStar_Parser_AST.Construct uu____3862 ->
        let uu____3868 = p_term e in soft_parens_with_nesting uu____3868
    | FStar_Parser_AST.Abs uu____3869 ->
        let uu____3873 = p_term e in soft_parens_with_nesting uu____3873
    | FStar_Parser_AST.App uu____3874 ->
        let uu____3878 = p_term e in soft_parens_with_nesting uu____3878
    | FStar_Parser_AST.Let uu____3879 ->
        let uu____3886 = p_term e in soft_parens_with_nesting uu____3886
    | FStar_Parser_AST.LetOpen uu____3887 ->
        let uu____3890 = p_term e in soft_parens_with_nesting uu____3890
    | FStar_Parser_AST.Seq uu____3891 ->
        let uu____3894 = p_term e in soft_parens_with_nesting uu____3894
    | FStar_Parser_AST.Bind uu____3895 ->
        let uu____3899 = p_term e in soft_parens_with_nesting uu____3899
    | FStar_Parser_AST.If uu____3900 ->
        let uu____3904 = p_term e in soft_parens_with_nesting uu____3904
    | FStar_Parser_AST.Match uu____3905 ->
        let uu____3913 = p_term e in soft_parens_with_nesting uu____3913
    | FStar_Parser_AST.TryWith uu____3914 ->
        let uu____3922 = p_term e in soft_parens_with_nesting uu____3922
    | FStar_Parser_AST.Ascribed uu____3923 ->
        let uu____3928 = p_term e in soft_parens_with_nesting uu____3928
    | FStar_Parser_AST.Record uu____3929 ->
        let uu____3936 = p_term e in soft_parens_with_nesting uu____3936
    | FStar_Parser_AST.Project uu____3937 ->
        let uu____3940 = p_term e in soft_parens_with_nesting uu____3940
    | FStar_Parser_AST.Product uu____3941 ->
        let uu____3945 = p_term e in soft_parens_with_nesting uu____3945
    | FStar_Parser_AST.Sum uu____3946 ->
        let uu____3950 = p_term e in soft_parens_with_nesting uu____3950
    | FStar_Parser_AST.QForall uu____3951 ->
        let uu____3958 = p_term e in soft_parens_with_nesting uu____3958
    | FStar_Parser_AST.QExists uu____3959 ->
        let uu____3966 = p_term e in soft_parens_with_nesting uu____3966
    | FStar_Parser_AST.Refine uu____3967 ->
        let uu____3970 = p_term e in soft_parens_with_nesting uu____3970
    | FStar_Parser_AST.NamedTyp uu____3971 ->
        let uu____3974 = p_term e in soft_parens_with_nesting uu____3974
    | FStar_Parser_AST.Requires uu____3975 ->
        let uu____3979 = p_term e in soft_parens_with_nesting uu____3979
    | FStar_Parser_AST.Ensures uu____3980 ->
        let uu____3984 = p_term e in soft_parens_with_nesting uu____3984
    | FStar_Parser_AST.Assign uu____3985 ->
        let uu____3988 = p_term e in soft_parens_with_nesting uu____3988
    | FStar_Parser_AST.Attributes uu____3989 ->
        let uu____3991 = p_term e in soft_parens_with_nesting uu____3991
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___106_3992  ->
    match uu___106_3992 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____3996 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____3996
    | FStar_Const.Const_string (bytes,uu____3998) ->
        let uu____4001 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____4001
    | FStar_Const.Const_bytearray (bytes,uu____4003) ->
        let uu____4006 =
          let uu____4007 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____4007 in
        let uu____4008 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____4006 uu____4008
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_4020 =
          match uu___104_4020 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___105_4024 =
          match uu___105_4024 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____4033  ->
               match uu____4033 with
               | (s,w) ->
                   let uu____4038 = signedness s in
                   let uu____4039 = width w in
                   FStar_Pprint.op_Hat_Hat uu____4038 uu____4039)
            sign_width_opt in
        let uu____4040 = str repr in
        FStar_Pprint.op_Hat_Hat uu____4040 ending
    | FStar_Const.Const_range r ->
        let uu____4042 = FStar_Range.string_of_range r in str uu____4042
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____4044 = p_quident lid in
        let uu____4045 =
          let uu____4046 =
            let uu____4047 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4047 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____4046 in
        FStar_Pprint.op_Hat_Hat uu____4044 uu____4045
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4049 = str "u#" in
    let uu____4050 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____4049 uu____4050
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4052 =
      let uu____4053 = unparen u in uu____4053.FStar_Parser_AST.tm in
    match uu____4052 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4054;_},u1::u2::[])
        ->
        let uu____4058 =
          let uu____4059 = p_universeFrom u1 in
          let uu____4060 =
            let uu____4061 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____4061 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4059 uu____4060 in
        FStar_Pprint.group uu____4058
    | FStar_Parser_AST.App uu____4062 ->
        let uu____4066 = head_and_args u in
        (match uu____4066 with
         | (head1,args) ->
             let uu____4080 =
               let uu____4081 = unparen head1 in
               uu____4081.FStar_Parser_AST.tm in
             (match uu____4080 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____4083 =
                    let uu____4084 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____4085 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____4091  ->
                           match uu____4091 with
                           | (u1,uu____4095) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____4084 uu____4085 in
                  FStar_Pprint.group uu____4083
              | uu____4096 ->
                  let uu____4097 =
                    let uu____4098 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____4098 in
                  failwith uu____4097))
    | uu____4099 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4101 =
      let uu____4102 = unparen u in uu____4102.FStar_Parser_AST.tm in
    match uu____4101 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____4116 = p_universeFrom u1 in
        soft_parens_with_nesting uu____4116
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4117;_},uu____4118::uu____4119::[])
        ->
        let uu____4121 = p_universeFrom u in
        soft_parens_with_nesting uu____4121
    | FStar_Parser_AST.App uu____4122 ->
        let uu____4126 = p_universeFrom u in
        soft_parens_with_nesting uu____4126
    | uu____4127 ->
        let uu____4128 =
          let uu____4129 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____4129 in
        failwith uu____4128
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
       | FStar_Parser_AST.Module (uu____4154,decls) ->
           let uu____4158 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4158
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____4163,decls,uu____4165) ->
           let uu____4168 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4168
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4191  ->
         match uu____4191 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____4218,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4222,decls,uu____4224) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4241 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4248;
                 FStar_Parser_AST.doc = uu____4249;
                 FStar_Parser_AST.quals = uu____4250;
                 FStar_Parser_AST.attrs = uu____4251;_}::uu____4252 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4256 =
                   let uu____4258 =
                     let uu____4260 = FStar_List.tl ds in d :: uu____4260 in
                   d0 :: uu____4258 in
                 (uu____4256, (d0.FStar_Parser_AST.drange))
             | uu____4263 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4241 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4286 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4286 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4308 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4308, comments1))))))