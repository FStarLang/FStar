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
    let uu____2001 =
      let uu____2002 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____2003 =
        let uu____2004 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____2005 =
          let uu____2006 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____2007 =
            let uu____2008 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____2008 in
          FStar_Pprint.op_Hat_Hat uu____2006 uu____2007 in
        FStar_Pprint.op_Hat_Hat uu____2004 uu____2005 in
      FStar_Pprint.op_Hat_Hat uu____2002 uu____2003 in
    FStar_Pprint.group uu____2001
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____2011 =
      let uu____2012 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____2012 in
    let uu____2013 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____2011 FStar_Pprint.space uu____2013
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____2014  ->
    match uu____2014 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____2035 =
                match uu____2035 with
                | (kwd1,arg) ->
                    let uu____2040 = str "@" in
                    let uu____2041 =
                      let uu____2042 = str kwd1 in
                      let uu____2043 =
                        let uu____2044 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2044 in
                      FStar_Pprint.op_Hat_Hat uu____2042 uu____2043 in
                    FStar_Pprint.op_Hat_Hat uu____2040 uu____2041 in
              let uu____2045 =
                let uu____2046 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____2046 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2045 in
        let uu____2049 =
          let uu____2050 =
            let uu____2051 =
              let uu____2052 =
                let uu____2053 = str doc1 in
                let uu____2054 =
                  let uu____2055 =
                    let uu____2056 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2056 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2055 in
                FStar_Pprint.op_Hat_Hat uu____2053 uu____2054 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2052 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2051 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2050 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2049
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____2059 =
          let uu____2060 = str "open" in
          let uu____2061 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2060 uu____2061 in
        FStar_Pprint.group uu____2059
    | FStar_Parser_AST.Include uid ->
        let uu____2063 =
          let uu____2064 = str "include" in
          let uu____2065 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____2064 uu____2065 in
        FStar_Pprint.group uu____2063
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____2068 =
          let uu____2069 = str "module" in
          let uu____2070 =
            let uu____2071 =
              let uu____2072 = p_uident uid1 in
              let uu____2073 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2072 uu____2073 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2071 in
          FStar_Pprint.op_Hat_Hat uu____2069 uu____2070 in
        let uu____2074 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____2068 uu____2074
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____2076 =
          let uu____2077 = str "module" in
          let uu____2078 =
            let uu____2079 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2079 in
          FStar_Pprint.op_Hat_Hat uu____2077 uu____2078 in
        FStar_Pprint.group uu____2076
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____2098 = str "effect" in
          let uu____2099 =
            let uu____2100 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2100 in
          FStar_Pprint.op_Hat_Hat uu____2098 uu____2099 in
        let uu____2101 =
          let uu____2102 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____2102 FStar_Pprint.equals in
        let uu____2103 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2101 uu____2103
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____2113 = str "type" in
        let uu____2114 = str "and" in
        precede_break_separate_map uu____2113 uu____2114 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____2127 = str "let" in
          let uu____2128 =
            let uu____2129 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____2129 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____2127 uu____2128 in
        let uu____2130 =
          let uu____2131 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____2131 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____2130 p_letbinding lbs
          (fun uu____2137  ->
             match uu____2137 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____2144 =
          let uu____2145 = str "val" in
          let uu____2146 =
            let uu____2147 =
              let uu____2148 = p_lident lid in
              let uu____2149 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____2148 uu____2149 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2147 in
          FStar_Pprint.op_Hat_Hat uu____2145 uu____2146 in
        let uu____2150 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2144 uu____2150
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____2154 =
            let uu____2155 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____2155 FStar_Util.is_upper in
          if uu____2154
          then FStar_Pprint.empty
          else
            (let uu____2157 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____2157 FStar_Pprint.space) in
        let uu____2158 =
          let uu____2159 =
            let uu____2160 = p_ident id in
            let uu____2161 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____2160 uu____2161 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____2159 in
        let uu____2162 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____2158 uu____2162
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____2167 = str "exception" in
        let uu____2168 =
          let uu____2169 =
            let uu____2170 = p_uident uid in
            let uu____2171 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____2176 = str "of" in
                   let uu____2177 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____2176 uu____2177) t_opt in
            FStar_Pprint.op_Hat_Hat uu____2170 uu____2171 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2169 in
        FStar_Pprint.op_Hat_Hat uu____2167 uu____2168
    | FStar_Parser_AST.NewEffect ne ->
        let uu____2179 = str "new_effect" in
        let uu____2180 =
          let uu____2181 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2181 in
        FStar_Pprint.op_Hat_Hat uu____2179 uu____2180
    | FStar_Parser_AST.SubEffect se ->
        let uu____2183 = str "sub_effect" in
        let uu____2184 =
          let uu____2185 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2185 in
        FStar_Pprint.op_Hat_Hat uu____2183 uu____2184
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____2188 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____2188 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____2189 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____2190) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___96_2199  ->
    match uu___96_2199 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____2201 = str "#set-options" in
        let uu____2202 =
          let uu____2203 =
            let uu____2204 = str s in FStar_Pprint.dquotes uu____2204 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2203 in
        FStar_Pprint.op_Hat_Hat uu____2201 uu____2202
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____2207 = str "#reset-options" in
        let uu____2208 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____2212 =
                 let uu____2213 = str s in FStar_Pprint.dquotes uu____2213 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2212) s_opt in
        FStar_Pprint.op_Hat_Hat uu____2207 uu____2208
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2219  ->
    match uu____2219 with
    | (typedecl,fsdoc_opt) ->
        let uu____2227 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____2228 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____2227 uu____2228
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___97_2229  ->
    match uu___97_2229 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____2240 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____2252 =
          let uu____2253 = p_typ t in prefix2 FStar_Pprint.equals uu____2253 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____2279 =
          match uu____2279 with
          | (lid1,t,doc_opt) ->
              let uu____2289 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____2289 in
        let p_fields uu____2298 =
          let uu____2299 =
            let uu____2300 =
              let uu____2301 =
                let uu____2302 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____2302 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____2301 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2300 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____2299 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____2338 =
          match uu____2338 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____2354 =
                  let uu____2355 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____2355 in
                FStar_Range.extend_to_end_of_line uu____2354 in
              let p_constructorBranch decl =
                let uu____2375 =
                  let uu____2376 =
                    let uu____2377 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2377 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____2376 in
                FStar_Pprint.group uu____2375 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____2389 =
          let uu____2390 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____2390 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____2399  ->
             let uu____2400 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____2400)
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
            let uu____2411 = p_ident lid in
            let uu____2412 =
              let uu____2413 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2413 in
            FStar_Pprint.op_Hat_Hat uu____2411 uu____2412
          else
            (let binders_doc =
               let uu____2416 = p_typars bs in
               let uu____2417 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____2421 =
                        let uu____2422 =
                          let uu____2423 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____2423 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2422 in
                      FStar_Pprint.op_Hat_Hat break1 uu____2421) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____2416 uu____2417 in
             let uu____2424 = p_ident lid in
             let uu____2425 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____2424 binders_doc uu____2425)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____2426  ->
    match uu____2426 with
    | (lid,t,doc_opt) ->
        let uu____2436 =
          let uu____2437 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____2438 =
            let uu____2439 = p_lident lid in
            let uu____2440 =
              let uu____2441 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2441 in
            FStar_Pprint.op_Hat_Hat uu____2439 uu____2440 in
          FStar_Pprint.op_Hat_Hat uu____2437 uu____2438 in
        FStar_Pprint.group uu____2436
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____2442  ->
    match uu____2442 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____2460 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____2461 =
          let uu____2462 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____2463 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____2468 =
                   let uu____2469 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____2469 in
                 let uu____2470 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____2468 uu____2470) t_opt in
          FStar_Pprint.op_Hat_Hat uu____2462 uu____2463 in
        FStar_Pprint.op_Hat_Hat uu____2460 uu____2461
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____2471  ->
    match uu____2471 with
    | (pat,e) ->
        let pat_doc =
          let uu____2477 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____2484 =
                  let uu____2485 =
                    let uu____2486 =
                      let uu____2487 =
                        let uu____2488 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2488 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2487 in
                    FStar_Pprint.group uu____2486 in
                  FStar_Pprint.op_Hat_Hat break1 uu____2485 in
                (pat1, uu____2484)
            | uu____2489 -> (pat, FStar_Pprint.empty) in
          match uu____2477 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____2493);
                      FStar_Parser_AST.prange = uu____2494;_},pats)
                   ->
                   let uu____2500 = p_lident x in
                   let uu____2501 =
                     let uu____2502 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____2502 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____2500 uu____2501
                     FStar_Pprint.equals
               | uu____2503 ->
                   let uu____2504 =
                     let uu____2505 = p_tuplePattern pat1 in
                     let uu____2506 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____2505 uu____2506 in
                   FStar_Pprint.group uu____2504) in
        let uu____2507 = p_term e in prefix2 pat_doc uu____2507
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___98_2508  ->
    match uu___98_2508 with
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
        let uu____2526 = p_uident uid in
        let uu____2527 = p_binders true bs in
        let uu____2528 =
          let uu____2529 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____2529 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2526 uu____2527 uu____2528
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
          let uu____2536 =
            let uu____2537 =
              let uu____2538 =
                let uu____2539 = p_uident uid in
                let uu____2540 = p_binders true bs in
                let uu____2541 =
                  let uu____2542 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____2542 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____2539 uu____2540 uu____2541 in
              FStar_Pprint.group uu____2538 in
            let uu____2543 =
              let uu____2544 = str "with" in
              let uu____2545 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____2544 uu____2545 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2537 uu____2543 in
          braces_with_nesting uu____2536
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____2562 =
          let uu____2563 = p_lident lid in
          let uu____2564 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____2563 uu____2564 in
        let uu____2565 = p_simpleTerm e in prefix2 uu____2562 uu____2565
    | uu____2566 ->
        let uu____2567 =
          let uu____2568 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____2568 in
        failwith uu____2567
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____2601 =
        match uu____2601 with
        | (kwd1,t) ->
            let uu____2606 =
              let uu____2607 = str kwd1 in
              let uu____2608 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____2607 uu____2608 in
            let uu____2609 = p_simpleTerm t in prefix2 uu____2606 uu____2609 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____2612 =
      let uu____2613 =
        let uu____2614 = p_quident lift.FStar_Parser_AST.msource in
        let uu____2615 =
          let uu____2616 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2616 in
        FStar_Pprint.op_Hat_Hat uu____2614 uu____2615 in
      let uu____2617 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____2613 uu____2617 in
    let uu____2618 =
      let uu____2619 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2619 in
    FStar_Pprint.op_Hat_Hat uu____2612 uu____2618
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___99_2620  ->
    match uu___99_2620 with
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
    let uu____2622 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____2622
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___100_2623  ->
    match uu___100_2623 with
    | FStar_Parser_AST.Rec  ->
        let uu____2624 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2624
    | FStar_Parser_AST.Mutable  ->
        let uu____2625 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2625
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___101_2626  ->
    match uu___101_2626 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____2630 =
          let uu____2631 =
            let uu____2632 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____2632 in
          FStar_Pprint.separate_map uu____2631 p_tuplePattern pats in
        FStar_Pprint.group uu____2630
    | uu____2633 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____2638 =
          let uu____2639 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____2639 p_constructorPattern pats in
        FStar_Pprint.group uu____2638
    | uu____2640 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____2643;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____2647 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____2648 = p_constructorPattern hd1 in
        let uu____2649 = p_constructorPattern tl1 in
        infix0 uu____2647 uu____2648 uu____2649
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____2651;_},pats)
        ->
        let uu____2655 = p_quident uid in
        let uu____2656 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____2655 uu____2656
    | uu____2657 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____2661 =
          let uu____2664 =
            let uu____2665 = unparen t in uu____2665.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____2664) in
        (match uu____2661 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____2670;
               FStar_Parser_AST.blevel = uu____2671;
               FStar_Parser_AST.aqual = uu____2672;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____2676 =
               let uu____2677 = p_ident lid in
               p_refinement aqual uu____2677 t1 phi in
             soft_parens_with_nesting uu____2676
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____2679;
               FStar_Parser_AST.blevel = uu____2680;
               FStar_Parser_AST.aqual = uu____2681;_},phi))
             ->
             let uu____2683 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____2683
         | uu____2684 ->
             let uu____2687 =
               let uu____2688 = p_tuplePattern pat in
               let uu____2689 =
                 let uu____2690 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____2691 =
                   let uu____2692 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2692 in
                 FStar_Pprint.op_Hat_Hat uu____2690 uu____2691 in
               FStar_Pprint.op_Hat_Hat uu____2688 uu____2689 in
             soft_parens_with_nesting uu____2687)
    | FStar_Parser_AST.PatList pats ->
        let uu____2695 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____2695 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____2705 =
          match uu____2705 with
          | (lid,pat) ->
              let uu____2710 = p_qlident lid in
              let uu____2711 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____2710 uu____2711 in
        let uu____2712 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____2712
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____2718 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____2719 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____2720 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____2718 uu____2719 uu____2720
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____2728 =
          let uu____2729 =
            let uu____2730 = str (FStar_Ident.text_of_id op) in
            let uu____2731 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____2730 uu____2731 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2729 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2728
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____2737 = FStar_Pprint.optional p_aqual aqual in
        let uu____2738 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____2737 uu____2738
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____2740 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____2742;
           FStar_Parser_AST.prange = uu____2743;_},uu____2744)
        ->
        let uu____2747 = p_tuplePattern p in
        soft_parens_with_nesting uu____2747
    | FStar_Parser_AST.PatTuple (uu____2748,false ) ->
        let uu____2751 = p_tuplePattern p in
        soft_parens_with_nesting uu____2751
    | uu____2752 ->
        let uu____2753 =
          let uu____2754 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____2754 in
        failwith uu____2753
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____2758 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____2759 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____2758 uu____2759
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____2764 =
              let uu____2765 = unparen t in uu____2765.FStar_Parser_AST.tm in
            match uu____2764 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____2768;
                   FStar_Parser_AST.blevel = uu____2769;
                   FStar_Parser_AST.aqual = uu____2770;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____2772 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____2772 t1 phi
            | uu____2773 ->
                let uu____2774 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____2775 =
                  let uu____2776 = p_lident lid in
                  let uu____2777 =
                    let uu____2778 =
                      let uu____2779 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____2780 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____2779 uu____2780 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2778 in
                  FStar_Pprint.op_Hat_Hat uu____2776 uu____2777 in
                FStar_Pprint.op_Hat_Hat uu____2774 uu____2775 in
          if is_atomic
          then
            let uu____2781 =
              let uu____2782 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2782 in
            FStar_Pprint.group uu____2781
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____2784 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____2788 =
            let uu____2789 = unparen t in uu____2789.FStar_Parser_AST.tm in
          (match uu____2788 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____2791;
                  FStar_Parser_AST.blevel = uu____2792;
                  FStar_Parser_AST.aqual = uu____2793;_},phi)
               ->
               if is_atomic
               then
                 let uu____2795 =
                   let uu____2796 =
                     let uu____2797 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____2797 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2796 in
                 FStar_Pprint.group uu____2795
               else
                 (let uu____2799 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____2799)
           | uu____2800 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____2807 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____2808 =
            let uu____2809 =
              let uu____2810 =
                let uu____2811 = p_appTerm t in
                let uu____2812 =
                  let uu____2813 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____2813 in
                FStar_Pprint.op_Hat_Hat uu____2811 uu____2812 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____2810 in
            FStar_Pprint.op_Hat_Hat binder uu____2809 in
          FStar_Pprint.op_Hat_Hat uu____2807 uu____2808
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
    let uu____2826 =
      let uu____2827 = unparen e in uu____2827.FStar_Parser_AST.tm in
    match uu____2826 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____2830 =
          let uu____2831 =
            let uu____2832 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____2832 FStar_Pprint.semi in
          FStar_Pprint.group uu____2831 in
        let uu____2833 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2830 uu____2833
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____2837 =
          let uu____2838 =
            let uu____2839 =
              let uu____2840 = p_lident x in
              let uu____2841 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____2840 uu____2841 in
            let uu____2842 =
              let uu____2843 = p_noSeqTerm e1 in
              let uu____2844 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____2843 uu____2844 in
            op_Hat_Slash_Plus_Hat uu____2839 uu____2842 in
          FStar_Pprint.group uu____2838 in
        let uu____2845 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____2837 uu____2845
    | uu____2846 ->
        let uu____2847 = p_noSeqTerm e in FStar_Pprint.group uu____2847
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____2850 =
      let uu____2851 = unparen e in uu____2851.FStar_Parser_AST.tm in
    match uu____2850 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____2855 =
          let uu____2856 = p_tmIff e1 in
          let uu____2857 =
            let uu____2858 =
              let uu____2859 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2859 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2858 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2856 uu____2857 in
        FStar_Pprint.group uu____2855
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____2864 =
          let uu____2865 = p_tmIff e1 in
          let uu____2866 =
            let uu____2867 =
              let uu____2868 =
                let uu____2869 = p_typ t in
                let uu____2870 =
                  let uu____2871 = str "by" in
                  let uu____2872 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____2871 uu____2872 in
                FStar_Pprint.op_Hat_Slash_Hat uu____2869 uu____2870 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____2868 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____2867 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2865 uu____2866 in
        FStar_Pprint.group uu____2864
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____2873;_},e1::e2::e3::[])
        ->
        let uu____2878 =
          let uu____2879 =
            let uu____2880 =
              let uu____2881 = p_atomicTermNotQUident e1 in
              let uu____2882 =
                let uu____2883 =
                  let uu____2884 =
                    let uu____2885 = p_term e2 in
                    soft_parens_with_nesting uu____2885 in
                  let uu____2886 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2884 uu____2886 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2883 in
              FStar_Pprint.op_Hat_Hat uu____2881 uu____2882 in
            FStar_Pprint.group uu____2880 in
          let uu____2887 =
            let uu____2888 = p_noSeqTerm e3 in jump2 uu____2888 in
          FStar_Pprint.op_Hat_Hat uu____2879 uu____2887 in
        FStar_Pprint.group uu____2878
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____2889;_},e1::e2::e3::[])
        ->
        let uu____2894 =
          let uu____2895 =
            let uu____2896 =
              let uu____2897 = p_atomicTermNotQUident e1 in
              let uu____2898 =
                let uu____2899 =
                  let uu____2900 =
                    let uu____2901 = p_term e2 in
                    soft_brackets_with_nesting uu____2901 in
                  let uu____2902 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____2900 uu____2902 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____2899 in
              FStar_Pprint.op_Hat_Hat uu____2897 uu____2898 in
            FStar_Pprint.group uu____2896 in
          let uu____2903 =
            let uu____2904 = p_noSeqTerm e3 in jump2 uu____2904 in
          FStar_Pprint.op_Hat_Hat uu____2895 uu____2903 in
        FStar_Pprint.group uu____2894
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____2911 =
          let uu____2912 = str "requires" in
          let uu____2913 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2912 uu____2913 in
        FStar_Pprint.group uu____2911
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____2920 =
          let uu____2921 = str "ensures" in
          let uu____2922 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2921 uu____2922 in
        FStar_Pprint.group uu____2920
    | FStar_Parser_AST.Attributes es ->
        let uu____2925 =
          let uu____2926 = str "attributes" in
          let uu____2927 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____2926 uu____2927 in
        FStar_Pprint.group uu____2925
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____2931 = is_unit e3 in
        if uu____2931
        then
          let uu____2932 =
            let uu____2933 =
              let uu____2934 = str "if" in
              let uu____2935 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____2934 uu____2935 in
            let uu____2936 =
              let uu____2937 = str "then" in
              let uu____2938 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____2937 uu____2938 in
            FStar_Pprint.op_Hat_Slash_Hat uu____2933 uu____2936 in
          FStar_Pprint.group uu____2932
        else
          (let e2_doc =
             let uu____2941 =
               let uu____2942 = unparen e2 in uu____2942.FStar_Parser_AST.tm in
             match uu____2941 with
             | FStar_Parser_AST.If (uu____2943,uu____2944,e31) when
                 is_unit e31 ->
                 let uu____2946 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____2946
             | uu____2947 -> p_noSeqTerm e2 in
           let uu____2948 =
             let uu____2949 =
               let uu____2950 = str "if" in
               let uu____2951 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____2950 uu____2951 in
             let uu____2952 =
               let uu____2953 =
                 let uu____2954 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____2954 e2_doc in
               let uu____2955 =
                 let uu____2956 = str "else" in
                 let uu____2957 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____2956 uu____2957 in
               FStar_Pprint.op_Hat_Slash_Hat uu____2953 uu____2955 in
             FStar_Pprint.op_Hat_Slash_Hat uu____2949 uu____2952 in
           FStar_Pprint.group uu____2948)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____2970 =
          let uu____2971 =
            let uu____2972 = str "try" in
            let uu____2973 = p_noSeqTerm e1 in prefix2 uu____2972 uu____2973 in
          let uu____2974 =
            let uu____2975 = str "with" in
            let uu____2976 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____2975 uu____2976 in
          FStar_Pprint.op_Hat_Slash_Hat uu____2971 uu____2974 in
        FStar_Pprint.group uu____2970
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____2993 =
          let uu____2994 =
            let uu____2995 = str "match" in
            let uu____2996 = p_noSeqTerm e1 in
            let uu____2997 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____2995 uu____2996 uu____2997 in
          let uu____2998 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____2994 uu____2998 in
        FStar_Pprint.group uu____2993
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____3005 =
          let uu____3006 =
            let uu____3007 = str "let open" in
            let uu____3008 = p_quident uid in
            let uu____3009 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____3007 uu____3008 uu____3009 in
          let uu____3010 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3006 uu____3010 in
        FStar_Pprint.group uu____3005
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____3021 = str "let" in
          let uu____3022 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____3021 uu____3022 in
        let uu____3023 =
          let uu____3024 =
            let uu____3025 =
              let uu____3026 = str "and" in
              precede_break_separate_map let_doc uu____3026 p_letbinding lbs in
            let uu____3029 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____3025 uu____3029 in
          FStar_Pprint.group uu____3024 in
        let uu____3030 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____3023 uu____3030
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____3033;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____3036;
                                                         FStar_Parser_AST.level
                                                           = uu____3037;_})
        when matches_var maybe_x x ->
        let uu____3051 =
          let uu____3052 = str "function" in
          let uu____3053 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____3052 uu____3053 in
        FStar_Pprint.group uu____3051
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____3060 =
          let uu____3061 = p_lident id in
          let uu____3062 =
            let uu____3063 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____3063 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3061 uu____3062 in
        FStar_Pprint.group uu____3060
    | uu____3064 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3067 =
      let uu____3068 = unparen e in uu____3068.FStar_Parser_AST.tm in
    match uu____3067 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____3078 =
          let uu____3079 =
            let uu____3080 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____3080 FStar_Pprint.space in
          let uu____3081 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3079 uu____3081 FStar_Pprint.dot in
        let uu____3082 =
          let uu____3083 = p_trigger trigger in
          let uu____3084 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____3083 uu____3084 in
        prefix2 uu____3078 uu____3082
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____3094 =
          let uu____3095 =
            let uu____3096 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____3096 FStar_Pprint.space in
          let uu____3097 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____3095 uu____3097 FStar_Pprint.dot in
        let uu____3098 =
          let uu____3099 = p_trigger trigger in
          let uu____3100 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____3099 uu____3100 in
        prefix2 uu____3094 uu____3098
    | uu____3101 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3103 =
      let uu____3104 = unparen e in uu____3104.FStar_Parser_AST.tm in
    match uu____3103 with
    | FStar_Parser_AST.QForall uu____3105 -> str "forall"
    | FStar_Parser_AST.QExists uu____3112 -> str "exists"
    | uu____3119 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___102_3120  ->
    match uu___102_3120 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____3127 =
          let uu____3128 =
            let uu____3129 = str "pattern" in
            let uu____3130 =
              let uu____3131 =
                let uu____3132 = p_disjunctivePats pats in jump2 uu____3132 in
              let uu____3133 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____3131 uu____3133 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3129 uu____3130 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3128 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____3127
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3137 = str "\\/" in
    FStar_Pprint.separate_map uu____3137 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____3141 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____3141
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3143 =
      let uu____3144 = unparen e in uu____3144.FStar_Parser_AST.tm in
    match uu____3143 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____3149 =
          let uu____3150 = str "fun" in
          let uu____3151 =
            let uu____3152 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____3152 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____3150 uu____3151 in
        let uu____3153 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____3149 uu____3153
    | uu____3154 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3157  ->
    match uu____3157 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____3170 =
            let uu____3171 = unparen e in uu____3171.FStar_Parser_AST.tm in
          match uu____3170 with
          | FStar_Parser_AST.Match uu____3174 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____3182 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____3191);
                 FStar_Parser_AST.prange = uu____3192;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____3194);
                                                               FStar_Parser_AST.range
                                                                 = uu____3195;
                                                               FStar_Parser_AST.level
                                                                 = uu____3196;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____3210 -> (fun x  -> x) in
        let uu____3212 =
          let uu____3213 =
            let uu____3214 =
              let uu____3215 =
                let uu____3216 =
                  let uu____3217 = p_disjunctivePattern pat in
                  let uu____3218 =
                    let uu____3219 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____3219 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____3217 uu____3218 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3216 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3215 in
            FStar_Pprint.group uu____3214 in
          let uu____3220 =
            let uu____3221 = p_term e in maybe_paren uu____3221 in
          op_Hat_Slash_Plus_Hat uu____3213 uu____3220 in
        FStar_Pprint.group uu____3212
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___103_3222  ->
    match uu___103_3222 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____3225 = str "when" in
        let uu____3226 =
          let uu____3227 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____3227 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____3225 uu____3226
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3229 =
      let uu____3230 = unparen e in uu____3230.FStar_Parser_AST.tm in
    match uu____3229 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____3231;_},e1::e2::[])
        ->
        let uu____3235 = str "<==>" in
        let uu____3236 = p_tmImplies e1 in
        let uu____3237 = p_tmIff e2 in
        infix0 uu____3235 uu____3236 uu____3237
    | uu____3238 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3240 =
      let uu____3241 = unparen e in uu____3241.FStar_Parser_AST.tm in
    match uu____3240 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____3242;_},e1::e2::[])
        ->
        let uu____3246 = str "==>" in
        let uu____3247 = p_tmArrow p_tmFormula e1 in
        let uu____3248 = p_tmImplies e2 in
        infix0 uu____3246 uu____3247 uu____3248
    | uu____3249 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____3254 =
        let uu____3255 = unparen e in uu____3255.FStar_Parser_AST.tm in
      match uu____3254 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3260 =
            let uu____3261 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____3266 = p_binder false b in
                   let uu____3267 =
                     let uu____3268 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3268 in
                   FStar_Pprint.op_Hat_Hat uu____3266 uu____3267) bs in
            let uu____3269 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____3261 uu____3269 in
          FStar_Pprint.group uu____3260
      | uu____3270 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3272 =
      let uu____3273 = unparen e in uu____3273.FStar_Parser_AST.tm in
    match uu____3272 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____3274;_},e1::e2::[])
        ->
        let uu____3278 = str "\\/" in
        let uu____3279 = p_tmFormula e1 in
        let uu____3280 = p_tmConjunction e2 in
        infix0 uu____3278 uu____3279 uu____3280
    | uu____3281 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3283 =
      let uu____3284 = unparen e in uu____3284.FStar_Parser_AST.tm in
    match uu____3283 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____3285;_},e1::e2::[])
        ->
        let uu____3289 = str "/\\" in
        let uu____3290 = p_tmConjunction e1 in
        let uu____3291 = p_tmTuple e2 in
        infix0 uu____3289 uu____3290 uu____3291
    | uu____3292 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3295 =
      let uu____3296 = unparen e in uu____3296.FStar_Parser_AST.tm in
    match uu____3295 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____3305 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____3305
          (fun uu____3311  ->
             match uu____3311 with | (e1,uu____3315) -> p_tmEq e1) args
    | uu____3316 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____3321 =
             let uu____3322 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3322 in
           FStar_Pprint.group uu____3321)
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
      let uu____3347 =
        let uu____3348 = unparen e in uu____3348.FStar_Parser_AST.tm in
      match uu____3347 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3354 = levels op1 in
          (match uu____3354 with
           | (left1,mine,right1) ->
               let uu____3361 =
                 let uu____3362 = FStar_All.pipe_left str op1 in
                 let uu____3363 = p_tmEq' left1 e1 in
                 let uu____3364 = p_tmEq' right1 e2 in
                 infix0 uu____3362 uu____3363 uu____3364 in
               paren_if curr mine uu____3361)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____3365;_},e1::e2::[])
          ->
          let uu____3369 =
            let uu____3370 = p_tmEq e1 in
            let uu____3371 =
              let uu____3372 =
                let uu____3373 =
                  let uu____3374 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____3374 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3373 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3372 in
            FStar_Pprint.op_Hat_Hat uu____3370 uu____3371 in
          FStar_Pprint.group uu____3369
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____3375;_},e1::[])
          ->
          let uu____3378 = levels "-" in
          (match uu____3378 with
           | (left1,mine,right1) ->
               let uu____3385 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____3385)
      | uu____3386 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____3416 =
        let uu____3417 = unparen e in uu____3417.FStar_Parser_AST.tm in
      match uu____3416 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____3420)::(e2,uu____3422)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____3433 = is_list e in Prims.op_Negation uu____3433)
          ->
          let op = "::" in
          let uu____3435 = levels op in
          (match uu____3435 with
           | (left1,mine,right1) ->
               let uu____3442 =
                 let uu____3443 = str op in
                 let uu____3444 = p_tmNoEq' left1 e1 in
                 let uu____3445 = p_tmNoEq' right1 e2 in
                 infix0 uu____3443 uu____3444 uu____3445 in
               paren_if curr mine uu____3442)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____3451 = levels op in
          (match uu____3451 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____3462 = p_binder false b in
                 let uu____3463 =
                   let uu____3464 =
                     let uu____3465 = str op in
                     FStar_Pprint.op_Hat_Hat uu____3465 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3464 in
                 FStar_Pprint.op_Hat_Hat uu____3462 uu____3463 in
               let uu____3466 =
                 let uu____3467 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____3468 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____3467 uu____3468 in
               paren_if curr mine uu____3466)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____3474 = levels op1 in
          (match uu____3474 with
           | (left1,mine,right1) ->
               let uu____3481 =
                 let uu____3482 = str op1 in
                 let uu____3483 = p_tmNoEq' left1 e1 in
                 let uu____3484 = p_tmNoEq' right1 e2 in
                 infix0 uu____3482 uu____3483 uu____3484 in
               paren_if curr mine uu____3481)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____3487 =
            let uu____3488 = p_lidentOrUnderscore lid in
            let uu____3489 =
              let uu____3490 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3490 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3488 uu____3489 in
          FStar_Pprint.group uu____3487
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____3503 =
            let uu____3504 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____3505 =
              let uu____3506 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____3506 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____3504 uu____3505 in
          braces_with_nesting uu____3503
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____3509;_},e1::[])
          ->
          let uu____3512 =
            let uu____3513 = str "~" in
            let uu____3514 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____3513 uu____3514 in
          FStar_Pprint.group uu____3512
      | uu____3515 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3517 = p_appTerm e in
    let uu____3518 =
      let uu____3519 =
        let uu____3520 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____3520 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3519 in
    FStar_Pprint.op_Hat_Hat uu____3517 uu____3518
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____3525 =
            let uu____3526 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____3526 t phi in
          soft_parens_with_nesting uu____3525
      | FStar_Parser_AST.TAnnotated uu____3527 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____3530 ->
          let uu____3531 =
            let uu____3532 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3532 in
          failwith uu____3531
      | FStar_Parser_AST.TVariable uu____3533 ->
          let uu____3534 =
            let uu____3535 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3535 in
          failwith uu____3534
      | FStar_Parser_AST.NoName uu____3536 ->
          let uu____3537 =
            let uu____3538 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____3538 in
          failwith uu____3537
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____3539  ->
    match uu____3539 with
    | (lid,e) ->
        let uu____3544 =
          let uu____3545 = p_qlident lid in
          let uu____3546 =
            let uu____3547 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____3547 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3545 uu____3546 in
        FStar_Pprint.group uu____3544
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3549 =
      let uu____3550 = unparen e in uu____3550.FStar_Parser_AST.tm in
    match uu____3549 with
    | FStar_Parser_AST.App uu____3551 when is_general_application e ->
        let uu____3555 = head_and_args e in
        (match uu____3555 with
         | (head1,args) ->
             let uu____3569 =
               let uu____3575 = FStar_ST.read should_print_fs_typ_app in
               if uu____3575
               then
                 let uu____3583 =
                   FStar_Util.take
                     (fun uu____3597  ->
                        match uu____3597 with
                        | (uu____3600,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____3583 with
                 | (fs_typ_args,args1) ->
                     let uu____3621 =
                       let uu____3622 = p_indexingTerm head1 in
                       let uu____3623 =
                         let uu____3624 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____3624 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____3622 uu____3623 in
                     (uu____3621, args1)
               else
                 (let uu____3631 = p_indexingTerm head1 in (uu____3631, args)) in
             (match uu____3569 with
              | (head_doc,args1) ->
                  let uu____3643 =
                    let uu____3644 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____3644 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____3643))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____3656 = is_dtuple_constructor lid in
           Prims.op_Negation uu____3656)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____3666 =
               let uu____3667 = p_quident lid in
               let uu____3668 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____3667 uu____3668 in
             FStar_Pprint.group uu____3666
         | hd1::tl1 ->
             let uu____3678 =
               let uu____3679 =
                 let uu____3680 =
                   let uu____3681 = p_quident lid in
                   let uu____3682 = p_argTerm hd1 in
                   prefix2 uu____3681 uu____3682 in
                 FStar_Pprint.group uu____3680 in
               let uu____3683 =
                 let uu____3684 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____3684 in
               FStar_Pprint.op_Hat_Hat uu____3679 uu____3683 in
             FStar_Pprint.group uu____3678)
    | uu____3687 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | ({ FStar_Parser_AST.tm = FStar_Parser_AST.Uvar uu____3691;
         FStar_Parser_AST.range = uu____3692;
         FStar_Parser_AST.level = uu____3693;_},FStar_Parser_AST.UnivApp
       ) -> p_univar (FStar_Pervasives_Native.fst arg_imp)
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____3697 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____3697 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____3699 = str "#" in
        let uu____3700 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____3699 uu____3700
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____3702  ->
    match uu____3702 with | (e,uu____3706) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____3711 =
        let uu____3712 = unparen e in uu____3712.FStar_Parser_AST.tm in
      match uu____3711 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____3713;_},e1::e2::[])
          ->
          let uu____3717 =
            let uu____3718 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3719 =
              let uu____3720 =
                let uu____3721 = p_term e2 in
                soft_parens_with_nesting uu____3721 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3720 in
            FStar_Pprint.op_Hat_Hat uu____3718 uu____3719 in
          FStar_Pprint.group uu____3717
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____3722;_},e1::e2::[])
          ->
          let uu____3726 =
            let uu____3727 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____3728 =
              let uu____3729 =
                let uu____3730 = p_term e2 in
                soft_brackets_with_nesting uu____3730 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3729 in
            FStar_Pprint.op_Hat_Hat uu____3727 uu____3728 in
          FStar_Pprint.group uu____3726
      | uu____3731 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3734 =
      let uu____3735 = unparen e in uu____3735.FStar_Parser_AST.tm in
    match uu____3734 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____3738 = p_quident lid in
        let uu____3739 =
          let uu____3740 =
            let uu____3741 = p_term e1 in soft_parens_with_nesting uu____3741 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3740 in
        FStar_Pprint.op_Hat_Hat uu____3738 uu____3739
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3746 = str (FStar_Ident.text_of_id op) in
        let uu____3747 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____3746 uu____3747
    | uu____3748 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3750 =
      let uu____3751 = unparen e in uu____3751.FStar_Parser_AST.tm in
    match uu____3750 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____3756 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____3762 = str (FStar_Ident.text_of_id op) in
        let uu____3763 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____3762 uu____3763
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____3766 =
          let uu____3767 =
            let uu____3768 = str (FStar_Ident.text_of_id op) in
            let uu____3769 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____3768 uu____3769 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3767 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3766
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____3778 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____3779 =
          let uu____3780 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____3781 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____3780 p_tmEq uu____3781 in
        let uu____3785 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3778 uu____3779 uu____3785
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____3788 =
          let uu____3789 = p_atomicTermNotQUident e1 in
          let uu____3790 =
            let uu____3791 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3791 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____3789 uu____3790 in
        FStar_Pprint.group uu____3788
    | uu____3792 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3794 =
      let uu____3795 = unparen e in uu____3795.FStar_Parser_AST.tm in
    match uu____3794 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____3799 = p_quident constr_lid in
        let uu____3800 =
          let uu____3801 =
            let uu____3802 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____3802 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____3801 in
        FStar_Pprint.op_Hat_Hat uu____3799 uu____3800
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____3804 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____3804 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____3806 = p_term e1 in soft_parens_with_nesting uu____3806
    | uu____3807 when is_array e ->
        let es = extract_from_list e in
        let uu____3810 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____3811 =
          let uu____3812 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____3812 p_noSeqTerm es in
        let uu____3813 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3810 uu____3811 uu____3813
    | uu____3814 when is_list e ->
        let uu____3815 =
          let uu____3816 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3817 = extract_from_list e in
          separate_map_or_flow uu____3816 p_noSeqTerm uu____3817 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3815 FStar_Pprint.rbracket
    | uu____3819 when is_lex_list e ->
        let uu____3820 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____3821 =
          let uu____3822 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____3823 = extract_from_list e in
          separate_map_or_flow uu____3822 p_noSeqTerm uu____3823 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3820 uu____3821 FStar_Pprint.rbracket
    | uu____3825 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____3828 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____3829 =
          let uu____3830 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____3830 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____3828 uu____3829 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____3834 = FStar_Pprint.break_ (Prims.parse_int "0") in
        let uu____3835 =
          let uu____3836 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
          let uu____3837 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____3836 uu____3837 in
        FStar_Pprint.op_Hat_Hat uu____3834 uu____3835
    | FStar_Parser_AST.Op (op,args) when
        let uu____3842 = handleable_op op args in
        Prims.op_Negation uu____3842 ->
        let uu____3843 =
          let uu____3844 =
            let uu____3845 =
              let uu____3846 =
                let uu____3847 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____3847
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____3846 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____3845 in
          Prims.strcat "Operation " uu____3844 in
        failwith uu____3843
    | FStar_Parser_AST.Uvar uu____3854 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____3855 = p_term e in soft_parens_with_nesting uu____3855
    | FStar_Parser_AST.Const uu____3856 ->
        let uu____3857 = p_term e in soft_parens_with_nesting uu____3857
    | FStar_Parser_AST.Op uu____3858 ->
        let uu____3862 = p_term e in soft_parens_with_nesting uu____3862
    | FStar_Parser_AST.Tvar uu____3863 ->
        let uu____3864 = p_term e in soft_parens_with_nesting uu____3864
    | FStar_Parser_AST.Var uu____3865 ->
        let uu____3866 = p_term e in soft_parens_with_nesting uu____3866
    | FStar_Parser_AST.Name uu____3867 ->
        let uu____3868 = p_term e in soft_parens_with_nesting uu____3868
    | FStar_Parser_AST.Construct uu____3869 ->
        let uu____3875 = p_term e in soft_parens_with_nesting uu____3875
    | FStar_Parser_AST.Abs uu____3876 ->
        let uu____3880 = p_term e in soft_parens_with_nesting uu____3880
    | FStar_Parser_AST.App uu____3881 ->
        let uu____3885 = p_term e in soft_parens_with_nesting uu____3885
    | FStar_Parser_AST.Let uu____3886 ->
        let uu____3893 = p_term e in soft_parens_with_nesting uu____3893
    | FStar_Parser_AST.LetOpen uu____3894 ->
        let uu____3897 = p_term e in soft_parens_with_nesting uu____3897
    | FStar_Parser_AST.Seq uu____3898 ->
        let uu____3901 = p_term e in soft_parens_with_nesting uu____3901
    | FStar_Parser_AST.Bind uu____3902 ->
        let uu____3906 = p_term e in soft_parens_with_nesting uu____3906
    | FStar_Parser_AST.If uu____3907 ->
        let uu____3911 = p_term e in soft_parens_with_nesting uu____3911
    | FStar_Parser_AST.Match uu____3912 ->
        let uu____3920 = p_term e in soft_parens_with_nesting uu____3920
    | FStar_Parser_AST.TryWith uu____3921 ->
        let uu____3929 = p_term e in soft_parens_with_nesting uu____3929
    | FStar_Parser_AST.Ascribed uu____3930 ->
        let uu____3935 = p_term e in soft_parens_with_nesting uu____3935
    | FStar_Parser_AST.Record uu____3936 ->
        let uu____3943 = p_term e in soft_parens_with_nesting uu____3943
    | FStar_Parser_AST.Project uu____3944 ->
        let uu____3947 = p_term e in soft_parens_with_nesting uu____3947
    | FStar_Parser_AST.Product uu____3948 ->
        let uu____3952 = p_term e in soft_parens_with_nesting uu____3952
    | FStar_Parser_AST.Sum uu____3953 ->
        let uu____3957 = p_term e in soft_parens_with_nesting uu____3957
    | FStar_Parser_AST.QForall uu____3958 ->
        let uu____3965 = p_term e in soft_parens_with_nesting uu____3965
    | FStar_Parser_AST.QExists uu____3966 ->
        let uu____3973 = p_term e in soft_parens_with_nesting uu____3973
    | FStar_Parser_AST.Refine uu____3974 ->
        let uu____3977 = p_term e in soft_parens_with_nesting uu____3977
    | FStar_Parser_AST.NamedTyp uu____3978 ->
        let uu____3981 = p_term e in soft_parens_with_nesting uu____3981
    | FStar_Parser_AST.Requires uu____3982 ->
        let uu____3986 = p_term e in soft_parens_with_nesting uu____3986
    | FStar_Parser_AST.Ensures uu____3987 ->
        let uu____3991 = p_term e in soft_parens_with_nesting uu____3991
    | FStar_Parser_AST.Assign uu____3992 ->
        let uu____3995 = p_term e in soft_parens_with_nesting uu____3995
    | FStar_Parser_AST.Attributes uu____3996 ->
        let uu____3998 = p_term e in soft_parens_with_nesting uu____3998
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___106_3999  ->
    match uu___106_3999 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____4003 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____4003
    | FStar_Const.Const_string (bytes,uu____4005) ->
        let uu____4008 = str (FStar_Util.string_of_bytes bytes) in
        FStar_Pprint.dquotes uu____4008
    | FStar_Const.Const_bytearray (bytes,uu____4010) ->
        let uu____4013 =
          let uu____4014 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____4014 in
        let uu____4015 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____4013 uu____4015
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_4027 =
          match uu___104_4027 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___105_4031 =
          match uu___105_4031 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____4040  ->
               match uu____4040 with
               | (s,w) ->
                   let uu____4045 = signedness s in
                   let uu____4046 = width w in
                   FStar_Pprint.op_Hat_Hat uu____4045 uu____4046)
            sign_width_opt in
        let uu____4047 = str repr in
        FStar_Pprint.op_Hat_Hat uu____4047 ending
    | FStar_Const.Const_range r ->
        let uu____4049 = FStar_Range.string_of_range r in str uu____4049
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____4051 = p_quident lid in
        let uu____4052 =
          let uu____4053 =
            let uu____4054 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4054 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____4053 in
        FStar_Pprint.op_Hat_Hat uu____4051 uu____4052
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4056 = str "u#" in
    let uu____4057 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____4056 uu____4057
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4059 =
      let uu____4060 = unparen u in uu____4060.FStar_Parser_AST.tm in
    match uu____4059 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4061;_},u1::u2::[])
        ->
        let uu____4065 =
          let uu____4066 = p_universeFrom u1 in
          let uu____4067 =
            let uu____4068 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____4068 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4066 uu____4067 in
        FStar_Pprint.group uu____4065
    | FStar_Parser_AST.App uu____4069 ->
        let uu____4073 = head_and_args u in
        (match uu____4073 with
         | (head1,args) ->
             let uu____4087 =
               let uu____4088 = unparen head1 in
               uu____4088.FStar_Parser_AST.tm in
             (match uu____4087 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____4090 =
                    let uu____4091 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____4092 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____4098  ->
                           match uu____4098 with
                           | (u1,uu____4102) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____4091 uu____4092 in
                  FStar_Pprint.group uu____4090
              | uu____4103 ->
                  let uu____4104 =
                    let uu____4105 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____4105 in
                  failwith uu____4104))
    | uu____4106 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4108 =
      let uu____4109 = unparen u in uu____4109.FStar_Parser_AST.tm in
    match uu____4108 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar uu____4121 -> p_univar u
    | FStar_Parser_AST.Paren u1 ->
        let uu____4123 = p_universeFrom u1 in
        soft_parens_with_nesting uu____4123
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____4124;_},uu____4125::uu____4126::[])
        ->
        let uu____4128 = p_universeFrom u in
        soft_parens_with_nesting uu____4128
    | FStar_Parser_AST.App uu____4129 ->
        let uu____4133 = p_universeFrom u in
        soft_parens_with_nesting uu____4133
    | uu____4134 ->
        let uu____4135 =
          let uu____4136 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____4136 in
        failwith uu____4135
and p_univar: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____4138 =
      let uu____4139 = unparen u in uu____4139.FStar_Parser_AST.tm in
    match uu____4138 with
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | uu____4141 ->
        let uu____4142 =
          let uu____4143 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Not a universe variable %s" uu____4143 in
        failwith uu____4142
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
       | FStar_Parser_AST.Module (uu____4168,decls) ->
           let uu____4172 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4172
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____4177,decls,uu____4179) ->
           let uu____4182 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____4182
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.write should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____4205  ->
         match uu____4205 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____4232,decls) -> decls
        | FStar_Parser_AST.Interface (uu____4236,decls,uu____4238) -> decls in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____4255 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____4262;
                 FStar_Parser_AST.doc = uu____4263;
                 FStar_Parser_AST.quals = uu____4264;
                 FStar_Parser_AST.attrs = uu____4265;_}::uu____4266 ->
                 let d0 = FStar_List.hd ds in
                 let uu____4270 =
                   let uu____4272 =
                     let uu____4274 = FStar_List.tl ds in d :: uu____4274 in
                   d0 :: uu____4272 in
                 (uu____4270, (d0.FStar_Parser_AST.drange))
             | uu____4277 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____4255 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____4300 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____4300 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.read comment_stack in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____4322 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____4322, comments1))))))