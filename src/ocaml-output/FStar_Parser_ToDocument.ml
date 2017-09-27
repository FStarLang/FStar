open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app:
  'Auu____20 'Auu____21 .
    Prims.bool -> ('Auu____21 -> 'Auu____20) -> 'Auu____21 -> 'Auu____20
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
let should_unparen: Prims.bool FStar_ST.ref = FStar_Util.mk_ref true
let rec unparen: FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____86 =
      let uu____87 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____87 in
    if uu____86
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____100 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____115 'Auu____116 .
    'Auu____116 ->
      ('Auu____115 -> 'Auu____116) ->
        'Auu____115 FStar_Pervasives_Native.option -> 'Auu____116
  =
  fun n1  ->
    fun f  ->
      fun x  ->
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
let separate_break_map:
  'Auu____185 .
    FStar_Pprint.document ->
      ('Auu____185 -> FStar_Pprint.document) ->
        'Auu____185 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____207 =
          let uu____208 =
            let uu____209 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____209 in
          FStar_Pprint.separate_map uu____208 f l in
        FStar_Pprint.group uu____207
let precede_break_separate_map:
  'Auu____220 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____220 -> FStar_Pprint.document) ->
          'Auu____220 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____246 =
            let uu____247 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____248 =
              let uu____249 = FStar_List.hd l in
              FStar_All.pipe_right uu____249 f in
            FStar_Pprint.precede uu____247 uu____248 in
          let uu____250 =
            let uu____251 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____257 =
                   let uu____258 =
                     let uu____259 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____259 in
                   FStar_Pprint.op_Hat_Hat sep uu____258 in
                 FStar_Pprint.op_Hat_Hat break1 uu____257) uu____251 in
          FStar_Pprint.op_Hat_Hat uu____246 uu____250
let concat_break_map:
  'Auu____266 .
    ('Auu____266 -> FStar_Pprint.document) ->
      'Auu____266 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____284 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____288 = f x in FStar_Pprint.op_Hat_Hat uu____288 break1)
          l in
      FStar_Pprint.group uu____284
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
    let uu____317 = str "begin" in
    let uu____318 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____317 contents uu____318
let separate_map_or_flow:
  'Auu____327 .
    FStar_Pprint.document ->
      ('Auu____327 -> FStar_Pprint.document) ->
        'Auu____327 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
  'Auu____368 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____368 -> FStar_Pprint.document) ->
                  'Auu____368 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____413 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____413
                       closing)
let soft_surround_map_or_flow:
  'Auu____432 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____432 -> FStar_Pprint.document) ->
                  'Auu____432 Prims.list -> FStar_Pprint.document
  =
  fun n1  ->
    fun b  ->
      fun void_  ->
        fun opening  ->
          fun sep  ->
            fun closing  ->
              fun f  ->
                fun xs  ->
                  if xs = []
                  then void_
                  else
                    (let uu____477 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____477
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____491  ->
    match uu____491 with
    | (comment,keywords) ->
        let uu____516 =
          let uu____517 =
            let uu____520 = str comment in
            let uu____521 =
              let uu____524 =
                let uu____527 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____536  ->
                       match uu____536 with
                       | (k,v1) ->
                           let uu____543 =
                             let uu____546 = str k in
                             let uu____547 =
                               let uu____550 =
                                 let uu____553 = str v1 in [uu____553] in
                               FStar_Pprint.rarrow :: uu____550 in
                             uu____546 :: uu____547 in
                           FStar_Pprint.concat uu____543) keywords in
                [uu____527] in
              FStar_Pprint.space :: uu____524 in
            uu____520 :: uu____521 in
          FStar_Pprint.concat uu____517 in
        FStar_Pprint.group uu____516
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____558 =
      let uu____559 = unparen e in uu____559.FStar_Parser_AST.tm in
    match uu____558 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____560 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____569 =
        let uu____570 = unparen t in uu____570.FStar_Parser_AST.tm in
      match uu____569 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____572 -> false
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
        let uu____594 =
          let uu____595 = unparen e in uu____595.FStar_Parser_AST.tm in
        match uu____594 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____608::(e2,uu____610)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____633 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____646 =
      let uu____647 = unparen e in uu____647.FStar_Parser_AST.tm in
    match uu____646 with
    | FStar_Parser_AST.Construct (uu____650,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____661,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____682 = extract_from_list e2 in e1 :: uu____682
    | uu____685 ->
        let uu____686 =
          let uu____687 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____687 in
        failwith uu____686
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____694 =
      let uu____695 = unparen e in uu____695.FStar_Parser_AST.tm in
    match uu____694 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____697;
           FStar_Parser_AST.level = uu____698;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____700 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____705 =
      let uu____706 = unparen e in uu____706.FStar_Parser_AST.tm in
    match uu____705 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____709;
           FStar_Parser_AST.level = uu____710;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____712;
                                                        FStar_Parser_AST.level
                                                          = uu____713;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____715;
                                                   FStar_Parser_AST.level =
                                                     uu____716;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.set_singleton)
          &&
          (FStar_Ident.lid_equals maybe_addr_of_lid
             FStar_Parser_Const.heap_addr_of_lid)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____718;
                FStar_Parser_AST.level = uu____719;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____721;
           FStar_Parser_AST.level = uu____722;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____724 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____731 =
      let uu____732 = unparen e in uu____732.FStar_Parser_AST.tm in
    match uu____731 with
    | FStar_Parser_AST.Var uu____735 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____736;
           FStar_Parser_AST.range = uu____737;
           FStar_Parser_AST.level = uu____738;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____739;
                                                        FStar_Parser_AST.range
                                                          = uu____740;
                                                        FStar_Parser_AST.level
                                                          = uu____741;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____743;
                                                   FStar_Parser_AST.level =
                                                     uu____744;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____745;
                FStar_Parser_AST.range = uu____746;
                FStar_Parser_AST.level = uu____747;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____749;
           FStar_Parser_AST.level = uu____750;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____752 = extract_from_ref_set e1 in
        let uu____755 = extract_from_ref_set e2 in
        FStar_List.append uu____752 uu____755
    | uu____758 ->
        let uu____759 =
          let uu____760 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____760 in
        failwith uu____759
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____767 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____767
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____772 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____772
let is_general_prefix_op: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0") in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) && ((FStar_Ident.text_of_id op) <> "~"))
let head_and_args:
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____839 =
        let uu____840 = unparen e1 in uu____840.FStar_Parser_AST.tm in
      match uu____839 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____858 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____873 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____878 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____883 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___91_901  ->
    match uu___91_901 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___92_928  ->
      match uu___92_928 with
      | FStar_Util.Inl c ->
          let uu____934 = FStar_String.get s (Prims.parse_int "0") in
          uu____934 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____954 .
    Prims.string ->
      ('Auu____954,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____972  ->
      match uu____972 with
      | (assoc_levels,tokens) ->
          let uu____997 = FStar_List.tryFind (matches_token s) tokens in
          uu____997 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1020 .
    Prims.unit ->
      (associativity,('Auu____1020,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1031  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1048 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1048) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1059  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1084 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1084) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1095  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1116 .
    Prims.unit ->
      (associativity,('Auu____1116,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1127  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1144 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1144) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1155  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1176 .
    Prims.unit ->
      (associativity,('Auu____1176,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1187  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1204 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1204) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1215  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1232 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1232) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1243  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1268 .
    Prims.unit ->
      (associativity,('Auu____1268,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1279  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1296 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1296) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1307  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1324 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1324) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1335  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1352 .
    Prims.unit ->
      (associativity,('Auu____1352,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1363  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1380 .
    Prims.unit ->
      (associativity,('Auu____1380,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1391  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1408 .
    Prims.unit ->
      (associativity,('Auu____1408,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1419  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___93_1606 =
    match uu___93_1606 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1644  ->
         match uu____1644 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1721 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1721 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1769) ->
          assoc_levels
      | uu____1810 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1848 .
    ('Auu____1848,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1904 =
        FStar_List.tryFind
          (fun uu____1942  ->
             match uu____1942 with
             | (uu____1959,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1904 with
      | FStar_Pervasives_Native.Some ((uu____1997,l1,uu____1999),uu____2000)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2051 =
            let uu____2052 =
              let uu____2053 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2053 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2052 in
          failwith uu____2051 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2087 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2087) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2100  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2175 =
      let uu____2188 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2188 (operatorInfix0ad12 ()) in
    uu____2175 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2292 =
      let uu____2305 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2305 opinfix34 in
    uu____2292 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2367 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2367
    then Prims.parse_int "1"
    else
      (let uu____2369 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2369
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2378 . FStar_Ident.ident -> 'Auu____2378 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_28 when _0_28 = (Prims.parse_int "0") -> true
      | _0_29 when _0_29 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
      | _0_30 when _0_30 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (FStar_List.mem (FStar_Ident.text_of_id op)
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_31 when _0_31 = (Prims.parse_int "3") ->
          FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
      | uu____2391 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2425 .
    ('Auu____2425 -> FStar_Pprint.document) ->
      'Auu____2425 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2457 = FStar_ST.op_Bang comment_stack in
          match uu____2457 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2519 = FStar_Range.range_before_pos crange print_pos in
              if uu____2519
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2559 =
                    let uu____2560 =
                      let uu____2561 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2561
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2560 in
                  comments_before_pos uu____2559 print_pos lookahead_pos))
              else
                (let uu____2563 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2563)) in
        let uu____2564 =
          let uu____2569 =
            let uu____2570 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2570 in
          let uu____2571 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2569 uu____2571 in
        match uu____2564 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2577 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2577
              else comments in
            let uu____2583 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2583
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2600 = FStar_ST.op_Bang comment_stack in
          match uu____2600 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2690 =
                    let uu____2691 =
                      let uu____2692 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2692 in
                    uu____2691 - lbegin in
                  max k uu____2690 in
                let doc2 =
                  let uu____2694 =
                    let uu____2695 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2696 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2695 uu____2696 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2694 in
                let uu____2697 =
                  let uu____2698 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2698 in
                place_comments_until_pos (Prims.parse_int "1") uu____2697
                  pos_end doc2))
          | uu____2699 ->
              let lnum =
                let uu____2707 =
                  let uu____2708 = FStar_Range.line_of_pos pos_end in
                  uu____2708 - lbegin in
                max (Prims.parse_int "1") uu____2707 in
              let uu____2709 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2709
let separate_map_with_comments:
  'Auu____2722 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2722 -> FStar_Pprint.document) ->
          'Auu____2722 Prims.list ->
            ('Auu____2722 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2770 x =
              match uu____2770 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2784 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2784 doc1 in
                  let uu____2785 =
                    let uu____2786 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2786 in
                  let uu____2787 =
                    let uu____2788 =
                      let uu____2789 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2789 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2788 in
                  (uu____2785, uu____2787) in
            let uu____2790 =
              let uu____2797 = FStar_List.hd xs in
              let uu____2798 = FStar_List.tl xs in (uu____2797, uu____2798) in
            match uu____2790 with
            | (x,xs1) ->
                let init1 =
                  let uu____2814 =
                    let uu____2815 =
                      let uu____2816 = extract_range x in
                      FStar_Range.end_of_range uu____2816 in
                    FStar_Range.line_of_pos uu____2815 in
                  let uu____2817 =
                    let uu____2818 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2818 in
                  (uu____2814, uu____2817) in
                let uu____2819 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2819
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3114 =
      let uu____3115 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3116 =
        let uu____3117 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3118 =
          let uu____3119 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3120 =
            let uu____3121 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3121 in
          FStar_Pprint.op_Hat_Hat uu____3119 uu____3120 in
        FStar_Pprint.op_Hat_Hat uu____3117 uu____3118 in
      FStar_Pprint.op_Hat_Hat uu____3115 uu____3116 in
    FStar_Pprint.group uu____3114
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3124 =
      let uu____3125 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3125 in
    let uu____3126 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3124 FStar_Pprint.space uu____3126
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3127  ->
    match uu____3127 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3161 =
                match uu____3161 with
                | (kwd,arg) ->
                    let uu____3168 = str "@" in
                    let uu____3169 =
                      let uu____3170 = str kwd in
                      let uu____3171 =
                        let uu____3172 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3172 in
                      FStar_Pprint.op_Hat_Hat uu____3170 uu____3171 in
                    FStar_Pprint.op_Hat_Hat uu____3168 uu____3169 in
              let uu____3173 =
                let uu____3174 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3174 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3173 in
        let uu____3179 =
          let uu____3180 =
            let uu____3181 =
              let uu____3182 =
                let uu____3183 = str doc1 in
                let uu____3184 =
                  let uu____3185 =
                    let uu____3186 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3186 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3185 in
                FStar_Pprint.op_Hat_Hat uu____3183 uu____3184 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3182 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3181 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3180 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3179
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3190 =
          let uu____3191 = str "val" in
          let uu____3192 =
            let uu____3193 =
              let uu____3194 = p_lident lid in
              let uu____3195 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3194 uu____3195 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3193 in
          FStar_Pprint.op_Hat_Hat uu____3191 uu____3192 in
        let uu____3196 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3190 uu____3196
    | FStar_Parser_AST.TopLevelLet (uu____3197,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3222 =
               let uu____3223 = str "let" in
               let uu____3224 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3223 uu____3224 in
             FStar_Pprint.group uu____3222) lbs
    | uu____3225 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3228 =
          let uu____3229 = str "open" in
          let uu____3230 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3229 uu____3230 in
        FStar_Pprint.group uu____3228
    | FStar_Parser_AST.Include uid ->
        let uu____3232 =
          let uu____3233 = str "include" in
          let uu____3234 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3233 uu____3234 in
        FStar_Pprint.group uu____3232
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3237 =
          let uu____3238 = str "module" in
          let uu____3239 =
            let uu____3240 =
              let uu____3241 = p_uident uid1 in
              let uu____3242 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3241 uu____3242 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3240 in
          FStar_Pprint.op_Hat_Hat uu____3238 uu____3239 in
        let uu____3243 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3237 uu____3243
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3245 =
          let uu____3246 = str "module" in
          let uu____3247 =
            let uu____3248 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3248 in
          FStar_Pprint.op_Hat_Hat uu____3246 uu____3247 in
        FStar_Pprint.group uu____3245
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3281 = str "effect" in
          let uu____3282 =
            let uu____3283 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3283 in
          FStar_Pprint.op_Hat_Hat uu____3281 uu____3282 in
        let uu____3284 =
          let uu____3285 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3285 FStar_Pprint.equals in
        let uu____3286 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3284 uu____3286
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3304 = str "type" in
        let uu____3305 = str "and" in
        precede_break_separate_map uu____3304 uu____3305 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3327 = str "let" in
          let uu____3328 =
            let uu____3329 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3329 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3327 uu____3328 in
        let uu____3330 =
          let uu____3331 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3331 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3330 p_letbinding lbs
          (fun uu____3339  ->
             match uu____3339 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3348 =
          let uu____3349 = str "val" in
          let uu____3350 =
            let uu____3351 =
              let uu____3352 = p_lident lid in
              let uu____3353 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3352 uu____3353 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3351 in
          FStar_Pprint.op_Hat_Hat uu____3349 uu____3350 in
        let uu____3354 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3348 uu____3354
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3358 =
            let uu____3359 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3359 FStar_Util.is_upper in
          if uu____3358
          then FStar_Pprint.empty
          else
            (let uu____3367 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3367 FStar_Pprint.space) in
        let uu____3368 =
          let uu____3369 =
            let uu____3370 = p_ident id1 in
            let uu____3371 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3370 uu____3371 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3369 in
        let uu____3372 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3368 uu____3372
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3379 = str "exception" in
        let uu____3380 =
          let uu____3381 =
            let uu____3382 = p_uident uid in
            let uu____3383 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3388 = str "of" in
                   let uu____3389 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3388 uu____3389) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3382 uu____3383 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3381 in
        FStar_Pprint.op_Hat_Hat uu____3379 uu____3380
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3391 = str "new_effect" in
        let uu____3392 =
          let uu____3393 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3393 in
        FStar_Pprint.op_Hat_Hat uu____3391 uu____3392
    | FStar_Parser_AST.SubEffect se ->
        let uu____3395 = str "sub_effect" in
        let uu____3396 =
          let uu____3397 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3397 in
        FStar_Pprint.op_Hat_Hat uu____3395 uu____3396
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3400 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3400 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3401 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3402) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___94_3419  ->
    match uu___94_3419 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3421 = str "#set-options" in
        let uu____3422 =
          let uu____3423 =
            let uu____3424 = str s in FStar_Pprint.dquotes uu____3424 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3423 in
        FStar_Pprint.op_Hat_Hat uu____3421 uu____3422
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3428 = str "#reset-options" in
        let uu____3429 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3433 =
                 let uu____3434 = str s in FStar_Pprint.dquotes uu____3434 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3433) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3428 uu____3429
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")
and p_typars: FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs
and p_fsdocTypeDeclPairs:
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3449  ->
    match uu____3449 with
    | (typedecl,fsdoc_opt) ->
        let uu____3462 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3463 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3462 uu____3463
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___95_3464  ->
    match uu___95_3464 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3479 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3495 =
          let uu____3496 = p_typ t in prefix2 FStar_Pprint.equals uu____3496 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3540 =
          match uu____3540 with
          | (lid1,t,doc_opt) ->
              let uu____3556 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3556 in
        let p_fields uu____3570 =
          let uu____3571 =
            let uu____3572 =
              let uu____3573 =
                let uu____3574 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3574 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3573 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3572 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3571 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3638 =
          match uu____3638 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3664 =
                  let uu____3665 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3665 in
                FStar_Range.extend_to_end_of_line uu____3664 in
              let p_constructorBranch decl =
                let uu____3698 =
                  let uu____3699 =
                    let uu____3700 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3700 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3699 in
                FStar_Pprint.group uu____3698 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3720 =
          let uu____3721 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3721 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3736  ->
             let uu____3737 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3737)
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
            let uu____3752 = p_ident lid in
            let uu____3753 =
              let uu____3754 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3754 in
            FStar_Pprint.op_Hat_Hat uu____3752 uu____3753
          else
            (let binders_doc =
               let uu____3757 = p_typars bs in
               let uu____3758 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3762 =
                        let uu____3763 =
                          let uu____3764 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3764 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3763 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3762) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3757 uu____3758 in
             let uu____3765 = p_ident lid in
             let uu____3766 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3765 binders_doc uu____3766)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3767  ->
    match uu____3767 with
    | (lid,t,doc_opt) ->
        let uu____3783 =
          let uu____3784 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3785 =
            let uu____3786 = p_lident lid in
            let uu____3787 =
              let uu____3788 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3788 in
            FStar_Pprint.op_Hat_Hat uu____3786 uu____3787 in
          FStar_Pprint.op_Hat_Hat uu____3784 uu____3785 in
        FStar_Pprint.group uu____3783
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3789  ->
    match uu____3789 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3817 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3818 =
          let uu____3819 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3820 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3825 =
                   let uu____3826 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3826 in
                 let uu____3827 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3825 uu____3827) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3819 uu____3820 in
        FStar_Pprint.op_Hat_Hat uu____3817 uu____3818
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3828  ->
    match uu____3828 with
    | (pat,uu____3834) ->
        let uu____3835 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3846 =
                let uu____3847 =
                  let uu____3848 =
                    let uu____3849 =
                      let uu____3850 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3850 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3849 in
                  FStar_Pprint.group uu____3848 in
                FStar_Pprint.op_Hat_Hat break1 uu____3847 in
              (pat1, uu____3846)
          | uu____3851 -> (pat, FStar_Pprint.empty) in
        (match uu____3835 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3855);
                     FStar_Parser_AST.prange = uu____3856;_},pats)
                  ->
                  let uu____3866 =
                    let uu____3867 = p_lident x in
                    let uu____3868 =
                      let uu____3869 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____3869 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3867 uu____3868 in
                  FStar_Pprint.group uu____3866
              | uu____3870 ->
                  let uu____3871 =
                    let uu____3872 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____3872 ascr_doc in
                  FStar_Pprint.group uu____3871))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3873  ->
    match uu____3873 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____3881 =
          let uu____3882 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____3882 in
        let uu____3883 = p_term e in prefix2 uu____3881 uu____3883
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___96_3884  ->
    match uu___96_3884 with
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
        let uu____3909 = p_uident uid in
        let uu____3910 = p_binders true bs in
        let uu____3911 =
          let uu____3912 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3912 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3909 uu____3910 uu____3911
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
          let uu____3921 =
            let uu____3922 =
              let uu____3923 =
                let uu____3924 = p_uident uid in
                let uu____3925 = p_binders true bs in
                let uu____3926 =
                  let uu____3927 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3927 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3924 uu____3925 uu____3926 in
              FStar_Pprint.group uu____3923 in
            let uu____3928 =
              let uu____3929 = str "with" in
              let uu____3930 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3929 uu____3930 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3922 uu____3928 in
          braces_with_nesting uu____3921
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3960 =
          let uu____3961 = p_lident lid in
          let uu____3962 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3961 uu____3962 in
        let uu____3963 = p_simpleTerm e in prefix2 uu____3960 uu____3963
    | uu____3964 ->
        let uu____3965 =
          let uu____3966 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3966 in
        failwith uu____3965
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4021 =
        match uu____4021 with
        | (kwd,t) ->
            let uu____4028 =
              let uu____4029 = str kwd in
              let uu____4030 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4029 uu____4030 in
            let uu____4031 = p_simpleTerm t in prefix2 uu____4028 uu____4031 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4036 =
      let uu____4037 =
        let uu____4038 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4039 =
          let uu____4040 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4040 in
        FStar_Pprint.op_Hat_Hat uu____4038 uu____4039 in
      let uu____4041 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4037 uu____4041 in
    let uu____4042 =
      let uu____4043 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4043 in
    FStar_Pprint.op_Hat_Hat uu____4036 uu____4042
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___97_4044  ->
    match uu___97_4044 with
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
    let uu____4046 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4046
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___98_4047  ->
    match uu___98_4047 with
    | FStar_Parser_AST.Rec  ->
        let uu____4048 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4048
    | FStar_Parser_AST.Mutable  ->
        let uu____4049 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4049
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___99_4050  ->
    match uu___99_4050 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4055 =
          let uu____4056 =
            let uu____4057 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4057 in
          FStar_Pprint.separate_map uu____4056 p_tuplePattern pats in
        FStar_Pprint.group uu____4055
    | uu____4058 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4065 =
          let uu____4066 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4066 p_constructorPattern pats in
        FStar_Pprint.group uu____4065
    | uu____4067 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4070;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4075 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4076 = p_constructorPattern hd1 in
        let uu____4077 = p_constructorPattern tl1 in
        infix0 uu____4075 uu____4076 uu____4077
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4079;_},pats)
        ->
        let uu____4085 = p_quident uid in
        let uu____4086 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4085 uu____4086
    | uu____4087 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4091 =
          let uu____4096 =
            let uu____4097 = unparen t in uu____4097.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4096) in
        (match uu____4091 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4102;
               FStar_Parser_AST.blevel = uu____4103;
               FStar_Parser_AST.aqual = uu____4104;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4110 =
               let uu____4111 = p_ident lid in
               p_refinement aqual uu____4111 t1 phi in
             soft_parens_with_nesting uu____4110
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4113;
               FStar_Parser_AST.blevel = uu____4114;
               FStar_Parser_AST.aqual = uu____4115;_},phi))
             ->
             let uu____4117 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4117
         | uu____4118 ->
             let uu____4123 =
               let uu____4124 = p_tuplePattern pat in
               let uu____4125 =
                 let uu____4126 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4127 =
                   let uu____4128 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4128 in
                 FStar_Pprint.op_Hat_Hat uu____4126 uu____4127 in
               FStar_Pprint.op_Hat_Hat uu____4124 uu____4125 in
             soft_parens_with_nesting uu____4123)
    | FStar_Parser_AST.PatList pats ->
        let uu____4132 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4132 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4147 =
          match uu____4147 with
          | (lid,pat) ->
              let uu____4154 = p_qlident lid in
              let uu____4155 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4154 uu____4155 in
        let uu____4156 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4156
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4166 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4167 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4168 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4166 uu____4167 uu____4168
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4179 =
          let uu____4180 =
            let uu____4181 = str (FStar_Ident.text_of_id op) in
            let uu____4182 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4181 uu____4182 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4180 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4179
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4190 = FStar_Pprint.optional p_aqual aqual in
        let uu____4191 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4190 uu____4191
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4193 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4196;
           FStar_Parser_AST.prange = uu____4197;_},uu____4198)
        ->
        let uu____4203 = p_tuplePattern p in
        soft_parens_with_nesting uu____4203
    | FStar_Parser_AST.PatTuple (uu____4204,false ) ->
        let uu____4209 = p_tuplePattern p in
        soft_parens_with_nesting uu____4209
    | uu____4210 ->
        let uu____4211 =
          let uu____4212 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4212 in
        failwith uu____4211
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4216 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4217 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4216 uu____4217
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4222 =
              let uu____4223 = unparen t in uu____4223.FStar_Parser_AST.tm in
            match uu____4222 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4226;
                   FStar_Parser_AST.blevel = uu____4227;
                   FStar_Parser_AST.aqual = uu____4228;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4230 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4230 t1 phi
            | uu____4231 ->
                let uu____4232 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4233 =
                  let uu____4234 = p_lident lid in
                  let uu____4235 =
                    let uu____4236 =
                      let uu____4237 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4238 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4237 uu____4238 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4236 in
                  FStar_Pprint.op_Hat_Hat uu____4234 uu____4235 in
                FStar_Pprint.op_Hat_Hat uu____4232 uu____4233 in
          if is_atomic
          then
            let uu____4239 =
              let uu____4240 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4240 in
            FStar_Pprint.group uu____4239
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4242 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4248 =
            let uu____4249 = unparen t in uu____4249.FStar_Parser_AST.tm in
          (match uu____4248 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4251;
                  FStar_Parser_AST.blevel = uu____4252;
                  FStar_Parser_AST.aqual = uu____4253;_},phi)
               ->
               if is_atomic
               then
                 let uu____4255 =
                   let uu____4256 =
                     let uu____4257 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4257 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4256 in
                 FStar_Pprint.group uu____4255
               else
                 (let uu____4259 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4259)
           | uu____4260 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4268 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4269 =
            let uu____4270 =
              let uu____4271 =
                let uu____4272 = p_appTerm t in
                let uu____4273 =
                  let uu____4274 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4274 in
                FStar_Pprint.op_Hat_Hat uu____4272 uu____4273 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4271 in
            FStar_Pprint.op_Hat_Hat binder uu____4270 in
          FStar_Pprint.op_Hat_Hat uu____4268 uu____4269
and p_binders:
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs
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
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1
and p_term: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4288 =
      let uu____4289 = unparen e in uu____4289.FStar_Parser_AST.tm in
    match uu____4288 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4292 =
          let uu____4293 =
            let uu____4294 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4294 FStar_Pprint.semi in
          FStar_Pprint.group uu____4293 in
        let uu____4295 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4292 uu____4295
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4299 =
          let uu____4300 =
            let uu____4301 =
              let uu____4302 = p_lident x in
              let uu____4303 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4302 uu____4303 in
            let uu____4304 =
              let uu____4305 = p_noSeqTerm e1 in
              let uu____4306 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4305 uu____4306 in
            op_Hat_Slash_Plus_Hat uu____4301 uu____4304 in
          FStar_Pprint.group uu____4300 in
        let uu____4307 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4299 uu____4307
    | uu____4308 ->
        let uu____4309 = p_noSeqTerm e in FStar_Pprint.group uu____4309
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4312 =
      let uu____4313 = unparen e in uu____4313.FStar_Parser_AST.tm in
    match uu____4312 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4318 =
          let uu____4319 = p_tmIff e1 in
          let uu____4320 =
            let uu____4321 =
              let uu____4322 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4322 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4321 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4319 uu____4320 in
        FStar_Pprint.group uu____4318
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4328 =
          let uu____4329 = p_tmIff e1 in
          let uu____4330 =
            let uu____4331 =
              let uu____4332 =
                let uu____4333 = p_typ t in
                let uu____4334 =
                  let uu____4335 = str "by" in
                  let uu____4336 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4335 uu____4336 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4333 uu____4334 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4332 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4331 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4329 uu____4330 in
        FStar_Pprint.group uu____4328
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4337;_},e1::e2::e3::[])
        ->
        let uu____4343 =
          let uu____4344 =
            let uu____4345 =
              let uu____4346 = p_atomicTermNotQUident e1 in
              let uu____4347 =
                let uu____4348 =
                  let uu____4349 =
                    let uu____4350 = p_term e2 in
                    soft_parens_with_nesting uu____4350 in
                  let uu____4351 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4349 uu____4351 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4348 in
              FStar_Pprint.op_Hat_Hat uu____4346 uu____4347 in
            FStar_Pprint.group uu____4345 in
          let uu____4352 =
            let uu____4353 = p_noSeqTerm e3 in jump2 uu____4353 in
          FStar_Pprint.op_Hat_Hat uu____4344 uu____4352 in
        FStar_Pprint.group uu____4343
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4354;_},e1::e2::e3::[])
        ->
        let uu____4360 =
          let uu____4361 =
            let uu____4362 =
              let uu____4363 = p_atomicTermNotQUident e1 in
              let uu____4364 =
                let uu____4365 =
                  let uu____4366 =
                    let uu____4367 = p_term e2 in
                    soft_brackets_with_nesting uu____4367 in
                  let uu____4368 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4366 uu____4368 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4365 in
              FStar_Pprint.op_Hat_Hat uu____4363 uu____4364 in
            FStar_Pprint.group uu____4362 in
          let uu____4369 =
            let uu____4370 = p_noSeqTerm e3 in jump2 uu____4370 in
          FStar_Pprint.op_Hat_Hat uu____4361 uu____4369 in
        FStar_Pprint.group uu____4360
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4380 =
          let uu____4381 = str "requires" in
          let uu____4382 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4381 uu____4382 in
        FStar_Pprint.group uu____4380
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4392 =
          let uu____4393 = str "ensures" in
          let uu____4394 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4393 uu____4394 in
        FStar_Pprint.group uu____4392
    | FStar_Parser_AST.Attributes es ->
        let uu____4398 =
          let uu____4399 = str "attributes" in
          let uu____4400 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4399 uu____4400 in
        FStar_Pprint.group uu____4398
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4404 = is_unit e3 in
        if uu____4404
        then
          let uu____4405 =
            let uu____4406 =
              let uu____4407 = str "if" in
              let uu____4408 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4407 uu____4408 in
            let uu____4409 =
              let uu____4410 = str "then" in
              let uu____4411 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4410 uu____4411 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4406 uu____4409 in
          FStar_Pprint.group uu____4405
        else
          (let e2_doc =
             let uu____4414 =
               let uu____4415 = unparen e2 in uu____4415.FStar_Parser_AST.tm in
             match uu____4414 with
             | FStar_Parser_AST.If (uu____4416,uu____4417,e31) when
                 is_unit e31 ->
                 let uu____4419 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4419
             | uu____4420 -> p_noSeqTerm e2 in
           let uu____4421 =
             let uu____4422 =
               let uu____4423 = str "if" in
               let uu____4424 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4423 uu____4424 in
             let uu____4425 =
               let uu____4426 =
                 let uu____4427 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4427 e2_doc in
               let uu____4428 =
                 let uu____4429 = str "else" in
                 let uu____4430 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4429 uu____4430 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4426 uu____4428 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4422 uu____4425 in
           FStar_Pprint.group uu____4421)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4453 =
          let uu____4454 =
            let uu____4455 = str "try" in
            let uu____4456 = p_noSeqTerm e1 in prefix2 uu____4455 uu____4456 in
          let uu____4457 =
            let uu____4458 = str "with" in
            let uu____4459 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4458 uu____4459 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4454 uu____4457 in
        FStar_Pprint.group uu____4453
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4490 =
          let uu____4491 =
            let uu____4492 = str "match" in
            let uu____4493 = p_noSeqTerm e1 in
            let uu____4494 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4492 uu____4493 uu____4494 in
          let uu____4495 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4491 uu____4495 in
        FStar_Pprint.group uu____4490
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4506 =
          let uu____4507 =
            let uu____4508 = str "let open" in
            let uu____4509 = p_quident uid in
            let uu____4510 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4508 uu____4509 uu____4510 in
          let uu____4511 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4507 uu____4511 in
        FStar_Pprint.group uu____4506
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4528 = str "let" in
          let uu____4529 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4528 uu____4529 in
        let uu____4530 =
          let uu____4531 =
            let uu____4532 =
              let uu____4533 = str "and" in
              precede_break_separate_map let_doc uu____4533 p_letbinding lbs in
            let uu____4538 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4532 uu____4538 in
          FStar_Pprint.group uu____4531 in
        let uu____4539 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4530 uu____4539
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4542;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4545;
                                                         FStar_Parser_AST.level
                                                           = uu____4546;_})
        when matches_var maybe_x x ->
        let uu____4573 =
          let uu____4574 = str "function" in
          let uu____4575 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4574 uu____4575 in
        FStar_Pprint.group uu____4573
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4586 =
          let uu____4587 = p_lident id1 in
          let uu____4588 =
            let uu____4589 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4589 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4587 uu____4588 in
        FStar_Pprint.group uu____4586
    | uu____4590 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4593 =
      let uu____4594 = unparen e in uu____4594.FStar_Parser_AST.tm in
    match uu____4593 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4610 =
          let uu____4611 =
            let uu____4612 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4612 FStar_Pprint.space in
          let uu____4613 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4611 uu____4613 FStar_Pprint.dot in
        let uu____4614 =
          let uu____4615 = p_trigger trigger in
          let uu____4616 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4615 uu____4616 in
        prefix2 uu____4610 uu____4614
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4632 =
          let uu____4633 =
            let uu____4634 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4634 FStar_Pprint.space in
          let uu____4635 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4633 uu____4635 FStar_Pprint.dot in
        let uu____4636 =
          let uu____4637 = p_trigger trigger in
          let uu____4638 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4637 uu____4638 in
        prefix2 uu____4632 uu____4636
    | uu____4639 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4641 =
      let uu____4642 = unparen e in uu____4642.FStar_Parser_AST.tm in
    match uu____4641 with
    | FStar_Parser_AST.QForall uu____4643 -> str "forall"
    | FStar_Parser_AST.QExists uu____4656 -> str "exists"
    | uu____4669 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___100_4670  ->
    match uu___100_4670 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4682 =
          let uu____4683 =
            let uu____4684 = str "pattern" in
            let uu____4685 =
              let uu____4686 =
                let uu____4687 = p_disjunctivePats pats in jump2 uu____4687 in
              let uu____4688 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4686 uu____4688 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4684 uu____4685 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4683 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4682
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4694 = str "\\/" in
    FStar_Pprint.separate_map uu____4694 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4700 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4700
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4702 =
      let uu____4703 = unparen e in uu____4703.FStar_Parser_AST.tm in
    match uu____4702 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4710 =
          let uu____4711 = str "fun" in
          let uu____4712 =
            let uu____4713 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4713 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4711 uu____4712 in
        let uu____4714 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4710 uu____4714
    | uu____4715 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4718  ->
    match uu____4718 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4737 =
            let uu____4738 = unparen e in uu____4738.FStar_Parser_AST.tm in
          match uu____4737 with
          | FStar_Parser_AST.Match uu____4741 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4756 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4772);
                 FStar_Parser_AST.prange = uu____4773;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4775);
                                                               FStar_Parser_AST.range
                                                                 = uu____4776;
                                                               FStar_Parser_AST.level
                                                                 = uu____4777;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4804 -> (fun x  -> x) in
        let uu____4806 =
          let uu____4807 =
            let uu____4808 =
              let uu____4809 =
                let uu____4810 =
                  let uu____4811 = p_disjunctivePattern pat in
                  let uu____4812 =
                    let uu____4813 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4813 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4811 uu____4812 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4810 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4809 in
            FStar_Pprint.group uu____4808 in
          let uu____4814 =
            let uu____4815 = p_term e in maybe_paren uu____4815 in
          op_Hat_Slash_Plus_Hat uu____4807 uu____4814 in
        FStar_Pprint.group uu____4806
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___101_4816  ->
    match uu___101_4816 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4820 = str "when" in
        let uu____4821 =
          let uu____4822 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4822 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4820 uu____4821
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4824 =
      let uu____4825 = unparen e in uu____4825.FStar_Parser_AST.tm in
    match uu____4824 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4826;_},e1::e2::[])
        ->
        let uu____4831 = str "<==>" in
        let uu____4832 = p_tmImplies e1 in
        let uu____4833 = p_tmIff e2 in
        infix0 uu____4831 uu____4832 uu____4833
    | uu____4834 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4836 =
      let uu____4837 = unparen e in uu____4837.FStar_Parser_AST.tm in
    match uu____4836 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4838;_},e1::e2::[])
        ->
        let uu____4843 = str "==>" in
        let uu____4844 = p_tmArrow p_tmFormula e1 in
        let uu____4845 = p_tmImplies e2 in
        infix0 uu____4843 uu____4844 uu____4845
    | uu____4846 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4851 =
        let uu____4852 = unparen e in uu____4852.FStar_Parser_AST.tm in
      match uu____4851 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4859 =
            let uu____4860 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4865 = p_binder false b in
                   let uu____4866 =
                     let uu____4867 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4867 in
                   FStar_Pprint.op_Hat_Hat uu____4865 uu____4866) bs in
            let uu____4868 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4860 uu____4868 in
          FStar_Pprint.group uu____4859
      | uu____4869 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4871 =
      let uu____4872 = unparen e in uu____4872.FStar_Parser_AST.tm in
    match uu____4871 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4873;_},e1::e2::[])
        ->
        let uu____4878 = str "\\/" in
        let uu____4879 = p_tmFormula e1 in
        let uu____4880 = p_tmConjunction e2 in
        infix0 uu____4878 uu____4879 uu____4880
    | uu____4881 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4883 =
      let uu____4884 = unparen e in uu____4884.FStar_Parser_AST.tm in
    match uu____4883 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4885;_},e1::e2::[])
        ->
        let uu____4890 = str "/\\" in
        let uu____4891 = p_tmConjunction e1 in
        let uu____4892 = p_tmTuple e2 in
        infix0 uu____4890 uu____4891 uu____4892
    | uu____4893 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4896 =
      let uu____4897 = unparen e in uu____4897.FStar_Parser_AST.tm in
    match uu____4896 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4912 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4912
          (fun uu____4920  ->
             match uu____4920 with | (e1,uu____4926) -> p_tmEq e1) args
    | uu____4927 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4932 =
             let uu____4933 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4933 in
           FStar_Pprint.group uu____4932)
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
      let uu____4978 =
        let uu____4979 = unparen e in uu____4979.FStar_Parser_AST.tm in
      match uu____4978 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____4986 = levels op1 in
          (match uu____4986 with
           | (left1,mine,right1) ->
               let uu____4996 =
                 let uu____4997 = FStar_All.pipe_left str op1 in
                 let uu____4998 = p_tmEq' left1 e1 in
                 let uu____4999 = p_tmEq' right1 e2 in
                 infix0 uu____4997 uu____4998 uu____4999 in
               paren_if curr mine uu____4996)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5000;_},e1::e2::[])
          ->
          let uu____5005 =
            let uu____5006 = p_tmEq e1 in
            let uu____5007 =
              let uu____5008 =
                let uu____5009 =
                  let uu____5010 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5010 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5009 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5008 in
            FStar_Pprint.op_Hat_Hat uu____5006 uu____5007 in
          FStar_Pprint.group uu____5005
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5011;_},e1::[])
          ->
          let uu____5015 = levels "-" in
          (match uu____5015 with
           | (left1,mine,right1) ->
               let uu____5025 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5025)
      | uu____5026 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5081 =
        let uu____5082 = unparen e in uu____5082.FStar_Parser_AST.tm in
      match uu____5081 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5085)::(e2,uu____5087)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5107 = is_list e in Prims.op_Negation uu____5107)
          ->
          let op = "::" in
          let uu____5109 = levels op in
          (match uu____5109 with
           | (left1,mine,right1) ->
               let uu____5119 =
                 let uu____5120 = str op in
                 let uu____5121 = p_tmNoEq' left1 e1 in
                 let uu____5122 = p_tmNoEq' right1 e2 in
                 infix0 uu____5120 uu____5121 uu____5122 in
               paren_if curr mine uu____5119)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5130 = levels op in
          (match uu____5130 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5144 = p_binder false b in
                 let uu____5145 =
                   let uu____5146 =
                     let uu____5147 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5147 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5146 in
                 FStar_Pprint.op_Hat_Hat uu____5144 uu____5145 in
               let uu____5148 =
                 let uu____5149 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5150 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5149 uu____5150 in
               paren_if curr mine uu____5148)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5157 = levels op1 in
          (match uu____5157 with
           | (left1,mine,right1) ->
               let uu____5167 =
                 let uu____5168 = str op1 in
                 let uu____5169 = p_tmNoEq' left1 e1 in
                 let uu____5170 = p_tmNoEq' right1 e2 in
                 infix0 uu____5168 uu____5169 uu____5170 in
               paren_if curr mine uu____5167)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5173 =
            let uu____5174 = p_lidentOrUnderscore lid in
            let uu____5175 =
              let uu____5176 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5176 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5174 uu____5175 in
          FStar_Pprint.group uu____5173
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5197 =
            let uu____5198 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5199 =
              let uu____5200 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5200 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5198 uu____5199 in
          braces_with_nesting uu____5197
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5205;_},e1::[])
          ->
          let uu____5209 =
            let uu____5210 = str "~" in
            let uu____5211 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5210 uu____5211 in
          FStar_Pprint.group uu____5209
      | uu____5212 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5214 = p_appTerm e in
    let uu____5215 =
      let uu____5216 =
        let uu____5217 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5217 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5216 in
    FStar_Pprint.op_Hat_Hat uu____5214 uu____5215
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5222 =
            let uu____5223 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5223 t phi in
          soft_parens_with_nesting uu____5222
      | FStar_Parser_AST.TAnnotated uu____5224 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5229 ->
          let uu____5230 =
            let uu____5231 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5231 in
          failwith uu____5230
      | FStar_Parser_AST.TVariable uu____5232 ->
          let uu____5233 =
            let uu____5234 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5234 in
          failwith uu____5233
      | FStar_Parser_AST.NoName uu____5235 ->
          let uu____5236 =
            let uu____5237 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5237 in
          failwith uu____5236
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5238  ->
    match uu____5238 with
    | (lid,e) ->
        let uu____5245 =
          let uu____5246 = p_qlident lid in
          let uu____5247 =
            let uu____5248 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5248 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5246 uu____5247 in
        FStar_Pprint.group uu____5245
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5250 =
      let uu____5251 = unparen e in uu____5251.FStar_Parser_AST.tm in
    match uu____5250 with
    | FStar_Parser_AST.App uu____5252 when is_general_application e ->
        let uu____5259 = head_and_args e in
        (match uu____5259 with
         | (head1,args) ->
             let uu____5284 =
               let uu____5295 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5295
               then
                 let uu____5316 =
                   FStar_Util.take
                     (fun uu____5340  ->
                        match uu____5340 with
                        | (uu____5345,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5316 with
                 | (fs_typ_args,args1) ->
                     let uu____5383 =
                       let uu____5384 = p_indexingTerm head1 in
                       let uu____5385 =
                         let uu____5386 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5386 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5384 uu____5385 in
                     (uu____5383, args1)
               else
                 (let uu____5398 = p_indexingTerm head1 in (uu____5398, args)) in
             (match uu____5284 with
              | (head_doc,args1) ->
                  let uu____5419 =
                    let uu____5420 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5420 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5419))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5440 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5440)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5458 =
               let uu____5459 = p_quident lid in
               let uu____5460 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5459 uu____5460 in
             FStar_Pprint.group uu____5458
         | hd1::tl1 ->
             let uu____5477 =
               let uu____5478 =
                 let uu____5479 =
                   let uu____5480 = p_quident lid in
                   let uu____5481 = p_argTerm hd1 in
                   prefix2 uu____5480 uu____5481 in
                 FStar_Pprint.group uu____5479 in
               let uu____5482 =
                 let uu____5483 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5483 in
               FStar_Pprint.op_Hat_Hat uu____5478 uu____5482 in
             FStar_Pprint.group uu____5477)
    | uu____5488 -> p_indexingTerm e
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
         (let uu____5497 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5497 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5499 = str "#" in
        let uu____5500 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5499 uu____5500
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5502  ->
    match uu____5502 with | (e,uu____5508) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5513 =
        let uu____5514 = unparen e in uu____5514.FStar_Parser_AST.tm in
      match uu____5513 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5515;_},e1::e2::[])
          ->
          let uu____5520 =
            let uu____5521 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5522 =
              let uu____5523 =
                let uu____5524 = p_term e2 in
                soft_parens_with_nesting uu____5524 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5523 in
            FStar_Pprint.op_Hat_Hat uu____5521 uu____5522 in
          FStar_Pprint.group uu____5520
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5525;_},e1::e2::[])
          ->
          let uu____5530 =
            let uu____5531 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5532 =
              let uu____5533 =
                let uu____5534 = p_term e2 in
                soft_brackets_with_nesting uu____5534 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5533 in
            FStar_Pprint.op_Hat_Hat uu____5531 uu____5532 in
          FStar_Pprint.group uu____5530
      | uu____5535 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5538 =
      let uu____5539 = unparen e in uu____5539.FStar_Parser_AST.tm in
    match uu____5538 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5542 = p_quident lid in
        let uu____5543 =
          let uu____5544 =
            let uu____5545 = p_term e1 in soft_parens_with_nesting uu____5545 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5544 in
        FStar_Pprint.op_Hat_Hat uu____5542 uu____5543
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5551 = str (FStar_Ident.text_of_id op) in
        let uu____5552 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5551 uu____5552
    | uu____5553 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5555 =
      let uu____5556 = unparen e in uu____5556.FStar_Parser_AST.tm in
    match uu____5555 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5567 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5574 = str (FStar_Ident.text_of_id op) in
        let uu____5575 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5574 uu____5575
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5579 =
          let uu____5580 =
            let uu____5581 = str (FStar_Ident.text_of_id op) in
            let uu____5582 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5581 uu____5582 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5580 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5579
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5597 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5598 =
          let uu____5599 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5600 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5599 p_tmEq uu____5600 in
        let uu____5607 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5597 uu____5598 uu____5607
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5610 =
          let uu____5611 = p_atomicTermNotQUident e1 in
          let uu____5612 =
            let uu____5613 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5613 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5611 uu____5612 in
        FStar_Pprint.group uu____5610
    | uu____5614 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5616 =
      let uu____5617 = unparen e in uu____5617.FStar_Parser_AST.tm in
    match uu____5616 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5621 = p_quident constr_lid in
        let uu____5622 =
          let uu____5623 =
            let uu____5624 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5624 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5623 in
        FStar_Pprint.op_Hat_Hat uu____5621 uu____5622
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5626 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5626 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5628 = p_term e1 in soft_parens_with_nesting uu____5628
    | uu____5629 when is_array e ->
        let es = extract_from_list e in
        let uu____5633 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5634 =
          let uu____5635 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5635 p_noSeqTerm es in
        let uu____5636 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5633 uu____5634 uu____5636
    | uu____5637 when is_list e ->
        let uu____5638 =
          let uu____5639 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5640 = extract_from_list e in
          separate_map_or_flow uu____5639 p_noSeqTerm uu____5640 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5638 FStar_Pprint.rbracket
    | uu____5643 when is_lex_list e ->
        let uu____5644 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5645 =
          let uu____5646 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5647 = extract_from_list e in
          separate_map_or_flow uu____5646 p_noSeqTerm uu____5647 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5644 uu____5645 FStar_Pprint.rbracket
    | uu____5650 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5654 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5655 =
          let uu____5656 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5656 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5654 uu____5655 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5660 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5661 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5660 uu____5661
    | FStar_Parser_AST.Op (op,args) when
        let uu____5668 = handleable_op op args in
        Prims.op_Negation uu____5668 ->
        let uu____5669 =
          let uu____5670 =
            let uu____5671 =
              let uu____5672 =
                let uu____5673 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5673
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5672 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5671 in
          Prims.strcat "Operation " uu____5670 in
        failwith uu____5669
    | FStar_Parser_AST.Uvar uu____5674 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5675 = p_term e in soft_parens_with_nesting uu____5675
    | FStar_Parser_AST.Const uu____5676 ->
        let uu____5677 = p_term e in soft_parens_with_nesting uu____5677
    | FStar_Parser_AST.Op uu____5678 ->
        let uu____5685 = p_term e in soft_parens_with_nesting uu____5685
    | FStar_Parser_AST.Tvar uu____5686 ->
        let uu____5687 = p_term e in soft_parens_with_nesting uu____5687
    | FStar_Parser_AST.Var uu____5688 ->
        let uu____5689 = p_term e in soft_parens_with_nesting uu____5689
    | FStar_Parser_AST.Name uu____5690 ->
        let uu____5691 = p_term e in soft_parens_with_nesting uu____5691
    | FStar_Parser_AST.Construct uu____5692 ->
        let uu____5703 = p_term e in soft_parens_with_nesting uu____5703
    | FStar_Parser_AST.Abs uu____5704 ->
        let uu____5711 = p_term e in soft_parens_with_nesting uu____5711
    | FStar_Parser_AST.App uu____5712 ->
        let uu____5719 = p_term e in soft_parens_with_nesting uu____5719
    | FStar_Parser_AST.Let uu____5720 ->
        let uu____5733 = p_term e in soft_parens_with_nesting uu____5733
    | FStar_Parser_AST.LetOpen uu____5734 ->
        let uu____5739 = p_term e in soft_parens_with_nesting uu____5739
    | FStar_Parser_AST.Seq uu____5740 ->
        let uu____5745 = p_term e in soft_parens_with_nesting uu____5745
    | FStar_Parser_AST.Bind uu____5746 ->
        let uu____5753 = p_term e in soft_parens_with_nesting uu____5753
    | FStar_Parser_AST.If uu____5754 ->
        let uu____5761 = p_term e in soft_parens_with_nesting uu____5761
    | FStar_Parser_AST.Match uu____5762 ->
        let uu____5777 = p_term e in soft_parens_with_nesting uu____5777
    | FStar_Parser_AST.TryWith uu____5778 ->
        let uu____5793 = p_term e in soft_parens_with_nesting uu____5793
    | FStar_Parser_AST.Ascribed uu____5794 ->
        let uu____5803 = p_term e in soft_parens_with_nesting uu____5803
    | FStar_Parser_AST.Record uu____5804 ->
        let uu____5817 = p_term e in soft_parens_with_nesting uu____5817
    | FStar_Parser_AST.Project uu____5818 ->
        let uu____5823 = p_term e in soft_parens_with_nesting uu____5823
    | FStar_Parser_AST.Product uu____5824 ->
        let uu____5831 = p_term e in soft_parens_with_nesting uu____5831
    | FStar_Parser_AST.Sum uu____5832 ->
        let uu____5839 = p_term e in soft_parens_with_nesting uu____5839
    | FStar_Parser_AST.QForall uu____5840 ->
        let uu____5853 = p_term e in soft_parens_with_nesting uu____5853
    | FStar_Parser_AST.QExists uu____5854 ->
        let uu____5867 = p_term e in soft_parens_with_nesting uu____5867
    | FStar_Parser_AST.Refine uu____5868 ->
        let uu____5873 = p_term e in soft_parens_with_nesting uu____5873
    | FStar_Parser_AST.NamedTyp uu____5874 ->
        let uu____5879 = p_term e in soft_parens_with_nesting uu____5879
    | FStar_Parser_AST.Requires uu____5880 ->
        let uu____5887 = p_term e in soft_parens_with_nesting uu____5887
    | FStar_Parser_AST.Ensures uu____5888 ->
        let uu____5895 = p_term e in soft_parens_with_nesting uu____5895
    | FStar_Parser_AST.Assign uu____5896 ->
        let uu____5901 = p_term e in soft_parens_with_nesting uu____5901
    | FStar_Parser_AST.Attributes uu____5902 ->
        let uu____5905 = p_term e in soft_parens_with_nesting uu____5905
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___104_5906  ->
    match uu___104_5906 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5910 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5910
    | FStar_Const.Const_string (s,uu____5921) ->
        let uu____5922 = str s in FStar_Pprint.dquotes uu____5922
    | FStar_Const.Const_bytearray (bytes,uu____5924) ->
        let uu____5929 =
          let uu____5930 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5930 in
        let uu____5931 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5929 uu____5931
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___102_5949 =
          match uu___102_5949 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___103_5953 =
          match uu___103_5953 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5964  ->
               match uu____5964 with
               | (s,w) ->
                   let uu____5971 = signedness s in
                   let uu____5972 = width w in
                   FStar_Pprint.op_Hat_Hat uu____5971 uu____5972)
            sign_width_opt in
        let uu____5973 = str repr in
        FStar_Pprint.op_Hat_Hat uu____5973 ending
    | FStar_Const.Const_range r ->
        let uu____5975 = FStar_Range.string_of_range r in str uu____5975
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5977 = p_quident lid in
        let uu____5978 =
          let uu____5979 =
            let uu____5980 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5980 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5979 in
        FStar_Pprint.op_Hat_Hat uu____5977 uu____5978
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5982 = str "u#" in
    let uu____5983 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____5982 uu____5983
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5985 =
      let uu____5986 = unparen u in uu____5986.FStar_Parser_AST.tm in
    match uu____5985 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5987;_},u1::u2::[])
        ->
        let uu____5992 =
          let uu____5993 = p_universeFrom u1 in
          let uu____5994 =
            let uu____5995 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5995 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5993 uu____5994 in
        FStar_Pprint.group uu____5992
    | FStar_Parser_AST.App uu____5996 ->
        let uu____6003 = head_and_args u in
        (match uu____6003 with
         | (head1,args) ->
             let uu____6028 =
               let uu____6029 = unparen head1 in
               uu____6029.FStar_Parser_AST.tm in
             (match uu____6028 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6031 =
                    let uu____6032 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6033 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6041  ->
                           match uu____6041 with
                           | (u1,uu____6047) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6032 uu____6033 in
                  FStar_Pprint.group uu____6031
              | uu____6048 ->
                  let uu____6049 =
                    let uu____6050 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6050 in
                  failwith uu____6049))
    | uu____6051 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6053 =
      let uu____6054 = unparen u in uu____6054.FStar_Parser_AST.tm in
    match uu____6053 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6077 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6077
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6078;_},uu____6079::uu____6080::[])
        ->
        let uu____6083 = p_universeFrom u in
        soft_parens_with_nesting uu____6083
    | FStar_Parser_AST.App uu____6084 ->
        let uu____6091 = p_universeFrom u in
        soft_parens_with_nesting uu____6091
    | uu____6092 ->
        let uu____6093 =
          let uu____6094 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6094 in
        failwith uu____6093
let term_to_document: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e
let signature_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_justSig e
let decl_to_document: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e
let pat_to_document: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p
let binder_to_document: FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b
let modul_to_document: FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____6131,decls) ->
           let uu____6137 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6137
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6146,decls,uu____6148) ->
           let uu____6153 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6153
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6196  ->
         match uu____6196 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6238,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6244,decls,uu____6246) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6282 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6295;
                 FStar_Parser_AST.doc = uu____6296;
                 FStar_Parser_AST.quals = uu____6297;
                 FStar_Parser_AST.attrs = uu____6298;_}::uu____6299 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6305 =
                   let uu____6308 =
                     let uu____6311 = FStar_List.tl ds in d :: uu____6311 in
                   d0 :: uu____6308 in
                 (uu____6305, (d0.FStar_Parser_AST.drange))
             | uu____6316 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6282 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6377 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6377 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6470 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6470, comments1))))))