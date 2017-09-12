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
      let uu____821 =
        let uu____822 = unparen e1 in uu____822.FStar_Parser_AST.tm in
      match uu____821 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____840 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____855 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____860 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____865 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___91_883  ->
    match uu___91_883 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___92_901  ->
      match uu___92_901 with
      | FStar_Util.Inl c ->
          let uu____907 = FStar_String.get s (Prims.parse_int "0") in
          uu____907 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____915 .
    Prims.string ->
      ('Auu____915,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____933  ->
      match uu____933 with
      | (assoc_levels,tokens) ->
          let uu____958 = FStar_List.tryFind (matches_token s) tokens in
          uu____958 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____981 .
    Prims.unit ->
      (associativity,('Auu____981,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____992  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1009 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1009) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1020  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1045 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1045) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1056  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1077 .
    Prims.unit ->
      (associativity,('Auu____1077,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1088  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1105 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1105) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1116  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1137 .
    Prims.unit ->
      (associativity,('Auu____1137,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1148  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1165 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1165) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1176  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1193 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1193) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1204  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1229 .
    Prims.unit ->
      (associativity,('Auu____1229,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1240  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1257 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1257) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1268  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1285 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1285) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1296  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1313 .
    Prims.unit ->
      (associativity,('Auu____1313,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1324  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1341 .
    Prims.unit ->
      (associativity,('Auu____1341,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1352  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1369 .
    Prims.unit ->
      (associativity,('Auu____1369,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1380  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___93_1567 =
    match uu___93_1567 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1605  ->
         match uu____1605 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1682 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1682 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1730) ->
          assoc_levels
      | uu____1771 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1809 .
    ('Auu____1809,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1865 =
        FStar_List.tryFind
          (fun uu____1903  ->
             match uu____1903 with
             | (uu____1920,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1865 with
      | FStar_Pervasives_Native.Some ((uu____1958,l1,uu____1960),uu____1961)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2012 =
            let uu____2013 =
              let uu____2014 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2014 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2013 in
          failwith uu____2012 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2048 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2048) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2061  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2136 =
      let uu____2149 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2149 (operatorInfix0ad12 ()) in
    uu____2136 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2253 =
      let uu____2266 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2266 opinfix34 in
    uu____2253 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2328 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2328
    then Prims.parse_int "1"
    else
      (let uu____2330 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2330
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2339 . FStar_Ident.ident -> 'Auu____2339 Prims.list -> Prims.bool =
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
      | uu____2352 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2386 .
    ('Auu____2386 -> FStar_Pprint.document) ->
      'Auu____2386 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2418 = FStar_ST.op_Bang comment_stack in
          match uu____2418 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2480 = FStar_Range.range_before_pos crange print_pos in
              if uu____2480
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2520 =
                    let uu____2521 =
                      let uu____2522 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2522
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2521 in
                  comments_before_pos uu____2520 print_pos lookahead_pos))
              else
                (let uu____2524 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2524)) in
        let uu____2525 =
          let uu____2530 =
            let uu____2531 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2531 in
          let uu____2532 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2530 uu____2532 in
        match uu____2525 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2538 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2538
              else comments in
            let uu____2544 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2544
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2561 = FStar_ST.op_Bang comment_stack in
          match uu____2561 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2651 =
                    let uu____2652 =
                      let uu____2653 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2653 in
                    uu____2652 - lbegin in
                  max k uu____2651 in
                let doc2 =
                  let uu____2655 =
                    let uu____2656 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2657 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2656 uu____2657 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2655 in
                let uu____2658 =
                  let uu____2659 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2659 in
                place_comments_until_pos (Prims.parse_int "1") uu____2658
                  pos_end doc2))
          | uu____2660 ->
              let lnum =
                let uu____2668 =
                  let uu____2669 = FStar_Range.line_of_pos pos_end in
                  uu____2669 - lbegin in
                max (Prims.parse_int "1") uu____2668 in
              let uu____2670 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2670
let separate_map_with_comments:
  'Auu____2683 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2683 -> FStar_Pprint.document) ->
          'Auu____2683 Prims.list ->
            ('Auu____2683 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2731 x =
              match uu____2731 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2745 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2745 doc1 in
                  let uu____2746 =
                    let uu____2747 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2747 in
                  let uu____2748 =
                    let uu____2749 =
                      let uu____2750 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2750 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2749 in
                  (uu____2746, uu____2748) in
            let uu____2751 =
              let uu____2758 = FStar_List.hd xs in
              let uu____2759 = FStar_List.tl xs in (uu____2758, uu____2759) in
            match uu____2751 with
            | (x,xs1) ->
                let init1 =
                  let uu____2775 =
                    let uu____2776 =
                      let uu____2777 = extract_range x in
                      FStar_Range.end_of_range uu____2777 in
                    FStar_Range.line_of_pos uu____2776 in
                  let uu____2778 =
                    let uu____2779 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2779 in
                  (uu____2775, uu____2778) in
                let uu____2780 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2780
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3067 =
      let uu____3068 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3069 =
        let uu____3070 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3071 =
          let uu____3072 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3073 =
            let uu____3074 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3074 in
          FStar_Pprint.op_Hat_Hat uu____3072 uu____3073 in
        FStar_Pprint.op_Hat_Hat uu____3070 uu____3071 in
      FStar_Pprint.op_Hat_Hat uu____3068 uu____3069 in
    FStar_Pprint.group uu____3067
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3077 =
      let uu____3078 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3078 in
    let uu____3079 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3077 FStar_Pprint.space uu____3079
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3080  ->
    match uu____3080 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3114 =
                match uu____3114 with
                | (kwd,arg) ->
                    let uu____3121 = str "@" in
                    let uu____3122 =
                      let uu____3123 = str kwd in
                      let uu____3124 =
                        let uu____3125 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3125 in
                      FStar_Pprint.op_Hat_Hat uu____3123 uu____3124 in
                    FStar_Pprint.op_Hat_Hat uu____3121 uu____3122 in
              let uu____3126 =
                let uu____3127 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3127 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3126 in
        let uu____3132 =
          let uu____3133 =
            let uu____3134 =
              let uu____3135 =
                let uu____3136 = str doc1 in
                let uu____3137 =
                  let uu____3138 =
                    let uu____3139 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3139 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3138 in
                FStar_Pprint.op_Hat_Hat uu____3136 uu____3137 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3135 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3134 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3133 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3132
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3142 =
          let uu____3143 = str "open" in
          let uu____3144 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3143 uu____3144 in
        FStar_Pprint.group uu____3142
    | FStar_Parser_AST.Include uid ->
        let uu____3146 =
          let uu____3147 = str "include" in
          let uu____3148 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3147 uu____3148 in
        FStar_Pprint.group uu____3146
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3151 =
          let uu____3152 = str "module" in
          let uu____3153 =
            let uu____3154 =
              let uu____3155 = p_uident uid1 in
              let uu____3156 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3155 uu____3156 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3154 in
          FStar_Pprint.op_Hat_Hat uu____3152 uu____3153 in
        let uu____3157 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3151 uu____3157
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3159 =
          let uu____3160 = str "module" in
          let uu____3161 =
            let uu____3162 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3162 in
          FStar_Pprint.op_Hat_Hat uu____3160 uu____3161 in
        FStar_Pprint.group uu____3159
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3195 = str "effect" in
          let uu____3196 =
            let uu____3197 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3197 in
          FStar_Pprint.op_Hat_Hat uu____3195 uu____3196 in
        let uu____3198 =
          let uu____3199 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3199 FStar_Pprint.equals in
        let uu____3200 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3198 uu____3200
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3218 = str "type" in
        let uu____3219 = str "and" in
        precede_break_separate_map uu____3218 uu____3219 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3241 = str "let" in
          let uu____3242 =
            let uu____3243 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3243 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3241 uu____3242 in
        let uu____3244 =
          let uu____3245 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3245 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3244 p_letbinding lbs
          (fun uu____3253  ->
             match uu____3253 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3262 =
          let uu____3263 = str "val" in
          let uu____3264 =
            let uu____3265 =
              let uu____3266 = p_lident lid in
              let uu____3267 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3266 uu____3267 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3265 in
          FStar_Pprint.op_Hat_Hat uu____3263 uu____3264 in
        let uu____3268 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3262 uu____3268
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3272 =
            let uu____3273 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3273 FStar_Util.is_upper in
          if uu____3272
          then FStar_Pprint.empty
          else
            (let uu____3275 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3275 FStar_Pprint.space) in
        let uu____3276 =
          let uu____3277 =
            let uu____3278 = p_ident id in
            let uu____3279 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3278 uu____3279 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3277 in
        let uu____3280 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3276 uu____3280
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3287 = str "exception" in
        let uu____3288 =
          let uu____3289 =
            let uu____3290 = p_uident uid in
            let uu____3291 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3296 = str "of" in
                   let uu____3297 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3296 uu____3297) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3290 uu____3291 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3289 in
        FStar_Pprint.op_Hat_Hat uu____3287 uu____3288
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3299 = str "new_effect" in
        let uu____3300 =
          let uu____3301 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3301 in
        FStar_Pprint.op_Hat_Hat uu____3299 uu____3300
    | FStar_Parser_AST.SubEffect se ->
        let uu____3303 = str "sub_effect" in
        let uu____3304 =
          let uu____3305 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3305 in
        FStar_Pprint.op_Hat_Hat uu____3303 uu____3304
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3308 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3308 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3309 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3310) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___94_3327  ->
    match uu___94_3327 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3329 = str "#set-options" in
        let uu____3330 =
          let uu____3331 =
            let uu____3332 = str s in FStar_Pprint.dquotes uu____3332 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3331 in
        FStar_Pprint.op_Hat_Hat uu____3329 uu____3330
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3336 = str "#reset-options" in
        let uu____3337 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3341 =
                 let uu____3342 = str s in FStar_Pprint.dquotes uu____3342 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3341) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3336 uu____3337
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
  fun uu____3357  ->
    match uu____3357 with
    | (typedecl,fsdoc_opt) ->
        let uu____3370 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3371 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3370 uu____3371
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___95_3372  ->
    match uu___95_3372 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3387 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3403 =
          let uu____3404 = p_typ t in prefix2 FStar_Pprint.equals uu____3404 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3448 =
          match uu____3448 with
          | (lid1,t,doc_opt) ->
              let uu____3464 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3464 in
        let p_fields uu____3478 =
          let uu____3479 =
            let uu____3480 =
              let uu____3481 =
                let uu____3482 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3482 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3481 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3480 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3479 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3546 =
          match uu____3546 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3572 =
                  let uu____3573 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3573 in
                FStar_Range.extend_to_end_of_line uu____3572 in
              let p_constructorBranch decl =
                let uu____3606 =
                  let uu____3607 =
                    let uu____3608 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3608 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3607 in
                FStar_Pprint.group uu____3606 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3628 =
          let uu____3629 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3629 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3644  ->
             let uu____3645 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3645)
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
            let uu____3660 = p_ident lid in
            let uu____3661 =
              let uu____3662 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3662 in
            FStar_Pprint.op_Hat_Hat uu____3660 uu____3661
          else
            (let binders_doc =
               let uu____3665 = p_typars bs in
               let uu____3666 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3670 =
                        let uu____3671 =
                          let uu____3672 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3672 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3671 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3670) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3665 uu____3666 in
             let uu____3673 = p_ident lid in
             let uu____3674 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3673 binders_doc uu____3674)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3675  ->
    match uu____3675 with
    | (lid,t,doc_opt) ->
        let uu____3691 =
          let uu____3692 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3693 =
            let uu____3694 = p_lident lid in
            let uu____3695 =
              let uu____3696 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3696 in
            FStar_Pprint.op_Hat_Hat uu____3694 uu____3695 in
          FStar_Pprint.op_Hat_Hat uu____3692 uu____3693 in
        FStar_Pprint.group uu____3691
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3697  ->
    match uu____3697 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3725 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3726 =
          let uu____3727 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3728 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3733 =
                   let uu____3734 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3734 in
                 let uu____3735 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3733 uu____3735) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3727 uu____3728 in
        FStar_Pprint.op_Hat_Hat uu____3725 uu____3726
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3736  ->
    match uu____3736 with
    | (pat,e) ->
        let pat_doc =
          let uu____3744 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____3755 =
                  let uu____3756 =
                    let uu____3757 =
                      let uu____3758 =
                        let uu____3759 = p_tmArrow p_tmNoEq t in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3759 in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3758 in
                    FStar_Pprint.group uu____3757 in
                  FStar_Pprint.op_Hat_Hat break1 uu____3756 in
                (pat1, uu____3755)
            | uu____3760 -> (pat, FStar_Pprint.empty) in
          match uu____3744 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____3764);
                      FStar_Parser_AST.prange = uu____3765;_},pats)
                   ->
                   let uu____3775 = p_lident x in
                   let uu____3776 =
                     let uu____3777 =
                       separate_map_or_flow break1 p_atomicPattern pats in
                     FStar_Pprint.op_Hat_Hat uu____3777 ascr_doc in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____3775 uu____3776
                     FStar_Pprint.equals
               | uu____3778 ->
                   let uu____3779 =
                     let uu____3780 = p_tuplePattern pat1 in
                     let uu____3781 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals in
                     FStar_Pprint.op_Hat_Hat uu____3780 uu____3781 in
                   FStar_Pprint.group uu____3779) in
        let uu____3782 = p_term e in prefix2 pat_doc uu____3782
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___96_3783  ->
    match uu___96_3783 with
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
        let uu____3808 = p_uident uid in
        let uu____3809 = p_binders true bs in
        let uu____3810 =
          let uu____3811 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3811 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3808 uu____3809 uu____3810
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
          let uu____3820 =
            let uu____3821 =
              let uu____3822 =
                let uu____3823 = p_uident uid in
                let uu____3824 = p_binders true bs in
                let uu____3825 =
                  let uu____3826 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3826 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3823 uu____3824 uu____3825 in
              FStar_Pprint.group uu____3822 in
            let uu____3827 =
              let uu____3828 = str "with" in
              let uu____3829 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3828 uu____3829 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3821 uu____3827 in
          braces_with_nesting uu____3820
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3859 =
          let uu____3860 = p_lident lid in
          let uu____3861 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3860 uu____3861 in
        let uu____3862 = p_simpleTerm e in prefix2 uu____3859 uu____3862
    | uu____3863 ->
        let uu____3864 =
          let uu____3865 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3865 in
        failwith uu____3864
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____3920 =
        match uu____3920 with
        | (kwd,t) ->
            let uu____3927 =
              let uu____3928 = str kwd in
              let uu____3929 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3928 uu____3929 in
            let uu____3930 = p_simpleTerm t in prefix2 uu____3927 uu____3930 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____3935 =
      let uu____3936 =
        let uu____3937 = p_quident lift.FStar_Parser_AST.msource in
        let uu____3938 =
          let uu____3939 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3939 in
        FStar_Pprint.op_Hat_Hat uu____3937 uu____3938 in
      let uu____3940 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____3936 uu____3940 in
    let uu____3941 =
      let uu____3942 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3942 in
    FStar_Pprint.op_Hat_Hat uu____3935 uu____3941
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___97_3943  ->
    match uu___97_3943 with
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
    let uu____3945 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____3945
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___98_3946  ->
    match uu___98_3946 with
    | FStar_Parser_AST.Rec  ->
        let uu____3947 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3947
    | FStar_Parser_AST.Mutable  ->
        let uu____3948 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3948
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___99_3949  ->
    match uu___99_3949 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____3954 =
          let uu____3955 =
            let uu____3956 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____3956 in
          FStar_Pprint.separate_map uu____3955 p_tuplePattern pats in
        FStar_Pprint.group uu____3954
    | uu____3957 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____3964 =
          let uu____3965 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____3965 p_constructorPattern pats in
        FStar_Pprint.group uu____3964
    | uu____3966 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____3969;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____3974 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____3975 = p_constructorPattern hd1 in
        let uu____3976 = p_constructorPattern tl1 in
        infix0 uu____3974 uu____3975 uu____3976
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____3978;_},pats)
        ->
        let uu____3984 = p_quident uid in
        let uu____3985 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____3984 uu____3985
    | uu____3986 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____3990 =
          let uu____3995 =
            let uu____3996 = unparen t in uu____3996.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____3995) in
        (match uu____3990 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4001;
               FStar_Parser_AST.blevel = uu____4002;
               FStar_Parser_AST.aqual = uu____4003;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4009 =
               let uu____4010 = p_ident lid in
               p_refinement aqual uu____4010 t1 phi in
             soft_parens_with_nesting uu____4009
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4012;
               FStar_Parser_AST.blevel = uu____4013;
               FStar_Parser_AST.aqual = uu____4014;_},phi))
             ->
             let uu____4016 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4016
         | uu____4017 ->
             let uu____4022 =
               let uu____4023 = p_tuplePattern pat in
               let uu____4024 =
                 let uu____4025 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4026 =
                   let uu____4027 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4027 in
                 FStar_Pprint.op_Hat_Hat uu____4025 uu____4026 in
               FStar_Pprint.op_Hat_Hat uu____4023 uu____4024 in
             soft_parens_with_nesting uu____4022)
    | FStar_Parser_AST.PatList pats ->
        let uu____4031 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4031 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4046 =
          match uu____4046 with
          | (lid,pat) ->
              let uu____4053 = p_qlident lid in
              let uu____4054 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4053 uu____4054 in
        let uu____4055 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4055
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4065 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4066 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4067 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4065 uu____4066 uu____4067
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4078 =
          let uu____4079 =
            let uu____4080 = str (FStar_Ident.text_of_id op) in
            let uu____4081 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4080 uu____4081 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4079 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4078
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4089 = FStar_Pprint.optional p_aqual aqual in
        let uu____4090 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4089 uu____4090
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4092 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4095;
           FStar_Parser_AST.prange = uu____4096;_},uu____4097)
        ->
        let uu____4102 = p_tuplePattern p in
        soft_parens_with_nesting uu____4102
    | FStar_Parser_AST.PatTuple (uu____4103,false ) ->
        let uu____4108 = p_tuplePattern p in
        soft_parens_with_nesting uu____4108
    | uu____4109 ->
        let uu____4110 =
          let uu____4111 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4111 in
        failwith uu____4110
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4115 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4116 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4115 uu____4116
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4121 =
              let uu____4122 = unparen t in uu____4122.FStar_Parser_AST.tm in
            match uu____4121 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4125;
                   FStar_Parser_AST.blevel = uu____4126;
                   FStar_Parser_AST.aqual = uu____4127;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4129 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4129 t1 phi
            | uu____4130 ->
                let uu____4131 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4132 =
                  let uu____4133 = p_lident lid in
                  let uu____4134 =
                    let uu____4135 =
                      let uu____4136 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4137 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4136 uu____4137 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4135 in
                  FStar_Pprint.op_Hat_Hat uu____4133 uu____4134 in
                FStar_Pprint.op_Hat_Hat uu____4131 uu____4132 in
          if is_atomic
          then
            let uu____4138 =
              let uu____4139 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4139 in
            FStar_Pprint.group uu____4138
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4141 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4147 =
            let uu____4148 = unparen t in uu____4148.FStar_Parser_AST.tm in
          (match uu____4147 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4150;
                  FStar_Parser_AST.blevel = uu____4151;
                  FStar_Parser_AST.aqual = uu____4152;_},phi)
               ->
               if is_atomic
               then
                 let uu____4154 =
                   let uu____4155 =
                     let uu____4156 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4156 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4155 in
                 FStar_Pprint.group uu____4154
               else
                 (let uu____4158 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4158)
           | uu____4159 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4167 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4168 =
            let uu____4169 =
              let uu____4170 =
                let uu____4171 = p_appTerm t in
                let uu____4172 =
                  let uu____4173 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4173 in
                FStar_Pprint.op_Hat_Hat uu____4171 uu____4172 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4170 in
            FStar_Pprint.op_Hat_Hat binder uu____4169 in
          FStar_Pprint.op_Hat_Hat uu____4167 uu____4168
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
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id
and p_term: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4187 =
      let uu____4188 = unparen e in uu____4188.FStar_Parser_AST.tm in
    match uu____4187 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4191 =
          let uu____4192 =
            let uu____4193 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4193 FStar_Pprint.semi in
          FStar_Pprint.group uu____4192 in
        let uu____4194 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4191 uu____4194
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4198 =
          let uu____4199 =
            let uu____4200 =
              let uu____4201 = p_lident x in
              let uu____4202 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4201 uu____4202 in
            let uu____4203 =
              let uu____4204 = p_noSeqTerm e1 in
              let uu____4205 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4204 uu____4205 in
            op_Hat_Slash_Plus_Hat uu____4200 uu____4203 in
          FStar_Pprint.group uu____4199 in
        let uu____4206 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4198 uu____4206
    | uu____4207 ->
        let uu____4208 = p_noSeqTerm e in FStar_Pprint.group uu____4208
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4211 =
      let uu____4212 = unparen e in uu____4212.FStar_Parser_AST.tm in
    match uu____4211 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4217 =
          let uu____4218 = p_tmIff e1 in
          let uu____4219 =
            let uu____4220 =
              let uu____4221 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4221 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4220 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4218 uu____4219 in
        FStar_Pprint.group uu____4217
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4227 =
          let uu____4228 = p_tmIff e1 in
          let uu____4229 =
            let uu____4230 =
              let uu____4231 =
                let uu____4232 = p_typ t in
                let uu____4233 =
                  let uu____4234 = str "by" in
                  let uu____4235 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4234 uu____4235 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4232 uu____4233 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4231 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4230 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4228 uu____4229 in
        FStar_Pprint.group uu____4227
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4236;_},e1::e2::e3::[])
        ->
        let uu____4242 =
          let uu____4243 =
            let uu____4244 =
              let uu____4245 = p_atomicTermNotQUident e1 in
              let uu____4246 =
                let uu____4247 =
                  let uu____4248 =
                    let uu____4249 = p_term e2 in
                    soft_parens_with_nesting uu____4249 in
                  let uu____4250 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4248 uu____4250 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4247 in
              FStar_Pprint.op_Hat_Hat uu____4245 uu____4246 in
            FStar_Pprint.group uu____4244 in
          let uu____4251 =
            let uu____4252 = p_noSeqTerm e3 in jump2 uu____4252 in
          FStar_Pprint.op_Hat_Hat uu____4243 uu____4251 in
        FStar_Pprint.group uu____4242
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4253;_},e1::e2::e3::[])
        ->
        let uu____4259 =
          let uu____4260 =
            let uu____4261 =
              let uu____4262 = p_atomicTermNotQUident e1 in
              let uu____4263 =
                let uu____4264 =
                  let uu____4265 =
                    let uu____4266 = p_term e2 in
                    soft_brackets_with_nesting uu____4266 in
                  let uu____4267 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4265 uu____4267 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4264 in
              FStar_Pprint.op_Hat_Hat uu____4262 uu____4263 in
            FStar_Pprint.group uu____4261 in
          let uu____4268 =
            let uu____4269 = p_noSeqTerm e3 in jump2 uu____4269 in
          FStar_Pprint.op_Hat_Hat uu____4260 uu____4268 in
        FStar_Pprint.group uu____4259
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4279 =
          let uu____4280 = str "requires" in
          let uu____4281 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4280 uu____4281 in
        FStar_Pprint.group uu____4279
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4291 =
          let uu____4292 = str "ensures" in
          let uu____4293 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4292 uu____4293 in
        FStar_Pprint.group uu____4291
    | FStar_Parser_AST.Attributes es ->
        let uu____4297 =
          let uu____4298 = str "attributes" in
          let uu____4299 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4298 uu____4299 in
        FStar_Pprint.group uu____4297
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4303 = is_unit e3 in
        if uu____4303
        then
          let uu____4304 =
            let uu____4305 =
              let uu____4306 = str "if" in
              let uu____4307 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4306 uu____4307 in
            let uu____4308 =
              let uu____4309 = str "then" in
              let uu____4310 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4309 uu____4310 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4305 uu____4308 in
          FStar_Pprint.group uu____4304
        else
          (let e2_doc =
             let uu____4313 =
               let uu____4314 = unparen e2 in uu____4314.FStar_Parser_AST.tm in
             match uu____4313 with
             | FStar_Parser_AST.If (uu____4315,uu____4316,e31) when
                 is_unit e31 ->
                 let uu____4318 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4318
             | uu____4319 -> p_noSeqTerm e2 in
           let uu____4320 =
             let uu____4321 =
               let uu____4322 = str "if" in
               let uu____4323 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4322 uu____4323 in
             let uu____4324 =
               let uu____4325 =
                 let uu____4326 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4326 e2_doc in
               let uu____4327 =
                 let uu____4328 = str "else" in
                 let uu____4329 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4328 uu____4329 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4325 uu____4327 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4321 uu____4324 in
           FStar_Pprint.group uu____4320)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4352 =
          let uu____4353 =
            let uu____4354 = str "try" in
            let uu____4355 = p_noSeqTerm e1 in prefix2 uu____4354 uu____4355 in
          let uu____4356 =
            let uu____4357 = str "with" in
            let uu____4358 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4357 uu____4358 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4353 uu____4356 in
        FStar_Pprint.group uu____4352
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4389 =
          let uu____4390 =
            let uu____4391 = str "match" in
            let uu____4392 = p_noSeqTerm e1 in
            let uu____4393 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4391 uu____4392 uu____4393 in
          let uu____4394 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4390 uu____4394 in
        FStar_Pprint.group uu____4389
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4405 =
          let uu____4406 =
            let uu____4407 = str "let open" in
            let uu____4408 = p_quident uid in
            let uu____4409 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4407 uu____4408 uu____4409 in
          let uu____4410 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4406 uu____4410 in
        FStar_Pprint.group uu____4405
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4427 = str "let" in
          let uu____4428 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4427 uu____4428 in
        let uu____4429 =
          let uu____4430 =
            let uu____4431 =
              let uu____4432 = str "and" in
              precede_break_separate_map let_doc uu____4432 p_letbinding lbs in
            let uu____4437 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4431 uu____4437 in
          FStar_Pprint.group uu____4430 in
        let uu____4438 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4429 uu____4438
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4441;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4444;
                                                         FStar_Parser_AST.level
                                                           = uu____4445;_})
        when matches_var maybe_x x ->
        let uu____4472 =
          let uu____4473 = str "function" in
          let uu____4474 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4473 uu____4474 in
        FStar_Pprint.group uu____4472
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4485 =
          let uu____4486 = p_lident id in
          let uu____4487 =
            let uu____4488 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4488 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4486 uu____4487 in
        FStar_Pprint.group uu____4485
    | uu____4489 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4492 =
      let uu____4493 = unparen e in uu____4493.FStar_Parser_AST.tm in
    match uu____4492 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4509 =
          let uu____4510 =
            let uu____4511 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4511 FStar_Pprint.space in
          let uu____4512 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4510 uu____4512 FStar_Pprint.dot in
        let uu____4513 =
          let uu____4514 = p_trigger trigger in
          let uu____4515 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4514 uu____4515 in
        prefix2 uu____4509 uu____4513
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4531 =
          let uu____4532 =
            let uu____4533 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4533 FStar_Pprint.space in
          let uu____4534 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4532 uu____4534 FStar_Pprint.dot in
        let uu____4535 =
          let uu____4536 = p_trigger trigger in
          let uu____4537 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4536 uu____4537 in
        prefix2 uu____4531 uu____4535
    | uu____4538 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4540 =
      let uu____4541 = unparen e in uu____4541.FStar_Parser_AST.tm in
    match uu____4540 with
    | FStar_Parser_AST.QForall uu____4542 -> str "forall"
    | FStar_Parser_AST.QExists uu____4555 -> str "exists"
    | uu____4568 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___100_4569  ->
    match uu___100_4569 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4581 =
          let uu____4582 =
            let uu____4583 = str "pattern" in
            let uu____4584 =
              let uu____4585 =
                let uu____4586 = p_disjunctivePats pats in jump2 uu____4586 in
              let uu____4587 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4585 uu____4587 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4583 uu____4584 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4582 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4581
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4593 = str "\\/" in
    FStar_Pprint.separate_map uu____4593 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4599 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4599
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4601 =
      let uu____4602 = unparen e in uu____4602.FStar_Parser_AST.tm in
    match uu____4601 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4609 =
          let uu____4610 = str "fun" in
          let uu____4611 =
            let uu____4612 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4612 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4610 uu____4611 in
        let uu____4613 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4609 uu____4613
    | uu____4614 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4617  ->
    match uu____4617 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4636 =
            let uu____4637 = unparen e in uu____4637.FStar_Parser_AST.tm in
          match uu____4636 with
          | FStar_Parser_AST.Match uu____4640 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4655 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4671);
                 FStar_Parser_AST.prange = uu____4672;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4674);
                                                               FStar_Parser_AST.range
                                                                 = uu____4675;
                                                               FStar_Parser_AST.level
                                                                 = uu____4676;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4703 -> (fun x  -> x) in
        let uu____4705 =
          let uu____4706 =
            let uu____4707 =
              let uu____4708 =
                let uu____4709 =
                  let uu____4710 = p_disjunctivePattern pat in
                  let uu____4711 =
                    let uu____4712 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4712 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4710 uu____4711 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4709 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4708 in
            FStar_Pprint.group uu____4707 in
          let uu____4713 =
            let uu____4714 = p_term e in maybe_paren uu____4714 in
          op_Hat_Slash_Plus_Hat uu____4706 uu____4713 in
        FStar_Pprint.group uu____4705
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___101_4715  ->
    match uu___101_4715 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4719 = str "when" in
        let uu____4720 =
          let uu____4721 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4721 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4719 uu____4720
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4723 =
      let uu____4724 = unparen e in uu____4724.FStar_Parser_AST.tm in
    match uu____4723 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4725;_},e1::e2::[])
        ->
        let uu____4730 = str "<==>" in
        let uu____4731 = p_tmImplies e1 in
        let uu____4732 = p_tmIff e2 in
        infix0 uu____4730 uu____4731 uu____4732
    | uu____4733 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4735 =
      let uu____4736 = unparen e in uu____4736.FStar_Parser_AST.tm in
    match uu____4735 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4737;_},e1::e2::[])
        ->
        let uu____4742 = str "==>" in
        let uu____4743 = p_tmArrow p_tmFormula e1 in
        let uu____4744 = p_tmImplies e2 in
        infix0 uu____4742 uu____4743 uu____4744
    | uu____4745 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4750 =
        let uu____4751 = unparen e in uu____4751.FStar_Parser_AST.tm in
      match uu____4750 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4758 =
            let uu____4759 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4764 = p_binder false b in
                   let uu____4765 =
                     let uu____4766 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4766 in
                   FStar_Pprint.op_Hat_Hat uu____4764 uu____4765) bs in
            let uu____4767 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4759 uu____4767 in
          FStar_Pprint.group uu____4758
      | uu____4768 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4770 =
      let uu____4771 = unparen e in uu____4771.FStar_Parser_AST.tm in
    match uu____4770 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4772;_},e1::e2::[])
        ->
        let uu____4777 = str "\\/" in
        let uu____4778 = p_tmFormula e1 in
        let uu____4779 = p_tmConjunction e2 in
        infix0 uu____4777 uu____4778 uu____4779
    | uu____4780 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4782 =
      let uu____4783 = unparen e in uu____4783.FStar_Parser_AST.tm in
    match uu____4782 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4784;_},e1::e2::[])
        ->
        let uu____4789 = str "/\\" in
        let uu____4790 = p_tmConjunction e1 in
        let uu____4791 = p_tmTuple e2 in
        infix0 uu____4789 uu____4790 uu____4791
    | uu____4792 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4795 =
      let uu____4796 = unparen e in uu____4796.FStar_Parser_AST.tm in
    match uu____4795 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4811 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4811
          (fun uu____4819  ->
             match uu____4819 with | (e1,uu____4825) -> p_tmEq e1) args
    | uu____4826 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4831 =
             let uu____4832 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4832 in
           FStar_Pprint.group uu____4831)
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
      let uu____4877 =
        let uu____4878 = unparen e in uu____4878.FStar_Parser_AST.tm in
      match uu____4877 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____4885 = levels op1 in
          (match uu____4885 with
           | (left1,mine,right1) ->
               let uu____4895 =
                 let uu____4896 = FStar_All.pipe_left str op1 in
                 let uu____4897 = p_tmEq' left1 e1 in
                 let uu____4898 = p_tmEq' right1 e2 in
                 infix0 uu____4896 uu____4897 uu____4898 in
               paren_if curr mine uu____4895)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4899;_},e1::e2::[])
          ->
          let uu____4904 =
            let uu____4905 = p_tmEq e1 in
            let uu____4906 =
              let uu____4907 =
                let uu____4908 =
                  let uu____4909 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4909 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4908 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4907 in
            FStar_Pprint.op_Hat_Hat uu____4905 uu____4906 in
          FStar_Pprint.group uu____4904
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4910;_},e1::[])
          ->
          let uu____4914 = levels "-" in
          (match uu____4914 with
           | (left1,mine,right1) ->
               let uu____4924 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4924)
      | uu____4925 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____4980 =
        let uu____4981 = unparen e in uu____4981.FStar_Parser_AST.tm in
      match uu____4980 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____4984)::(e2,uu____4986)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5006 = is_list e in Prims.op_Negation uu____5006)
          ->
          let op = "::" in
          let uu____5008 = levels op in
          (match uu____5008 with
           | (left1,mine,right1) ->
               let uu____5018 =
                 let uu____5019 = str op in
                 let uu____5020 = p_tmNoEq' left1 e1 in
                 let uu____5021 = p_tmNoEq' right1 e2 in
                 infix0 uu____5019 uu____5020 uu____5021 in
               paren_if curr mine uu____5018)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5029 = levels op in
          (match uu____5029 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5043 = p_binder false b in
                 let uu____5044 =
                   let uu____5045 =
                     let uu____5046 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5046 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5045 in
                 FStar_Pprint.op_Hat_Hat uu____5043 uu____5044 in
               let uu____5047 =
                 let uu____5048 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5049 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5048 uu____5049 in
               paren_if curr mine uu____5047)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5056 = levels op1 in
          (match uu____5056 with
           | (left1,mine,right1) ->
               let uu____5066 =
                 let uu____5067 = str op1 in
                 let uu____5068 = p_tmNoEq' left1 e1 in
                 let uu____5069 = p_tmNoEq' right1 e2 in
                 infix0 uu____5067 uu____5068 uu____5069 in
               paren_if curr mine uu____5066)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5072 =
            let uu____5073 = p_lidentOrUnderscore lid in
            let uu____5074 =
              let uu____5075 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5075 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5073 uu____5074 in
          FStar_Pprint.group uu____5072
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5096 =
            let uu____5097 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5098 =
              let uu____5099 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5099 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5097 uu____5098 in
          braces_with_nesting uu____5096
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5104;_},e1::[])
          ->
          let uu____5108 =
            let uu____5109 = str "~" in
            let uu____5110 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5109 uu____5110 in
          FStar_Pprint.group uu____5108
      | uu____5111 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5113 = p_appTerm e in
    let uu____5114 =
      let uu____5115 =
        let uu____5116 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5116 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5115 in
    FStar_Pprint.op_Hat_Hat uu____5113 uu____5114
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5121 =
            let uu____5122 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5122 t phi in
          soft_parens_with_nesting uu____5121
      | FStar_Parser_AST.TAnnotated uu____5123 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5128 ->
          let uu____5129 =
            let uu____5130 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5130 in
          failwith uu____5129
      | FStar_Parser_AST.TVariable uu____5131 ->
          let uu____5132 =
            let uu____5133 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5133 in
          failwith uu____5132
      | FStar_Parser_AST.NoName uu____5134 ->
          let uu____5135 =
            let uu____5136 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5136 in
          failwith uu____5135
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5137  ->
    match uu____5137 with
    | (lid,e) ->
        let uu____5144 =
          let uu____5145 = p_qlident lid in
          let uu____5146 =
            let uu____5147 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5147 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5145 uu____5146 in
        FStar_Pprint.group uu____5144
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5149 =
      let uu____5150 = unparen e in uu____5150.FStar_Parser_AST.tm in
    match uu____5149 with
    | FStar_Parser_AST.App uu____5151 when is_general_application e ->
        let uu____5158 = head_and_args e in
        (match uu____5158 with
         | (head1,args) ->
             let uu____5183 =
               let uu____5194 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5194
               then
                 let uu____5215 =
                   FStar_Util.take
                     (fun uu____5239  ->
                        match uu____5239 with
                        | (uu____5244,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5215 with
                 | (fs_typ_args,args1) ->
                     let uu____5282 =
                       let uu____5283 = p_indexingTerm head1 in
                       let uu____5284 =
                         let uu____5285 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5285 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5283 uu____5284 in
                     (uu____5282, args1)
               else
                 (let uu____5297 = p_indexingTerm head1 in (uu____5297, args)) in
             (match uu____5183 with
              | (head_doc,args1) ->
                  let uu____5318 =
                    let uu____5319 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5319 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5318))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5339 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5339)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5357 =
               let uu____5358 = p_quident lid in
               let uu____5359 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5358 uu____5359 in
             FStar_Pprint.group uu____5357
         | hd1::tl1 ->
             let uu____5376 =
               let uu____5377 =
                 let uu____5378 =
                   let uu____5379 = p_quident lid in
                   let uu____5380 = p_argTerm hd1 in
                   prefix2 uu____5379 uu____5380 in
                 FStar_Pprint.group uu____5378 in
               let uu____5381 =
                 let uu____5382 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5382 in
               FStar_Pprint.op_Hat_Hat uu____5377 uu____5381 in
             FStar_Pprint.group uu____5376)
    | uu____5387 -> p_indexingTerm e
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
         (let uu____5396 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5396 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5398 = str "#" in
        let uu____5399 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5398 uu____5399
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5401  ->
    match uu____5401 with | (e,uu____5407) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5412 =
        let uu____5413 = unparen e in uu____5413.FStar_Parser_AST.tm in
      match uu____5412 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5414;_},e1::e2::[])
          ->
          let uu____5419 =
            let uu____5420 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5421 =
              let uu____5422 =
                let uu____5423 = p_term e2 in
                soft_parens_with_nesting uu____5423 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5422 in
            FStar_Pprint.op_Hat_Hat uu____5420 uu____5421 in
          FStar_Pprint.group uu____5419
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5424;_},e1::e2::[])
          ->
          let uu____5429 =
            let uu____5430 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5431 =
              let uu____5432 =
                let uu____5433 = p_term e2 in
                soft_brackets_with_nesting uu____5433 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5432 in
            FStar_Pprint.op_Hat_Hat uu____5430 uu____5431 in
          FStar_Pprint.group uu____5429
      | uu____5434 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5437 =
      let uu____5438 = unparen e in uu____5438.FStar_Parser_AST.tm in
    match uu____5437 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5441 = p_quident lid in
        let uu____5442 =
          let uu____5443 =
            let uu____5444 = p_term e1 in soft_parens_with_nesting uu____5444 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5443 in
        FStar_Pprint.op_Hat_Hat uu____5441 uu____5442
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5450 = str (FStar_Ident.text_of_id op) in
        let uu____5451 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5450 uu____5451
    | uu____5452 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5454 =
      let uu____5455 = unparen e in uu____5455.FStar_Parser_AST.tm in
    match uu____5454 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5460 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5467 = str (FStar_Ident.text_of_id op) in
        let uu____5468 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5467 uu____5468
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5472 =
          let uu____5473 =
            let uu____5474 = str (FStar_Ident.text_of_id op) in
            let uu____5475 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5474 uu____5475 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5473 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5472
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5490 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5491 =
          let uu____5492 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5493 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5492 p_tmEq uu____5493 in
        let uu____5500 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5490 uu____5491 uu____5500
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5503 =
          let uu____5504 = p_atomicTermNotQUident e1 in
          let uu____5505 =
            let uu____5506 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5506 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5504 uu____5505 in
        FStar_Pprint.group uu____5503
    | uu____5507 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5509 =
      let uu____5510 = unparen e in uu____5510.FStar_Parser_AST.tm in
    match uu____5509 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5514 = p_quident constr_lid in
        let uu____5515 =
          let uu____5516 =
            let uu____5517 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5517 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5516 in
        FStar_Pprint.op_Hat_Hat uu____5514 uu____5515
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5519 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5519 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5521 = p_term e1 in soft_parens_with_nesting uu____5521
    | uu____5522 when is_array e ->
        let es = extract_from_list e in
        let uu____5526 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5527 =
          let uu____5528 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5528 p_noSeqTerm es in
        let uu____5529 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5526 uu____5527 uu____5529
    | uu____5530 when is_list e ->
        let uu____5531 =
          let uu____5532 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5533 = extract_from_list e in
          separate_map_or_flow uu____5532 p_noSeqTerm uu____5533 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5531 FStar_Pprint.rbracket
    | uu____5536 when is_lex_list e ->
        let uu____5537 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5538 =
          let uu____5539 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5540 = extract_from_list e in
          separate_map_or_flow uu____5539 p_noSeqTerm uu____5540 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5537 uu____5538 FStar_Pprint.rbracket
    | uu____5543 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5547 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5548 =
          let uu____5549 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5549 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5547 uu____5548 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5553 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5554 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5553 uu____5554
    | FStar_Parser_AST.Op (op,args) when
        let uu____5561 = handleable_op op args in
        Prims.op_Negation uu____5561 ->
        let uu____5562 =
          let uu____5563 =
            let uu____5564 =
              let uu____5565 =
                let uu____5566 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5566
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5565 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5564 in
          Prims.strcat "Operation " uu____5563 in
        failwith uu____5562
    | FStar_Parser_AST.Uvar uu____5567 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5568 = p_term e in soft_parens_with_nesting uu____5568
    | FStar_Parser_AST.Const uu____5569 ->
        let uu____5570 = p_term e in soft_parens_with_nesting uu____5570
    | FStar_Parser_AST.Op uu____5571 ->
        let uu____5578 = p_term e in soft_parens_with_nesting uu____5578
    | FStar_Parser_AST.Tvar uu____5579 ->
        let uu____5580 = p_term e in soft_parens_with_nesting uu____5580
    | FStar_Parser_AST.Var uu____5581 ->
        let uu____5582 = p_term e in soft_parens_with_nesting uu____5582
    | FStar_Parser_AST.Name uu____5583 ->
        let uu____5584 = p_term e in soft_parens_with_nesting uu____5584
    | FStar_Parser_AST.Construct uu____5585 ->
        let uu____5596 = p_term e in soft_parens_with_nesting uu____5596
    | FStar_Parser_AST.Abs uu____5597 ->
        let uu____5604 = p_term e in soft_parens_with_nesting uu____5604
    | FStar_Parser_AST.App uu____5605 ->
        let uu____5612 = p_term e in soft_parens_with_nesting uu____5612
    | FStar_Parser_AST.Let uu____5613 ->
        let uu____5626 = p_term e in soft_parens_with_nesting uu____5626
    | FStar_Parser_AST.LetOpen uu____5627 ->
        let uu____5632 = p_term e in soft_parens_with_nesting uu____5632
    | FStar_Parser_AST.Seq uu____5633 ->
        let uu____5638 = p_term e in soft_parens_with_nesting uu____5638
    | FStar_Parser_AST.Bind uu____5639 ->
        let uu____5646 = p_term e in soft_parens_with_nesting uu____5646
    | FStar_Parser_AST.If uu____5647 ->
        let uu____5654 = p_term e in soft_parens_with_nesting uu____5654
    | FStar_Parser_AST.Match uu____5655 ->
        let uu____5670 = p_term e in soft_parens_with_nesting uu____5670
    | FStar_Parser_AST.TryWith uu____5671 ->
        let uu____5686 = p_term e in soft_parens_with_nesting uu____5686
    | FStar_Parser_AST.Ascribed uu____5687 ->
        let uu____5696 = p_term e in soft_parens_with_nesting uu____5696
    | FStar_Parser_AST.Record uu____5697 ->
        let uu____5710 = p_term e in soft_parens_with_nesting uu____5710
    | FStar_Parser_AST.Project uu____5711 ->
        let uu____5716 = p_term e in soft_parens_with_nesting uu____5716
    | FStar_Parser_AST.Product uu____5717 ->
        let uu____5724 = p_term e in soft_parens_with_nesting uu____5724
    | FStar_Parser_AST.Sum uu____5725 ->
        let uu____5732 = p_term e in soft_parens_with_nesting uu____5732
    | FStar_Parser_AST.QForall uu____5733 ->
        let uu____5746 = p_term e in soft_parens_with_nesting uu____5746
    | FStar_Parser_AST.QExists uu____5747 ->
        let uu____5760 = p_term e in soft_parens_with_nesting uu____5760
    | FStar_Parser_AST.Refine uu____5761 ->
        let uu____5766 = p_term e in soft_parens_with_nesting uu____5766
    | FStar_Parser_AST.NamedTyp uu____5767 ->
        let uu____5772 = p_term e in soft_parens_with_nesting uu____5772
    | FStar_Parser_AST.Requires uu____5773 ->
        let uu____5780 = p_term e in soft_parens_with_nesting uu____5780
    | FStar_Parser_AST.Ensures uu____5781 ->
        let uu____5788 = p_term e in soft_parens_with_nesting uu____5788
    | FStar_Parser_AST.Assign uu____5789 ->
        let uu____5794 = p_term e in soft_parens_with_nesting uu____5794
    | FStar_Parser_AST.Attributes uu____5795 ->
        let uu____5798 = p_term e in soft_parens_with_nesting uu____5798
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___104_5799  ->
    match uu___104_5799 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5803 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5803
    | FStar_Const.Const_string (s,uu____5805) ->
        let uu____5806 = str s in FStar_Pprint.dquotes uu____5806
    | FStar_Const.Const_bytearray (bytes,uu____5808) ->
        let uu____5813 =
          let uu____5814 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5814 in
        let uu____5815 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5813 uu____5815
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___102_5833 =
          match uu___102_5833 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___103_5837 =
          match uu___103_5837 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5848  ->
               match uu____5848 with
               | (s,w) ->
                   let uu____5855 = signedness s in
                   let uu____5856 = width w in
                   FStar_Pprint.op_Hat_Hat uu____5855 uu____5856)
            sign_width_opt in
        let uu____5857 = str repr in
        FStar_Pprint.op_Hat_Hat uu____5857 ending
    | FStar_Const.Const_range r ->
        let uu____5859 = FStar_Range.string_of_range r in str uu____5859
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5861 = p_quident lid in
        let uu____5862 =
          let uu____5863 =
            let uu____5864 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5864 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5863 in
        FStar_Pprint.op_Hat_Hat uu____5861 uu____5862
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5866 = str "u#" in
    let uu____5867 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____5866 uu____5867
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5869 =
      let uu____5870 = unparen u in uu____5870.FStar_Parser_AST.tm in
    match uu____5869 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5871;_},u1::u2::[])
        ->
        let uu____5876 =
          let uu____5877 = p_universeFrom u1 in
          let uu____5878 =
            let uu____5879 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5879 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5877 uu____5878 in
        FStar_Pprint.group uu____5876
    | FStar_Parser_AST.App uu____5880 ->
        let uu____5887 = head_and_args u in
        (match uu____5887 with
         | (head1,args) ->
             let uu____5912 =
               let uu____5913 = unparen head1 in
               uu____5913.FStar_Parser_AST.tm in
             (match uu____5912 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____5915 =
                    let uu____5916 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____5917 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____5925  ->
                           match uu____5925 with
                           | (u1,uu____5931) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____5916 uu____5917 in
                  FStar_Pprint.group uu____5915
              | uu____5932 ->
                  let uu____5933 =
                    let uu____5934 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____5934 in
                  failwith uu____5933))
    | uu____5935 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5937 =
      let uu____5938 = unparen u in uu____5938.FStar_Parser_AST.tm in
    match uu____5937 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____5961 = p_universeFrom u1 in
        soft_parens_with_nesting uu____5961
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5962;_},uu____5963::uu____5964::[])
        ->
        let uu____5967 = p_universeFrom u in
        soft_parens_with_nesting uu____5967
    | FStar_Parser_AST.App uu____5968 ->
        let uu____5975 = p_universeFrom u in
        soft_parens_with_nesting uu____5975
    | uu____5976 ->
        let uu____5977 =
          let uu____5978 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____5978 in
        failwith uu____5977
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
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____6011,decls) ->
           let uu____6017 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6017
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6026,decls,uu____6028) ->
           let uu____6033 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6033
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6076  ->
         match uu____6076 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6118,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6124,decls,uu____6126) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6162 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6175;
                 FStar_Parser_AST.doc = uu____6176;
                 FStar_Parser_AST.quals = uu____6177;
                 FStar_Parser_AST.attrs = uu____6178;_}::uu____6179 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6185 =
                   let uu____6188 =
                     let uu____6191 = FStar_List.tl ds in d :: uu____6191 in
                   d0 :: uu____6188 in
                 (uu____6185, (d0.FStar_Parser_AST.drange))
             | uu____6196 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6162 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6257 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6257 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6350 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6350, comments1))))))