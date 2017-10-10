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
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____855 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____860 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____865 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
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
    let uu____3075 =
      let uu____3076 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3077 =
        let uu____3078 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3079 =
          let uu____3080 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3081 =
            let uu____3082 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3082 in
          FStar_Pprint.op_Hat_Hat uu____3080 uu____3081 in
        FStar_Pprint.op_Hat_Hat uu____3078 uu____3079 in
      FStar_Pprint.op_Hat_Hat uu____3076 uu____3077 in
    FStar_Pprint.group uu____3075
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3085 =
      let uu____3086 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3086 in
    let uu____3087 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3085 FStar_Pprint.space uu____3087
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3088  ->
    match uu____3088 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3122 =
                match uu____3122 with
                | (kwd,arg) ->
                    let uu____3129 = str "@" in
                    let uu____3130 =
                      let uu____3131 = str kwd in
                      let uu____3132 =
                        let uu____3133 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3133 in
                      FStar_Pprint.op_Hat_Hat uu____3131 uu____3132 in
                    FStar_Pprint.op_Hat_Hat uu____3129 uu____3130 in
              let uu____3134 =
                let uu____3135 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3135 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3134 in
        let uu____3140 =
          let uu____3141 =
            let uu____3142 =
              let uu____3143 =
                let uu____3144 = str doc1 in
                let uu____3145 =
                  let uu____3146 =
                    let uu____3147 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3147 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3146 in
                FStar_Pprint.op_Hat_Hat uu____3144 uu____3145 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3143 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3142 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3141 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3140
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3151 =
          let uu____3152 = str "val" in
          let uu____3153 =
            let uu____3154 =
              let uu____3155 = p_lident lid in
              let uu____3156 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3155 uu____3156 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3154 in
          FStar_Pprint.op_Hat_Hat uu____3152 uu____3153 in
        let uu____3157 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3151 uu____3157
    | FStar_Parser_AST.TopLevelLet (uu____3158,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3183 =
               let uu____3184 = str "let" in
               let uu____3185 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3184 uu____3185 in
             FStar_Pprint.group uu____3183) lbs
    | uu____3186 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3189 =
          let uu____3190 = str "open" in
          let uu____3191 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3190 uu____3191 in
        FStar_Pprint.group uu____3189
    | FStar_Parser_AST.Include uid ->
        let uu____3193 =
          let uu____3194 = str "include" in
          let uu____3195 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3194 uu____3195 in
        FStar_Pprint.group uu____3193
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3198 =
          let uu____3199 = str "module" in
          let uu____3200 =
            let uu____3201 =
              let uu____3202 = p_uident uid1 in
              let uu____3203 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3202 uu____3203 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3201 in
          FStar_Pprint.op_Hat_Hat uu____3199 uu____3200 in
        let uu____3204 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3198 uu____3204
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3206 =
          let uu____3207 = str "module" in
          let uu____3208 =
            let uu____3209 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3209 in
          FStar_Pprint.op_Hat_Hat uu____3207 uu____3208 in
        FStar_Pprint.group uu____3206
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3242 = str "effect" in
          let uu____3243 =
            let uu____3244 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3244 in
          FStar_Pprint.op_Hat_Hat uu____3242 uu____3243 in
        let uu____3245 =
          let uu____3246 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3246 FStar_Pprint.equals in
        let uu____3247 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3245 uu____3247
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3265 = str "type" in
        let uu____3266 = str "and" in
        precede_break_separate_map uu____3265 uu____3266 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3288 = str "let" in
          let uu____3289 =
            let uu____3290 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3290 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3288 uu____3289 in
        let uu____3291 =
          let uu____3292 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3292 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3291 p_letbinding lbs
          (fun uu____3300  ->
             match uu____3300 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3309 =
          let uu____3310 = str "val" in
          let uu____3311 =
            let uu____3312 =
              let uu____3313 = p_lident lid in
              let uu____3314 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3313 uu____3314 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3312 in
          FStar_Pprint.op_Hat_Hat uu____3310 uu____3311 in
        let uu____3315 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3309 uu____3315
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3319 =
            let uu____3320 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3320 FStar_Util.is_upper in
          if uu____3319
          then FStar_Pprint.empty
          else
            (let uu____3322 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3322 FStar_Pprint.space) in
        let uu____3323 =
          let uu____3324 =
            let uu____3325 = p_ident id in
            let uu____3326 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3325 uu____3326 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3324 in
        let uu____3327 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3323 uu____3327
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3334 = str "exception" in
        let uu____3335 =
          let uu____3336 =
            let uu____3337 = p_uident uid in
            let uu____3338 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3343 = str "of" in
                   let uu____3344 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3343 uu____3344) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3337 uu____3338 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3336 in
        FStar_Pprint.op_Hat_Hat uu____3334 uu____3335
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3346 = str "new_effect" in
        let uu____3347 =
          let uu____3348 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3348 in
        FStar_Pprint.op_Hat_Hat uu____3346 uu____3347
    | FStar_Parser_AST.SubEffect se ->
        let uu____3350 = str "sub_effect" in
        let uu____3351 =
          let uu____3352 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3352 in
        FStar_Pprint.op_Hat_Hat uu____3350 uu____3351
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3355 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3355 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3356 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3357) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___94_3374  ->
    match uu___94_3374 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3376 = str "#set-options" in
        let uu____3377 =
          let uu____3378 =
            let uu____3379 = str s in FStar_Pprint.dquotes uu____3379 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3378 in
        FStar_Pprint.op_Hat_Hat uu____3376 uu____3377
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3383 = str "#reset-options" in
        let uu____3384 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3388 =
                 let uu____3389 = str s in FStar_Pprint.dquotes uu____3389 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3388) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3383 uu____3384
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
  fun uu____3404  ->
    match uu____3404 with
    | (typedecl,fsdoc_opt) ->
        let uu____3417 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3418 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3417 uu____3418
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___95_3419  ->
    match uu___95_3419 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3434 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3450 =
          let uu____3451 = p_typ t in prefix2 FStar_Pprint.equals uu____3451 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3495 =
          match uu____3495 with
          | (lid1,t,doc_opt) ->
              let uu____3511 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3511 in
        let p_fields uu____3525 =
          let uu____3526 =
            let uu____3527 =
              let uu____3528 =
                let uu____3529 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3529 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3528 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3527 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3526 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3593 =
          match uu____3593 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3619 =
                  let uu____3620 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3620 in
                FStar_Range.extend_to_end_of_line uu____3619 in
              let p_constructorBranch decl =
                let uu____3653 =
                  let uu____3654 =
                    let uu____3655 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3655 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3654 in
                FStar_Pprint.group uu____3653 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3675 =
          let uu____3676 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3676 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3691  ->
             let uu____3692 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3692)
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
            let uu____3707 = p_ident lid in
            let uu____3708 =
              let uu____3709 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3709 in
            FStar_Pprint.op_Hat_Hat uu____3707 uu____3708
          else
            (let binders_doc =
               let uu____3712 = p_typars bs in
               let uu____3713 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3717 =
                        let uu____3718 =
                          let uu____3719 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3719 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3718 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3717) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3712 uu____3713 in
             let uu____3720 = p_ident lid in
             let uu____3721 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3720 binders_doc uu____3721)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3722  ->
    match uu____3722 with
    | (lid,t,doc_opt) ->
        let uu____3738 =
          let uu____3739 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3740 =
            let uu____3741 = p_lident lid in
            let uu____3742 =
              let uu____3743 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3743 in
            FStar_Pprint.op_Hat_Hat uu____3741 uu____3742 in
          FStar_Pprint.op_Hat_Hat uu____3739 uu____3740 in
        FStar_Pprint.group uu____3738
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3744  ->
    match uu____3744 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3772 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3773 =
          let uu____3774 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3775 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3780 =
                   let uu____3781 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3781 in
                 let uu____3782 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3780 uu____3782) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3774 uu____3775 in
        FStar_Pprint.op_Hat_Hat uu____3772 uu____3773
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3783  ->
    match uu____3783 with
    | (pat,uu____3789) ->
        let uu____3790 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3801 =
                let uu____3802 =
                  let uu____3803 =
                    let uu____3804 =
                      let uu____3805 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3805 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3804 in
                  FStar_Pprint.group uu____3803 in
                FStar_Pprint.op_Hat_Hat break1 uu____3802 in
              (pat1, uu____3801)
          | uu____3806 -> (pat, FStar_Pprint.empty) in
        (match uu____3790 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3810);
                     FStar_Parser_AST.prange = uu____3811;_},pats)
                  ->
                  let uu____3821 =
                    let uu____3822 = p_lident x in
                    let uu____3823 =
                      let uu____3824 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____3824 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3822 uu____3823 in
                  FStar_Pprint.group uu____3821
              | uu____3825 ->
                  let uu____3826 =
                    let uu____3827 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____3827 ascr_doc in
                  FStar_Pprint.group uu____3826))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3828  ->
    match uu____3828 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____3836 =
          let uu____3837 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____3837 in
        let uu____3838 = p_term e in prefix2 uu____3836 uu____3838
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___96_3839  ->
    match uu___96_3839 with
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
        let uu____3864 = p_uident uid in
        let uu____3865 = p_binders true bs in
        let uu____3866 =
          let uu____3867 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3867 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3864 uu____3865 uu____3866
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
          let uu____3876 =
            let uu____3877 =
              let uu____3878 =
                let uu____3879 = p_uident uid in
                let uu____3880 = p_binders true bs in
                let uu____3881 =
                  let uu____3882 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3882 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3879 uu____3880 uu____3881 in
              FStar_Pprint.group uu____3878 in
            let uu____3883 =
              let uu____3884 = str "with" in
              let uu____3885 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3884 uu____3885 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3877 uu____3883 in
          braces_with_nesting uu____3876
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3915 =
          let uu____3916 = p_lident lid in
          let uu____3917 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3916 uu____3917 in
        let uu____3918 = p_simpleTerm e in prefix2 uu____3915 uu____3918
    | uu____3919 ->
        let uu____3920 =
          let uu____3921 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3921 in
        failwith uu____3920
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____3976 =
        match uu____3976 with
        | (kwd,t) ->
            let uu____3983 =
              let uu____3984 = str kwd in
              let uu____3985 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3984 uu____3985 in
            let uu____3986 = p_simpleTerm t in prefix2 uu____3983 uu____3986 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____3991 =
      let uu____3992 =
        let uu____3993 = p_quident lift.FStar_Parser_AST.msource in
        let uu____3994 =
          let uu____3995 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3995 in
        FStar_Pprint.op_Hat_Hat uu____3993 uu____3994 in
      let uu____3996 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____3992 uu____3996 in
    let uu____3997 =
      let uu____3998 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3998 in
    FStar_Pprint.op_Hat_Hat uu____3991 uu____3997
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___97_3999  ->
    match uu___97_3999 with
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
    let uu____4001 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4001
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___98_4002  ->
    match uu___98_4002 with
    | FStar_Parser_AST.Rec  ->
        let uu____4003 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4003
    | FStar_Parser_AST.Mutable  ->
        let uu____4004 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4004
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___99_4005  ->
    match uu___99_4005 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4010 =
          let uu____4011 =
            let uu____4012 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4012 in
          FStar_Pprint.separate_map uu____4011 p_tuplePattern pats in
        FStar_Pprint.group uu____4010
    | uu____4013 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4020 =
          let uu____4021 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4021 p_constructorPattern pats in
        FStar_Pprint.group uu____4020
    | uu____4022 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4025;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4030 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4031 = p_constructorPattern hd1 in
        let uu____4032 = p_constructorPattern tl1 in
        infix0 uu____4030 uu____4031 uu____4032
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4034;_},pats)
        ->
        let uu____4040 = p_quident uid in
        let uu____4041 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4040 uu____4041
    | uu____4042 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4046 =
          let uu____4051 =
            let uu____4052 = unparen t in uu____4052.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4051) in
        (match uu____4046 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4057;
               FStar_Parser_AST.blevel = uu____4058;
               FStar_Parser_AST.aqual = uu____4059;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4065 =
               let uu____4066 = p_ident lid in
               p_refinement aqual uu____4066 t1 phi in
             soft_parens_with_nesting uu____4065
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4068;
               FStar_Parser_AST.blevel = uu____4069;
               FStar_Parser_AST.aqual = uu____4070;_},phi))
             ->
             let uu____4072 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4072
         | uu____4073 ->
             let uu____4078 =
               let uu____4079 = p_tuplePattern pat in
               let uu____4080 =
                 let uu____4081 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4082 =
                   let uu____4083 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4083 in
                 FStar_Pprint.op_Hat_Hat uu____4081 uu____4082 in
               FStar_Pprint.op_Hat_Hat uu____4079 uu____4080 in
             soft_parens_with_nesting uu____4078)
    | FStar_Parser_AST.PatList pats ->
        let uu____4087 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4087 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4102 =
          match uu____4102 with
          | (lid,pat) ->
              let uu____4109 = p_qlident lid in
              let uu____4110 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4109 uu____4110 in
        let uu____4111 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4111
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4121 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4122 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4123 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4121 uu____4122 uu____4123
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4134 =
          let uu____4135 =
            let uu____4136 = str (FStar_Ident.text_of_id op) in
            let uu____4137 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4136 uu____4137 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4135 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4134
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4145 = FStar_Pprint.optional p_aqual aqual in
        let uu____4146 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4145 uu____4146
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4148 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4151;
           FStar_Parser_AST.prange = uu____4152;_},uu____4153)
        ->
        let uu____4158 = p_tuplePattern p in
        soft_parens_with_nesting uu____4158
    | FStar_Parser_AST.PatTuple (uu____4159,false ) ->
        let uu____4164 = p_tuplePattern p in
        soft_parens_with_nesting uu____4164
    | uu____4165 ->
        let uu____4166 =
          let uu____4167 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4167 in
        failwith uu____4166
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4171 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4172 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4171 uu____4172
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4177 =
              let uu____4178 = unparen t in uu____4178.FStar_Parser_AST.tm in
            match uu____4177 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4181;
                   FStar_Parser_AST.blevel = uu____4182;
                   FStar_Parser_AST.aqual = uu____4183;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4185 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4185 t1 phi
            | uu____4186 ->
                let uu____4187 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4188 =
                  let uu____4189 = p_lident lid in
                  let uu____4190 =
                    let uu____4191 =
                      let uu____4192 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4193 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4192 uu____4193 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4191 in
                  FStar_Pprint.op_Hat_Hat uu____4189 uu____4190 in
                FStar_Pprint.op_Hat_Hat uu____4187 uu____4188 in
          if is_atomic
          then
            let uu____4194 =
              let uu____4195 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4195 in
            FStar_Pprint.group uu____4194
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4197 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4203 =
            let uu____4204 = unparen t in uu____4204.FStar_Parser_AST.tm in
          (match uu____4203 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4206;
                  FStar_Parser_AST.blevel = uu____4207;
                  FStar_Parser_AST.aqual = uu____4208;_},phi)
               ->
               if is_atomic
               then
                 let uu____4210 =
                   let uu____4211 =
                     let uu____4212 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4212 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4211 in
                 FStar_Pprint.group uu____4210
               else
                 (let uu____4214 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4214)
           | uu____4215 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4223 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4224 =
            let uu____4225 =
              let uu____4226 =
                let uu____4227 = p_appTerm t in
                let uu____4228 =
                  let uu____4229 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4229 in
                FStar_Pprint.op_Hat_Hat uu____4227 uu____4228 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4226 in
            FStar_Pprint.op_Hat_Hat binder uu____4225 in
          FStar_Pprint.op_Hat_Hat uu____4223 uu____4224
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
    let uu____4243 =
      let uu____4244 = unparen e in uu____4244.FStar_Parser_AST.tm in
    match uu____4243 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4247 =
          let uu____4248 =
            let uu____4249 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4249 FStar_Pprint.semi in
          FStar_Pprint.group uu____4248 in
        let uu____4250 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4247 uu____4250
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4254 =
          let uu____4255 =
            let uu____4256 =
              let uu____4257 = p_lident x in
              let uu____4258 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4257 uu____4258 in
            let uu____4259 =
              let uu____4260 = p_noSeqTerm e1 in
              let uu____4261 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4260 uu____4261 in
            op_Hat_Slash_Plus_Hat uu____4256 uu____4259 in
          FStar_Pprint.group uu____4255 in
        let uu____4262 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4254 uu____4262
    | uu____4263 ->
        let uu____4264 = p_noSeqTerm e in FStar_Pprint.group uu____4264
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4267 =
      let uu____4268 = unparen e in uu____4268.FStar_Parser_AST.tm in
    match uu____4267 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4273 =
          let uu____4274 = p_tmIff e1 in
          let uu____4275 =
            let uu____4276 =
              let uu____4277 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4277 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4276 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4274 uu____4275 in
        FStar_Pprint.group uu____4273
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4283 =
          let uu____4284 = p_tmIff e1 in
          let uu____4285 =
            let uu____4286 =
              let uu____4287 =
                let uu____4288 = p_typ t in
                let uu____4289 =
                  let uu____4290 = str "by" in
                  let uu____4291 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4290 uu____4291 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4288 uu____4289 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4287 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4286 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4284 uu____4285 in
        FStar_Pprint.group uu____4283
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4292;_},e1::e2::e3::[])
        ->
        let uu____4298 =
          let uu____4299 =
            let uu____4300 =
              let uu____4301 = p_atomicTermNotQUident e1 in
              let uu____4302 =
                let uu____4303 =
                  let uu____4304 =
                    let uu____4305 = p_term e2 in
                    soft_parens_with_nesting uu____4305 in
                  let uu____4306 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4304 uu____4306 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4303 in
              FStar_Pprint.op_Hat_Hat uu____4301 uu____4302 in
            FStar_Pprint.group uu____4300 in
          let uu____4307 =
            let uu____4308 = p_noSeqTerm e3 in jump2 uu____4308 in
          FStar_Pprint.op_Hat_Hat uu____4299 uu____4307 in
        FStar_Pprint.group uu____4298
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4309;_},e1::e2::e3::[])
        ->
        let uu____4315 =
          let uu____4316 =
            let uu____4317 =
              let uu____4318 = p_atomicTermNotQUident e1 in
              let uu____4319 =
                let uu____4320 =
                  let uu____4321 =
                    let uu____4322 = p_term e2 in
                    soft_brackets_with_nesting uu____4322 in
                  let uu____4323 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4321 uu____4323 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4320 in
              FStar_Pprint.op_Hat_Hat uu____4318 uu____4319 in
            FStar_Pprint.group uu____4317 in
          let uu____4324 =
            let uu____4325 = p_noSeqTerm e3 in jump2 uu____4325 in
          FStar_Pprint.op_Hat_Hat uu____4316 uu____4324 in
        FStar_Pprint.group uu____4315
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4335 =
          let uu____4336 = str "requires" in
          let uu____4337 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4336 uu____4337 in
        FStar_Pprint.group uu____4335
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4347 =
          let uu____4348 = str "ensures" in
          let uu____4349 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4348 uu____4349 in
        FStar_Pprint.group uu____4347
    | FStar_Parser_AST.Attributes es ->
        let uu____4353 =
          let uu____4354 = str "attributes" in
          let uu____4355 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4354 uu____4355 in
        FStar_Pprint.group uu____4353
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4359 = is_unit e3 in
        if uu____4359
        then
          let uu____4360 =
            let uu____4361 =
              let uu____4362 = str "if" in
              let uu____4363 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4362 uu____4363 in
            let uu____4364 =
              let uu____4365 = str "then" in
              let uu____4366 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4365 uu____4366 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4361 uu____4364 in
          FStar_Pprint.group uu____4360
        else
          (let e2_doc =
             let uu____4369 =
               let uu____4370 = unparen e2 in uu____4370.FStar_Parser_AST.tm in
             match uu____4369 with
             | FStar_Parser_AST.If (uu____4371,uu____4372,e31) when
                 is_unit e31 ->
                 let uu____4374 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4374
             | uu____4375 -> p_noSeqTerm e2 in
           let uu____4376 =
             let uu____4377 =
               let uu____4378 = str "if" in
               let uu____4379 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4378 uu____4379 in
             let uu____4380 =
               let uu____4381 =
                 let uu____4382 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4382 e2_doc in
               let uu____4383 =
                 let uu____4384 = str "else" in
                 let uu____4385 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4384 uu____4385 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4381 uu____4383 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4377 uu____4380 in
           FStar_Pprint.group uu____4376)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4408 =
          let uu____4409 =
            let uu____4410 = str "try" in
            let uu____4411 = p_noSeqTerm e1 in prefix2 uu____4410 uu____4411 in
          let uu____4412 =
            let uu____4413 = str "with" in
            let uu____4414 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4413 uu____4414 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4409 uu____4412 in
        FStar_Pprint.group uu____4408
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4445 =
          let uu____4446 =
            let uu____4447 = str "match" in
            let uu____4448 = p_noSeqTerm e1 in
            let uu____4449 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4447 uu____4448 uu____4449 in
          let uu____4450 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4446 uu____4450 in
        FStar_Pprint.group uu____4445
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4461 =
          let uu____4462 =
            let uu____4463 = str "let open" in
            let uu____4464 = p_quident uid in
            let uu____4465 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4463 uu____4464 uu____4465 in
          let uu____4466 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4462 uu____4466 in
        FStar_Pprint.group uu____4461
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4483 = str "let" in
          let uu____4484 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4483 uu____4484 in
        let uu____4485 =
          let uu____4486 =
            let uu____4487 =
              let uu____4488 = str "and" in
              precede_break_separate_map let_doc uu____4488 p_letbinding lbs in
            let uu____4493 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4487 uu____4493 in
          FStar_Pprint.group uu____4486 in
        let uu____4494 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4485 uu____4494
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4497;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4500;
                                                         FStar_Parser_AST.level
                                                           = uu____4501;_})
        when matches_var maybe_x x ->
        let uu____4528 =
          let uu____4529 = str "function" in
          let uu____4530 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4529 uu____4530 in
        FStar_Pprint.group uu____4528
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4541 =
          let uu____4542 = p_lident id in
          let uu____4543 =
            let uu____4544 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4544 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4542 uu____4543 in
        FStar_Pprint.group uu____4541
    | uu____4545 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4548 =
      let uu____4549 = unparen e in uu____4549.FStar_Parser_AST.tm in
    match uu____4548 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4565 =
          let uu____4566 =
            let uu____4567 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4567 FStar_Pprint.space in
          let uu____4568 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4566 uu____4568 FStar_Pprint.dot in
        let uu____4569 =
          let uu____4570 = p_trigger trigger in
          let uu____4571 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4570 uu____4571 in
        prefix2 uu____4565 uu____4569
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4587 =
          let uu____4588 =
            let uu____4589 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4589 FStar_Pprint.space in
          let uu____4590 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4588 uu____4590 FStar_Pprint.dot in
        let uu____4591 =
          let uu____4592 = p_trigger trigger in
          let uu____4593 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4592 uu____4593 in
        prefix2 uu____4587 uu____4591
    | uu____4594 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4596 =
      let uu____4597 = unparen e in uu____4597.FStar_Parser_AST.tm in
    match uu____4596 with
    | FStar_Parser_AST.QForall uu____4598 -> str "forall"
    | FStar_Parser_AST.QExists uu____4611 -> str "exists"
    | uu____4624 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___100_4625  ->
    match uu___100_4625 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4637 =
          let uu____4638 =
            let uu____4639 = str "pattern" in
            let uu____4640 =
              let uu____4641 =
                let uu____4642 = p_disjunctivePats pats in jump2 uu____4642 in
              let uu____4643 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4641 uu____4643 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4639 uu____4640 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4638 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4637
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4649 = str "\\/" in
    FStar_Pprint.separate_map uu____4649 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4655 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4655
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4657 =
      let uu____4658 = unparen e in uu____4658.FStar_Parser_AST.tm in
    match uu____4657 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4665 =
          let uu____4666 = str "fun" in
          let uu____4667 =
            let uu____4668 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4668 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4666 uu____4667 in
        let uu____4669 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4665 uu____4669
    | uu____4670 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4673  ->
    match uu____4673 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4692 =
            let uu____4693 = unparen e in uu____4693.FStar_Parser_AST.tm in
          match uu____4692 with
          | FStar_Parser_AST.Match uu____4696 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4711 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4727);
                 FStar_Parser_AST.prange = uu____4728;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4730);
                                                               FStar_Parser_AST.range
                                                                 = uu____4731;
                                                               FStar_Parser_AST.level
                                                                 = uu____4732;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4759 -> (fun x  -> x) in
        let uu____4761 =
          let uu____4762 =
            let uu____4763 =
              let uu____4764 =
                let uu____4765 =
                  let uu____4766 = p_disjunctivePattern pat in
                  let uu____4767 =
                    let uu____4768 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4768 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4766 uu____4767 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4765 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4764 in
            FStar_Pprint.group uu____4763 in
          let uu____4769 =
            let uu____4770 = p_term e in maybe_paren uu____4770 in
          op_Hat_Slash_Plus_Hat uu____4762 uu____4769 in
        FStar_Pprint.group uu____4761
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___101_4771  ->
    match uu___101_4771 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4775 = str "when" in
        let uu____4776 =
          let uu____4777 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4777 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4775 uu____4776
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4779 =
      let uu____4780 = unparen e in uu____4780.FStar_Parser_AST.tm in
    match uu____4779 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4781;_},e1::e2::[])
        ->
        let uu____4786 = str "<==>" in
        let uu____4787 = p_tmImplies e1 in
        let uu____4788 = p_tmIff e2 in
        infix0 uu____4786 uu____4787 uu____4788
    | uu____4789 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4791 =
      let uu____4792 = unparen e in uu____4792.FStar_Parser_AST.tm in
    match uu____4791 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4793;_},e1::e2::[])
        ->
        let uu____4798 = str "==>" in
        let uu____4799 = p_tmArrow p_tmFormula e1 in
        let uu____4800 = p_tmImplies e2 in
        infix0 uu____4798 uu____4799 uu____4800
    | uu____4801 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4806 =
        let uu____4807 = unparen e in uu____4807.FStar_Parser_AST.tm in
      match uu____4806 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4814 =
            let uu____4815 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4820 = p_binder false b in
                   let uu____4821 =
                     let uu____4822 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4822 in
                   FStar_Pprint.op_Hat_Hat uu____4820 uu____4821) bs in
            let uu____4823 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4815 uu____4823 in
          FStar_Pprint.group uu____4814
      | uu____4824 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4826 =
      let uu____4827 = unparen e in uu____4827.FStar_Parser_AST.tm in
    match uu____4826 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4828;_},e1::e2::[])
        ->
        let uu____4833 = str "\\/" in
        let uu____4834 = p_tmFormula e1 in
        let uu____4835 = p_tmConjunction e2 in
        infix0 uu____4833 uu____4834 uu____4835
    | uu____4836 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4838 =
      let uu____4839 = unparen e in uu____4839.FStar_Parser_AST.tm in
    match uu____4838 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4840;_},e1::e2::[])
        ->
        let uu____4845 = str "/\\" in
        let uu____4846 = p_tmConjunction e1 in
        let uu____4847 = p_tmTuple e2 in
        infix0 uu____4845 uu____4846 uu____4847
    | uu____4848 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4851 =
      let uu____4852 = unparen e in uu____4852.FStar_Parser_AST.tm in
    match uu____4851 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4867 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4867
          (fun uu____4875  ->
             match uu____4875 with | (e1,uu____4881) -> p_tmEq e1) args
    | uu____4882 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4887 =
             let uu____4888 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4888 in
           FStar_Pprint.group uu____4887)
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
      let uu____4933 =
        let uu____4934 = unparen e in uu____4934.FStar_Parser_AST.tm in
      match uu____4933 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____4941 = levels op1 in
          (match uu____4941 with
           | (left1,mine,right1) ->
               let uu____4951 =
                 let uu____4952 = FStar_All.pipe_left str op1 in
                 let uu____4953 = p_tmEq' left1 e1 in
                 let uu____4954 = p_tmEq' right1 e2 in
                 infix0 uu____4952 uu____4953 uu____4954 in
               paren_if curr mine uu____4951)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4955;_},e1::e2::[])
          ->
          let uu____4960 =
            let uu____4961 = p_tmEq e1 in
            let uu____4962 =
              let uu____4963 =
                let uu____4964 =
                  let uu____4965 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4965 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4964 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4963 in
            FStar_Pprint.op_Hat_Hat uu____4961 uu____4962 in
          FStar_Pprint.group uu____4960
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4966;_},e1::[])
          ->
          let uu____4970 = levels "-" in
          (match uu____4970 with
           | (left1,mine,right1) ->
               let uu____4980 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4980)
      | uu____4981 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5036 =
        let uu____5037 = unparen e in uu____5037.FStar_Parser_AST.tm in
      match uu____5036 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5040)::(e2,uu____5042)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5062 = is_list e in Prims.op_Negation uu____5062)
          ->
          let op = "::" in
          let uu____5064 = levels op in
          (match uu____5064 with
           | (left1,mine,right1) ->
               let uu____5074 =
                 let uu____5075 = str op in
                 let uu____5076 = p_tmNoEq' left1 e1 in
                 let uu____5077 = p_tmNoEq' right1 e2 in
                 infix0 uu____5075 uu____5076 uu____5077 in
               paren_if curr mine uu____5074)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5085 = levels op in
          (match uu____5085 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5099 = p_binder false b in
                 let uu____5100 =
                   let uu____5101 =
                     let uu____5102 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5102 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5101 in
                 FStar_Pprint.op_Hat_Hat uu____5099 uu____5100 in
               let uu____5103 =
                 let uu____5104 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5105 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5104 uu____5105 in
               paren_if curr mine uu____5103)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5112 = levels op1 in
          (match uu____5112 with
           | (left1,mine,right1) ->
               let uu____5122 =
                 let uu____5123 = str op1 in
                 let uu____5124 = p_tmNoEq' left1 e1 in
                 let uu____5125 = p_tmNoEq' right1 e2 in
                 infix0 uu____5123 uu____5124 uu____5125 in
               paren_if curr mine uu____5122)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5128 =
            let uu____5129 = p_lidentOrUnderscore lid in
            let uu____5130 =
              let uu____5131 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5131 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5129 uu____5130 in
          FStar_Pprint.group uu____5128
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5152 =
            let uu____5153 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5154 =
              let uu____5155 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5155 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5153 uu____5154 in
          braces_with_nesting uu____5152
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5160;_},e1::[])
          ->
          let uu____5164 =
            let uu____5165 = str "~" in
            let uu____5166 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5165 uu____5166 in
          FStar_Pprint.group uu____5164
      | uu____5167 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5169 = p_appTerm e in
    let uu____5170 =
      let uu____5171 =
        let uu____5172 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5172 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5171 in
    FStar_Pprint.op_Hat_Hat uu____5169 uu____5170
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5177 =
            let uu____5178 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5178 t phi in
          soft_parens_with_nesting uu____5177
      | FStar_Parser_AST.TAnnotated uu____5179 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5184 ->
          let uu____5185 =
            let uu____5186 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5186 in
          failwith uu____5185
      | FStar_Parser_AST.TVariable uu____5187 ->
          let uu____5188 =
            let uu____5189 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5189 in
          failwith uu____5188
      | FStar_Parser_AST.NoName uu____5190 ->
          let uu____5191 =
            let uu____5192 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5192 in
          failwith uu____5191
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5193  ->
    match uu____5193 with
    | (lid,e) ->
        let uu____5200 =
          let uu____5201 = p_qlident lid in
          let uu____5202 =
            let uu____5203 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5203 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5201 uu____5202 in
        FStar_Pprint.group uu____5200
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5205 =
      let uu____5206 = unparen e in uu____5206.FStar_Parser_AST.tm in
    match uu____5205 with
    | FStar_Parser_AST.App uu____5207 when is_general_application e ->
        let uu____5214 = head_and_args e in
        (match uu____5214 with
         | (head1,args) ->
             let uu____5239 =
               let uu____5250 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5250
               then
                 let uu____5271 =
                   FStar_Util.take
                     (fun uu____5295  ->
                        match uu____5295 with
                        | (uu____5300,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5271 with
                 | (fs_typ_args,args1) ->
                     let uu____5338 =
                       let uu____5339 = p_indexingTerm head1 in
                       let uu____5340 =
                         let uu____5341 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5341 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5339 uu____5340 in
                     (uu____5338, args1)
               else
                 (let uu____5353 = p_indexingTerm head1 in (uu____5353, args)) in
             (match uu____5239 with
              | (head_doc,args1) ->
                  let uu____5374 =
                    let uu____5375 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5375 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5374))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5395 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5395)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5413 =
               let uu____5414 = p_quident lid in
               let uu____5415 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5414 uu____5415 in
             FStar_Pprint.group uu____5413
         | hd1::tl1 ->
             let uu____5432 =
               let uu____5433 =
                 let uu____5434 =
                   let uu____5435 = p_quident lid in
                   let uu____5436 = p_argTerm hd1 in
                   prefix2 uu____5435 uu____5436 in
                 FStar_Pprint.group uu____5434 in
               let uu____5437 =
                 let uu____5438 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5438 in
               FStar_Pprint.op_Hat_Hat uu____5433 uu____5437 in
             FStar_Pprint.group uu____5432)
    | uu____5443 -> p_indexingTerm e
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
         (let uu____5452 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5452 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5454 = str "#" in
        let uu____5455 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5454 uu____5455
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5457  ->
    match uu____5457 with | (e,uu____5463) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5468 =
        let uu____5469 = unparen e in uu____5469.FStar_Parser_AST.tm in
      match uu____5468 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5470;_},e1::e2::[])
          ->
          let uu____5475 =
            let uu____5476 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5477 =
              let uu____5478 =
                let uu____5479 = p_term e2 in
                soft_parens_with_nesting uu____5479 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5478 in
            FStar_Pprint.op_Hat_Hat uu____5476 uu____5477 in
          FStar_Pprint.group uu____5475
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5480;_},e1::e2::[])
          ->
          let uu____5485 =
            let uu____5486 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5487 =
              let uu____5488 =
                let uu____5489 = p_term e2 in
                soft_brackets_with_nesting uu____5489 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5488 in
            FStar_Pprint.op_Hat_Hat uu____5486 uu____5487 in
          FStar_Pprint.group uu____5485
      | uu____5490 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5493 =
      let uu____5494 = unparen e in uu____5494.FStar_Parser_AST.tm in
    match uu____5493 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5497 = p_quident lid in
        let uu____5498 =
          let uu____5499 =
            let uu____5500 = p_term e1 in soft_parens_with_nesting uu____5500 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5499 in
        FStar_Pprint.op_Hat_Hat uu____5497 uu____5498
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5506 = str (FStar_Ident.text_of_id op) in
        let uu____5507 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5506 uu____5507
    | uu____5508 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5510 =
      let uu____5511 = unparen e in uu____5511.FStar_Parser_AST.tm in
    match uu____5510 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5516 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5523 = str (FStar_Ident.text_of_id op) in
        let uu____5524 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5523 uu____5524
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5528 =
          let uu____5529 =
            let uu____5530 = str (FStar_Ident.text_of_id op) in
            let uu____5531 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5530 uu____5531 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5529 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5528
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5546 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5547 =
          let uu____5548 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5549 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5548 p_tmEq uu____5549 in
        let uu____5556 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5546 uu____5547 uu____5556
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5559 =
          let uu____5560 = p_atomicTermNotQUident e1 in
          let uu____5561 =
            let uu____5562 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5562 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5560 uu____5561 in
        FStar_Pprint.group uu____5559
    | uu____5563 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5565 =
      let uu____5566 = unparen e in uu____5566.FStar_Parser_AST.tm in
    match uu____5565 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5570 = p_quident constr_lid in
        let uu____5571 =
          let uu____5572 =
            let uu____5573 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5573 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5572 in
        FStar_Pprint.op_Hat_Hat uu____5570 uu____5571
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5575 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5575 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5577 = p_term e1 in soft_parens_with_nesting uu____5577
    | uu____5578 when is_array e ->
        let es = extract_from_list e in
        let uu____5582 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5583 =
          let uu____5584 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5584 p_noSeqTerm es in
        let uu____5585 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5582 uu____5583 uu____5585
    | uu____5586 when is_list e ->
        let uu____5587 =
          let uu____5588 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5589 = extract_from_list e in
          separate_map_or_flow uu____5588 p_noSeqTerm uu____5589 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5587 FStar_Pprint.rbracket
    | uu____5592 when is_lex_list e ->
        let uu____5593 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5594 =
          let uu____5595 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5596 = extract_from_list e in
          separate_map_or_flow uu____5595 p_noSeqTerm uu____5596 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5593 uu____5594 FStar_Pprint.rbracket
    | uu____5599 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5603 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5604 =
          let uu____5605 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5605 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5603 uu____5604 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5609 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5610 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5609 uu____5610
    | FStar_Parser_AST.Op (op,args) when
        let uu____5617 = handleable_op op args in
        Prims.op_Negation uu____5617 ->
        let uu____5618 =
          let uu____5619 =
            let uu____5620 =
              let uu____5621 =
                let uu____5622 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5622
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5621 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5620 in
          Prims.strcat "Operation " uu____5619 in
        failwith uu____5618
    | FStar_Parser_AST.Uvar uu____5623 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5624 = p_term e in soft_parens_with_nesting uu____5624
    | FStar_Parser_AST.Const uu____5625 ->
        let uu____5626 = p_term e in soft_parens_with_nesting uu____5626
    | FStar_Parser_AST.Op uu____5627 ->
        let uu____5634 = p_term e in soft_parens_with_nesting uu____5634
    | FStar_Parser_AST.Tvar uu____5635 ->
        let uu____5636 = p_term e in soft_parens_with_nesting uu____5636
    | FStar_Parser_AST.Var uu____5637 ->
        let uu____5638 = p_term e in soft_parens_with_nesting uu____5638
    | FStar_Parser_AST.Name uu____5639 ->
        let uu____5640 = p_term e in soft_parens_with_nesting uu____5640
    | FStar_Parser_AST.Construct uu____5641 ->
        let uu____5652 = p_term e in soft_parens_with_nesting uu____5652
    | FStar_Parser_AST.Abs uu____5653 ->
        let uu____5660 = p_term e in soft_parens_with_nesting uu____5660
    | FStar_Parser_AST.App uu____5661 ->
        let uu____5668 = p_term e in soft_parens_with_nesting uu____5668
    | FStar_Parser_AST.Let uu____5669 ->
        let uu____5682 = p_term e in soft_parens_with_nesting uu____5682
    | FStar_Parser_AST.LetOpen uu____5683 ->
        let uu____5688 = p_term e in soft_parens_with_nesting uu____5688
    | FStar_Parser_AST.Seq uu____5689 ->
        let uu____5694 = p_term e in soft_parens_with_nesting uu____5694
    | FStar_Parser_AST.Bind uu____5695 ->
        let uu____5702 = p_term e in soft_parens_with_nesting uu____5702
    | FStar_Parser_AST.If uu____5703 ->
        let uu____5710 = p_term e in soft_parens_with_nesting uu____5710
    | FStar_Parser_AST.Match uu____5711 ->
        let uu____5726 = p_term e in soft_parens_with_nesting uu____5726
    | FStar_Parser_AST.TryWith uu____5727 ->
        let uu____5742 = p_term e in soft_parens_with_nesting uu____5742
    | FStar_Parser_AST.Ascribed uu____5743 ->
        let uu____5752 = p_term e in soft_parens_with_nesting uu____5752
    | FStar_Parser_AST.Record uu____5753 ->
        let uu____5766 = p_term e in soft_parens_with_nesting uu____5766
    | FStar_Parser_AST.Project uu____5767 ->
        let uu____5772 = p_term e in soft_parens_with_nesting uu____5772
    | FStar_Parser_AST.Product uu____5773 ->
        let uu____5780 = p_term e in soft_parens_with_nesting uu____5780
    | FStar_Parser_AST.Sum uu____5781 ->
        let uu____5788 = p_term e in soft_parens_with_nesting uu____5788
    | FStar_Parser_AST.QForall uu____5789 ->
        let uu____5802 = p_term e in soft_parens_with_nesting uu____5802
    | FStar_Parser_AST.QExists uu____5803 ->
        let uu____5816 = p_term e in soft_parens_with_nesting uu____5816
    | FStar_Parser_AST.Refine uu____5817 ->
        let uu____5822 = p_term e in soft_parens_with_nesting uu____5822
    | FStar_Parser_AST.NamedTyp uu____5823 ->
        let uu____5828 = p_term e in soft_parens_with_nesting uu____5828
    | FStar_Parser_AST.Requires uu____5829 ->
        let uu____5836 = p_term e in soft_parens_with_nesting uu____5836
    | FStar_Parser_AST.Ensures uu____5837 ->
        let uu____5844 = p_term e in soft_parens_with_nesting uu____5844
    | FStar_Parser_AST.Assign uu____5845 ->
        let uu____5850 = p_term e in soft_parens_with_nesting uu____5850
    | FStar_Parser_AST.Attributes uu____5851 ->
        let uu____5854 = p_term e in soft_parens_with_nesting uu____5854
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___104_5855  ->
    match uu___104_5855 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5859 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5859
    | FStar_Const.Const_string (s,uu____5861) ->
        let uu____5862 = str s in FStar_Pprint.dquotes uu____5862
    | FStar_Const.Const_bytearray (bytes,uu____5864) ->
        let uu____5869 =
          let uu____5870 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5870 in
        let uu____5871 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5869 uu____5871
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___102_5889 =
          match uu___102_5889 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___103_5893 =
          match uu___103_5893 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5904  ->
               match uu____5904 with
               | (s,w) ->
                   let uu____5911 = signedness s in
                   let uu____5912 = width w in
                   FStar_Pprint.op_Hat_Hat uu____5911 uu____5912)
            sign_width_opt in
        let uu____5913 = str repr in
        FStar_Pprint.op_Hat_Hat uu____5913 ending
    | FStar_Const.Const_range r ->
        let uu____5915 = FStar_Range.string_of_range r in str uu____5915
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5917 = p_quident lid in
        let uu____5918 =
          let uu____5919 =
            let uu____5920 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5920 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5919 in
        FStar_Pprint.op_Hat_Hat uu____5917 uu____5918
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5922 = str "u#" in
    let uu____5923 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____5922 uu____5923
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5925 =
      let uu____5926 = unparen u in uu____5926.FStar_Parser_AST.tm in
    match uu____5925 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5927;_},u1::u2::[])
        ->
        let uu____5932 =
          let uu____5933 = p_universeFrom u1 in
          let uu____5934 =
            let uu____5935 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5935 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5933 uu____5934 in
        FStar_Pprint.group uu____5932
    | FStar_Parser_AST.App uu____5936 ->
        let uu____5943 = head_and_args u in
        (match uu____5943 with
         | (head1,args) ->
             let uu____5968 =
               let uu____5969 = unparen head1 in
               uu____5969.FStar_Parser_AST.tm in
             (match uu____5968 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____5971 =
                    let uu____5972 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____5973 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____5981  ->
                           match uu____5981 with
                           | (u1,uu____5987) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____5972 uu____5973 in
                  FStar_Pprint.group uu____5971
              | uu____5988 ->
                  let uu____5989 =
                    let uu____5990 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____5990 in
                  failwith uu____5989))
    | uu____5991 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5993 =
      let uu____5994 = unparen u in uu____5994.FStar_Parser_AST.tm in
    match uu____5993 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6017 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6017
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6018;_},uu____6019::uu____6020::[])
        ->
        let uu____6023 = p_universeFrom u in
        soft_parens_with_nesting uu____6023
    | FStar_Parser_AST.App uu____6024 ->
        let uu____6031 = p_universeFrom u in
        soft_parens_with_nesting uu____6031
    | uu____6032 ->
        let uu____6033 =
          let uu____6034 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6034 in
        failwith uu____6033
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
       | FStar_Parser_AST.Module (uu____6071,decls) ->
           let uu____6077 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6077
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6086,decls,uu____6088) ->
           let uu____6093 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6093
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6136  ->
         match uu____6136 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6178,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6184,decls,uu____6186) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6222 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6235;
                 FStar_Parser_AST.doc = uu____6236;
                 FStar_Parser_AST.quals = uu____6237;
                 FStar_Parser_AST.attrs = uu____6238;_}::uu____6239 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6245 =
                   let uu____6248 =
                     let uu____6251 = FStar_List.tl ds in d :: uu____6251 in
                   d0 :: uu____6248 in
                 (uu____6245, (d0.FStar_Parser_AST.drange))
             | uu____6256 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6222 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6317 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6317 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6410 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6410, comments1))))))