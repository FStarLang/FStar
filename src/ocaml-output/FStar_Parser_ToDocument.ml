open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app:
  'Auu____19 'Auu____20 .
    Prims.bool -> ('Auu____20 -> 'Auu____19) -> 'Auu____20 -> 'Auu____19
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
    let uu____115 =
      let uu____116 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____116 in
    if uu____115
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____138 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____147 'Auu____148 .
    'Auu____148 ->
      ('Auu____147 -> 'Auu____148) ->
        'Auu____147 FStar_Pervasives_Native.option -> 'Auu____148
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
  'Auu____202 .
    FStar_Pprint.document ->
      ('Auu____202 -> FStar_Pprint.document) ->
        'Auu____202 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____224 =
          let uu____225 =
            let uu____226 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____226 in
          FStar_Pprint.separate_map uu____225 f l in
        FStar_Pprint.group uu____224
let precede_break_separate_map:
  'Auu____232 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____232 -> FStar_Pprint.document) ->
          'Auu____232 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____258 =
            let uu____259 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____260 =
              let uu____261 = FStar_List.hd l in
              FStar_All.pipe_right uu____261 f in
            FStar_Pprint.precede uu____259 uu____260 in
          let uu____262 =
            let uu____263 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____269 =
                   let uu____270 =
                     let uu____271 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____271 in
                   FStar_Pprint.op_Hat_Hat sep uu____270 in
                 FStar_Pprint.op_Hat_Hat break1 uu____269) uu____263 in
          FStar_Pprint.op_Hat_Hat uu____258 uu____262
let concat_break_map:
  'Auu____275 .
    ('Auu____275 -> FStar_Pprint.document) ->
      'Auu____275 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____293 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____297 = f x in FStar_Pprint.op_Hat_Hat uu____297 break1)
          l in
      FStar_Pprint.group uu____293
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
    let uu____319 = str "begin" in
    let uu____320 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____319 contents uu____320
let separate_map_or_flow:
  'Auu____325 .
    FStar_Pprint.document ->
      ('Auu____325 -> FStar_Pprint.document) ->
        'Auu____325 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
  'Auu____357 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____357 -> FStar_Pprint.document) ->
                  'Auu____357 Prims.list -> FStar_Pprint.document
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
                    (let uu____402 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____402
                       closing)
let soft_surround_map_or_flow:
  'Auu____412 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____412 -> FStar_Pprint.document) ->
                  'Auu____412 Prims.list -> FStar_Pprint.document
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
                    (let uu____457 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____457
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____470  ->
    match uu____470 with
    | (comment,keywords) ->
        let uu____495 =
          let uu____496 =
            let uu____499 = str comment in
            let uu____500 =
              let uu____503 =
                let uu____506 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____515  ->
                       match uu____515 with
                       | (k,v1) ->
                           let uu____522 =
                             let uu____525 = str k in
                             let uu____526 =
                               let uu____529 =
                                 let uu____532 = str v1 in [uu____532] in
                               FStar_Pprint.rarrow :: uu____529 in
                             uu____525 :: uu____526 in
                           FStar_Pprint.concat uu____522) keywords in
                [uu____506] in
              FStar_Pprint.space :: uu____503 in
            uu____499 :: uu____500 in
          FStar_Pprint.concat uu____496 in
        FStar_Pprint.group uu____495
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____536 =
      let uu____537 = unparen e in uu____537.FStar_Parser_AST.tm in
    match uu____536 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____538 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____545 =
        let uu____546 = unparen t in uu____546.FStar_Parser_AST.tm in
      match uu____545 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____548 -> false
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
        let uu____565 =
          let uu____566 = unparen e in uu____566.FStar_Parser_AST.tm in
        match uu____565 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____579::(e2,uu____581)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____604 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____614 =
      let uu____615 = unparen e in uu____615.FStar_Parser_AST.tm in
    match uu____614 with
    | FStar_Parser_AST.Construct (uu____618,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____629,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____650 = extract_from_list e2 in e1 :: uu____650
    | uu____653 ->
        let uu____654 =
          let uu____655 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____655 in
        failwith uu____654
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____661 =
      let uu____662 = unparen e in uu____662.FStar_Parser_AST.tm in
    match uu____661 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____664;
           FStar_Parser_AST.level = uu____665;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____667 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____671 =
      let uu____672 = unparen e in uu____672.FStar_Parser_AST.tm in
    match uu____671 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____675;
           FStar_Parser_AST.level = uu____676;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____678;
                                                        FStar_Parser_AST.level
                                                          = uu____679;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____681;
                                                   FStar_Parser_AST.level =
                                                     uu____682;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____684;
                FStar_Parser_AST.level = uu____685;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____687;
           FStar_Parser_AST.level = uu____688;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____690 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____696 =
      let uu____697 = unparen e in uu____697.FStar_Parser_AST.tm in
    match uu____696 with
    | FStar_Parser_AST.Var uu____700 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____701;
           FStar_Parser_AST.range = uu____702;
           FStar_Parser_AST.level = uu____703;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____704;
                                                        FStar_Parser_AST.range
                                                          = uu____705;
                                                        FStar_Parser_AST.level
                                                          = uu____706;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____708;
                                                   FStar_Parser_AST.level =
                                                     uu____709;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____710;
                FStar_Parser_AST.range = uu____711;
                FStar_Parser_AST.level = uu____712;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____714;
           FStar_Parser_AST.level = uu____715;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____717 = extract_from_ref_set e1 in
        let uu____720 = extract_from_ref_set e2 in
        FStar_List.append uu____717 uu____720
    | uu____723 ->
        let uu____724 =
          let uu____725 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____725 in
        failwith uu____724
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____731 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____731
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____735 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____735
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
      let uu____785 =
        let uu____786 = unparen e1 in uu____786.FStar_Parser_AST.tm in
      match uu____785 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____804 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____818 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____822 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____826 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___49_844  ->
    match uu___49_844 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___50_861  ->
      match uu___50_861 with
      | FStar_Util.Inl c ->
          let uu____870 = FStar_String.get s (Prims.parse_int "0") in
          uu____870 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____878 .
    Prims.string ->
      ('Auu____878,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____897  ->
      match uu____897 with
      | (assoc_levels,tokens) ->
          let uu____925 = FStar_List.tryFind (matches_token s) tokens in
          uu____925 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____951 .
    Prims.unit ->
      (associativity,('Auu____951,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____962  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____978 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____978) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____990  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1025 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1025) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1037  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1065 .
    Prims.unit ->
      (associativity,('Auu____1065,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1076  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1092 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1092) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1104  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1132 .
    Prims.unit ->
      (associativity,('Auu____1132,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1143  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1159 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1159) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1171  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1192 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1192) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1204  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1239 .
    Prims.unit ->
      (associativity,('Auu____1239,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1250  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1266 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1266) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1278  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1299 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1299) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1311  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1332 .
    Prims.unit ->
      (associativity,('Auu____1332,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1343  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1359 .
    Prims.unit ->
      (associativity,('Auu____1359,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1370  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1386 .
    Prims.unit ->
      (associativity,('Auu____1386,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1397  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___51_1604 =
    match uu___51_1604 with
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
      let uu____1724 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1724 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1774) ->
          assoc_levels
      | uu____1818 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1853 .
    ('Auu____1853,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1913 =
        FStar_List.tryFind
          (fun uu____1953  ->
             match uu____1953 with
             | (uu____1971,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1913 with
      | FStar_Pervasives_Native.Some ((uu____2013,l1,uu____2015),uu____2016)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2071 =
            let uu____2072 =
              let uu____2073 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2073 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2072 in
          failwith uu____2071 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2107 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2107) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2121  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2202 =
      let uu____2216 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2216 (operatorInfix0ad12 ()) in
    uu____2202 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2329 =
      let uu____2343 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2343 opinfix34 in
    uu____2329 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2409 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2409
    then Prims.parse_int "1"
    else
      (let uu____2411 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2411
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2417 . FStar_Ident.ident -> 'Auu____2417 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
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
      | uu____2430 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2464 .
    ('Auu____2464 -> FStar_Pprint.document) ->
      'Auu____2464 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2496 = FStar_ST.op_Bang comment_stack in
          match uu____2496 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2555 = FStar_Range.range_before_pos crange print_pos in
              if uu____2555
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2592 =
                    let uu____2593 =
                      let uu____2594 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2594
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2593 in
                  comments_before_pos uu____2592 print_pos lookahead_pos))
              else
                (let uu____2596 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2596)) in
        let uu____2597 =
          let uu____2602 =
            let uu____2603 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2603 in
          let uu____2604 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2602 uu____2604 in
        match uu____2597 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2610 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2610
              else comments in
            let uu____2616 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2616
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2629 = FStar_ST.op_Bang comment_stack in
          match uu____2629 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2713 =
                    let uu____2714 =
                      let uu____2715 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2715 in
                    uu____2714 - lbegin in
                  max k uu____2713 in
                let doc2 =
                  let uu____2717 =
                    let uu____2718 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2719 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2718 uu____2719 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2717 in
                let uu____2720 =
                  let uu____2721 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2721 in
                place_comments_until_pos (Prims.parse_int "1") uu____2720
                  pos_end doc2))
          | uu____2722 ->
              let lnum =
                let uu____2730 =
                  let uu____2731 = FStar_Range.line_of_pos pos_end in
                  uu____2731 - lbegin in
                max (Prims.parse_int "1") uu____2730 in
              let uu____2732 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2732
let separate_map_with_comments:
  'Auu____2739 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2739 -> FStar_Pprint.document) ->
          'Auu____2739 Prims.list ->
            ('Auu____2739 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2787 x =
              match uu____2787 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2801 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2801 doc1 in
                  let uu____2802 =
                    let uu____2803 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2803 in
                  let uu____2804 =
                    let uu____2805 =
                      let uu____2806 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2806 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2805 in
                  (uu____2802, uu____2804) in
            let uu____2807 =
              let uu____2814 = FStar_List.hd xs in
              let uu____2815 = FStar_List.tl xs in (uu____2814, uu____2815) in
            match uu____2807 with
            | (x,xs1) ->
                let init1 =
                  let uu____2831 =
                    let uu____2832 =
                      let uu____2833 = extract_range x in
                      FStar_Range.end_of_range uu____2833 in
                    FStar_Range.line_of_pos uu____2832 in
                  let uu____2834 =
                    let uu____2835 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2835 in
                  (uu____2831, uu____2834) in
                let uu____2836 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2836
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3131 =
      let uu____3132 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3133 =
        let uu____3134 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3135 =
          let uu____3136 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3137 =
            let uu____3138 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3138 in
          FStar_Pprint.op_Hat_Hat uu____3136 uu____3137 in
        FStar_Pprint.op_Hat_Hat uu____3134 uu____3135 in
      FStar_Pprint.op_Hat_Hat uu____3132 uu____3133 in
    FStar_Pprint.group uu____3131
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3141 =
      let uu____3142 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3142 in
    let uu____3143 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3141 FStar_Pprint.space uu____3143
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3144  ->
    match uu____3144 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3178 =
                match uu____3178 with
                | (kwd,arg) ->
                    let uu____3185 = str "@" in
                    let uu____3186 =
                      let uu____3187 = str kwd in
                      let uu____3188 =
                        let uu____3189 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3189 in
                      FStar_Pprint.op_Hat_Hat uu____3187 uu____3188 in
                    FStar_Pprint.op_Hat_Hat uu____3185 uu____3186 in
              let uu____3190 =
                let uu____3191 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3191 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3190 in
        let uu____3196 =
          let uu____3197 =
            let uu____3198 =
              let uu____3199 =
                let uu____3200 = str doc1 in
                let uu____3201 =
                  let uu____3202 =
                    let uu____3203 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3203 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3202 in
                FStar_Pprint.op_Hat_Hat uu____3200 uu____3201 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3199 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3198 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3197 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3196
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3207 =
          let uu____3208 = str "val" in
          let uu____3209 =
            let uu____3210 =
              let uu____3211 = p_lident lid in
              let uu____3212 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3211 uu____3212 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3210 in
          FStar_Pprint.op_Hat_Hat uu____3208 uu____3209 in
        let uu____3213 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3207 uu____3213
    | FStar_Parser_AST.TopLevelLet (uu____3214,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3239 =
               let uu____3240 = str "let" in
               let uu____3241 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3240 uu____3241 in
             FStar_Pprint.group uu____3239) lbs
    | uu____3242 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3245 =
          let uu____3246 = str "open" in
          let uu____3247 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3246 uu____3247 in
        FStar_Pprint.group uu____3245
    | FStar_Parser_AST.Include uid ->
        let uu____3249 =
          let uu____3250 = str "include" in
          let uu____3251 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3250 uu____3251 in
        FStar_Pprint.group uu____3249
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3254 =
          let uu____3255 = str "module" in
          let uu____3256 =
            let uu____3257 =
              let uu____3258 = p_uident uid1 in
              let uu____3259 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3258 uu____3259 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3257 in
          FStar_Pprint.op_Hat_Hat uu____3255 uu____3256 in
        let uu____3260 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3254 uu____3260
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3262 =
          let uu____3263 = str "module" in
          let uu____3264 =
            let uu____3265 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3265 in
          FStar_Pprint.op_Hat_Hat uu____3263 uu____3264 in
        FStar_Pprint.group uu____3262
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3298 = str "effect" in
          let uu____3299 =
            let uu____3300 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3300 in
          FStar_Pprint.op_Hat_Hat uu____3298 uu____3299 in
        let uu____3301 =
          let uu____3302 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3302 FStar_Pprint.equals in
        let uu____3303 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3301 uu____3303
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3321 = str "type" in
        let uu____3322 = str "and" in
        precede_break_separate_map uu____3321 uu____3322 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3344 = str "let" in
          let uu____3345 =
            let uu____3346 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3346 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3344 uu____3345 in
        let uu____3347 =
          let uu____3348 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3348 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3347 p_letbinding lbs
          (fun uu____3356  ->
             match uu____3356 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3365 =
          let uu____3366 = str "val" in
          let uu____3367 =
            let uu____3368 =
              let uu____3369 = p_lident lid in
              let uu____3370 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3369 uu____3370 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3368 in
          FStar_Pprint.op_Hat_Hat uu____3366 uu____3367 in
        let uu____3371 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3365 uu____3371
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3375 =
            let uu____3376 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3376 FStar_Util.is_upper in
          if uu____3375
          then FStar_Pprint.empty
          else
            (let uu____3378 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3378 FStar_Pprint.space) in
        let uu____3379 =
          let uu____3380 =
            let uu____3381 = p_ident id1 in
            let uu____3382 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3381 uu____3382 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3380 in
        let uu____3383 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3379 uu____3383
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3390 = str "exception" in
        let uu____3391 =
          let uu____3392 =
            let uu____3393 = p_uident uid in
            let uu____3394 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3399 = str "of" in
                   let uu____3400 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3399 uu____3400) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3393 uu____3394 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3392 in
        FStar_Pprint.op_Hat_Hat uu____3390 uu____3391
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3402 = str "new_effect" in
        let uu____3403 =
          let uu____3404 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3404 in
        FStar_Pprint.op_Hat_Hat uu____3402 uu____3403
    | FStar_Parser_AST.SubEffect se ->
        let uu____3406 = str "sub_effect" in
        let uu____3407 =
          let uu____3408 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3408 in
        FStar_Pprint.op_Hat_Hat uu____3406 uu____3407
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3411 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3411 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3412 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3413) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___52_3430  ->
    match uu___52_3430 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3432 = str "#set-options" in
        let uu____3433 =
          let uu____3434 =
            let uu____3435 = str s in FStar_Pprint.dquotes uu____3435 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3434 in
        FStar_Pprint.op_Hat_Hat uu____3432 uu____3433
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3439 = str "#reset-options" in
        let uu____3440 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3444 =
                 let uu____3445 = str s in FStar_Pprint.dquotes uu____3445 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3444) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3439 uu____3440
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
  fun uu____3469  ->
    match uu____3469 with
    | (typedecl,fsdoc_opt) ->
        let uu____3482 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3483 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3482 uu____3483
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___53_3484  ->
    match uu___53_3484 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3499 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3515 =
          let uu____3516 = p_typ t in prefix2 FStar_Pprint.equals uu____3516 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3560 =
          match uu____3560 with
          | (lid1,t,doc_opt) ->
              let uu____3576 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3576 in
        let p_fields uu____3590 =
          let uu____3591 =
            let uu____3592 =
              let uu____3593 =
                let uu____3594 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3594 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3593 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3592 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3591 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3658 =
          match uu____3658 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3684 =
                  let uu____3685 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3685 in
                FStar_Range.extend_to_end_of_line uu____3684 in
              let p_constructorBranch decl =
                let uu____3718 =
                  let uu____3719 =
                    let uu____3720 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3720 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3719 in
                FStar_Pprint.group uu____3718 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3740 =
          let uu____3741 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3741 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3756  ->
             let uu____3757 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3757)
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
            let uu____3772 = p_ident lid in
            let uu____3773 =
              let uu____3774 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3774 in
            FStar_Pprint.op_Hat_Hat uu____3772 uu____3773
          else
            (let binders_doc =
               let uu____3777 = p_typars bs in
               let uu____3778 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3782 =
                        let uu____3783 =
                          let uu____3784 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3784 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3783 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3782) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3777 uu____3778 in
             let uu____3785 = p_ident lid in
             let uu____3786 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3785 binders_doc uu____3786)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3787  ->
    match uu____3787 with
    | (lid,t,doc_opt) ->
        let uu____3803 =
          let uu____3804 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3805 =
            let uu____3806 = p_lident lid in
            let uu____3807 =
              let uu____3808 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3808 in
            FStar_Pprint.op_Hat_Hat uu____3806 uu____3807 in
          FStar_Pprint.op_Hat_Hat uu____3804 uu____3805 in
        FStar_Pprint.group uu____3803
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3809  ->
    match uu____3809 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3837 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3838 =
          let uu____3839 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3840 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3845 =
                   let uu____3846 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3846 in
                 let uu____3847 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3845 uu____3847) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3839 uu____3840 in
        FStar_Pprint.op_Hat_Hat uu____3837 uu____3838
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3848  ->
    match uu____3848 with
    | (pat,uu____3854) ->
        let uu____3855 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3866 =
                let uu____3867 =
                  let uu____3868 =
                    let uu____3869 =
                      let uu____3870 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3870 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3869 in
                  FStar_Pprint.group uu____3868 in
                FStar_Pprint.op_Hat_Hat break1 uu____3867 in
              (pat1, uu____3866)
          | uu____3871 -> (pat, FStar_Pprint.empty) in
        (match uu____3855 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3875);
                     FStar_Parser_AST.prange = uu____3876;_},pats)
                  ->
                  let uu____3886 =
                    let uu____3887 = p_lident x in
                    let uu____3888 =
                      let uu____3889 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____3889 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3887 uu____3888 in
                  FStar_Pprint.group uu____3886
              | uu____3890 ->
                  let uu____3891 =
                    let uu____3892 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____3892 ascr_doc in
                  FStar_Pprint.group uu____3891))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3893  ->
    match uu____3893 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____3901 =
          let uu____3902 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____3902 in
        let uu____3903 = p_term e in prefix2 uu____3901 uu____3903
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___54_3904  ->
    match uu___54_3904 with
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
        let uu____3929 = p_uident uid in
        let uu____3930 = p_binders true bs in
        let uu____3931 =
          let uu____3932 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3932 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3929 uu____3930 uu____3931
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
          let uu____3941 =
            let uu____3942 =
              let uu____3943 =
                let uu____3944 = p_uident uid in
                let uu____3945 = p_binders true bs in
                let uu____3946 =
                  let uu____3947 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3947 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3944 uu____3945 uu____3946 in
              FStar_Pprint.group uu____3943 in
            let uu____3948 =
              let uu____3949 = str "with" in
              let uu____3950 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3949 uu____3950 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3942 uu____3948 in
          braces_with_nesting uu____3941
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3980 =
          let uu____3981 = p_lident lid in
          let uu____3982 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3981 uu____3982 in
        let uu____3983 = p_simpleTerm e in prefix2 uu____3980 uu____3983
    | uu____3984 ->
        let uu____3985 =
          let uu____3986 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3986 in
        failwith uu____3985
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4041 =
        match uu____4041 with
        | (kwd,t) ->
            let uu____4048 =
              let uu____4049 = str kwd in
              let uu____4050 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4049 uu____4050 in
            let uu____4051 = p_simpleTerm t in prefix2 uu____4048 uu____4051 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4056 =
      let uu____4057 =
        let uu____4058 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4059 =
          let uu____4060 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4060 in
        FStar_Pprint.op_Hat_Hat uu____4058 uu____4059 in
      let uu____4061 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4057 uu____4061 in
    let uu____4062 =
      let uu____4063 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4063 in
    FStar_Pprint.op_Hat_Hat uu____4056 uu____4062
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___55_4064  ->
    match uu___55_4064 with
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
    let uu____4066 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4066
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___56_4067  ->
    match uu___56_4067 with
    | FStar_Parser_AST.Rec  ->
        let uu____4068 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4068
    | FStar_Parser_AST.Mutable  ->
        let uu____4069 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4069
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___57_4070  ->
    match uu___57_4070 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4075 =
          let uu____4076 =
            let uu____4077 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4077 in
          FStar_Pprint.separate_map uu____4076 p_tuplePattern pats in
        FStar_Pprint.group uu____4075
    | uu____4078 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4085 =
          let uu____4086 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4086 p_constructorPattern pats in
        FStar_Pprint.group uu____4085
    | uu____4087 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4090;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4095 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4096 = p_constructorPattern hd1 in
        let uu____4097 = p_constructorPattern tl1 in
        infix0 uu____4095 uu____4096 uu____4097
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4099;_},pats)
        ->
        let uu____4105 = p_quident uid in
        let uu____4106 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4105 uu____4106
    | uu____4107 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4111 =
          let uu____4116 =
            let uu____4117 = unparen t in uu____4117.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4116) in
        (match uu____4111 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4122;
               FStar_Parser_AST.blevel = uu____4123;
               FStar_Parser_AST.aqual = uu____4124;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4130 =
               let uu____4131 = p_ident lid in
               p_refinement aqual uu____4131 t1 phi in
             soft_parens_with_nesting uu____4130
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4133;
               FStar_Parser_AST.blevel = uu____4134;
               FStar_Parser_AST.aqual = uu____4135;_},phi))
             ->
             let uu____4137 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4137
         | uu____4138 ->
             let uu____4143 =
               let uu____4144 = p_tuplePattern pat in
               let uu____4145 =
                 let uu____4146 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4147 =
                   let uu____4148 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4148 in
                 FStar_Pprint.op_Hat_Hat uu____4146 uu____4147 in
               FStar_Pprint.op_Hat_Hat uu____4144 uu____4145 in
             soft_parens_with_nesting uu____4143)
    | FStar_Parser_AST.PatList pats ->
        let uu____4152 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4152 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4167 =
          match uu____4167 with
          | (lid,pat) ->
              let uu____4174 = p_qlident lid in
              let uu____4175 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4174 uu____4175 in
        let uu____4176 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4176
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4186 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4187 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4188 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4186 uu____4187 uu____4188
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4199 =
          let uu____4200 =
            let uu____4201 = str (FStar_Ident.text_of_id op) in
            let uu____4202 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4201 uu____4202 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4200 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4199
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4210 = FStar_Pprint.optional p_aqual aqual in
        let uu____4211 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4210 uu____4211
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4213 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4216;
           FStar_Parser_AST.prange = uu____4217;_},uu____4218)
        ->
        let uu____4223 = p_tuplePattern p in
        soft_parens_with_nesting uu____4223
    | FStar_Parser_AST.PatTuple (uu____4224,false ) ->
        let uu____4229 = p_tuplePattern p in
        soft_parens_with_nesting uu____4229
    | uu____4230 ->
        let uu____4231 =
          let uu____4232 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4232 in
        failwith uu____4231
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4236 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4237 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4236 uu____4237
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4242 =
              let uu____4243 = unparen t in uu____4243.FStar_Parser_AST.tm in
            match uu____4242 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4246;
                   FStar_Parser_AST.blevel = uu____4247;
                   FStar_Parser_AST.aqual = uu____4248;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4250 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4250 t1 phi
            | uu____4251 ->
                let uu____4252 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4253 =
                  let uu____4254 = p_lident lid in
                  let uu____4255 =
                    let uu____4256 =
                      let uu____4257 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4258 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4257 uu____4258 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4256 in
                  FStar_Pprint.op_Hat_Hat uu____4254 uu____4255 in
                FStar_Pprint.op_Hat_Hat uu____4252 uu____4253 in
          if is_atomic
          then
            let uu____4259 =
              let uu____4260 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4260 in
            FStar_Pprint.group uu____4259
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4262 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4268 =
            let uu____4269 = unparen t in uu____4269.FStar_Parser_AST.tm in
          (match uu____4268 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4271;
                  FStar_Parser_AST.blevel = uu____4272;
                  FStar_Parser_AST.aqual = uu____4273;_},phi)
               ->
               if is_atomic
               then
                 let uu____4275 =
                   let uu____4276 =
                     let uu____4277 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4277 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4276 in
                 FStar_Pprint.group uu____4275
               else
                 (let uu____4279 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4279)
           | uu____4280 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4288 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4289 =
            let uu____4290 =
              let uu____4291 =
                let uu____4292 = p_appTerm t in
                let uu____4293 =
                  let uu____4294 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4294 in
                FStar_Pprint.op_Hat_Hat uu____4292 uu____4293 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4291 in
            FStar_Pprint.op_Hat_Hat binder uu____4290 in
          FStar_Pprint.op_Hat_Hat uu____4288 uu____4289
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
    let uu____4308 =
      let uu____4309 = unparen e in uu____4309.FStar_Parser_AST.tm in
    match uu____4308 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4312 =
          let uu____4313 =
            let uu____4314 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4314 FStar_Pprint.semi in
          FStar_Pprint.group uu____4313 in
        let uu____4315 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4312 uu____4315
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4319 =
          let uu____4320 =
            let uu____4321 =
              let uu____4322 = p_lident x in
              let uu____4323 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4322 uu____4323 in
            let uu____4324 =
              let uu____4325 = p_noSeqTerm e1 in
              let uu____4326 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4325 uu____4326 in
            op_Hat_Slash_Plus_Hat uu____4321 uu____4324 in
          FStar_Pprint.group uu____4320 in
        let uu____4327 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4319 uu____4327
    | uu____4328 ->
        let uu____4329 = p_noSeqTerm e in FStar_Pprint.group uu____4329
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4332 =
      let uu____4333 = unparen e in uu____4333.FStar_Parser_AST.tm in
    match uu____4332 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4338 =
          let uu____4339 = p_tmIff e1 in
          let uu____4340 =
            let uu____4341 =
              let uu____4342 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4342 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4341 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4339 uu____4340 in
        FStar_Pprint.group uu____4338
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4348 =
          let uu____4349 = p_tmIff e1 in
          let uu____4350 =
            let uu____4351 =
              let uu____4352 =
                let uu____4353 = p_typ t in
                let uu____4354 =
                  let uu____4355 = str "by" in
                  let uu____4356 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4355 uu____4356 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4353 uu____4354 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4352 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4351 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4349 uu____4350 in
        FStar_Pprint.group uu____4348
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4357;_},e1::e2::e3::[])
        ->
        let uu____4363 =
          let uu____4364 =
            let uu____4365 =
              let uu____4366 = p_atomicTermNotQUident e1 in
              let uu____4367 =
                let uu____4368 =
                  let uu____4369 =
                    let uu____4370 = p_term e2 in
                    soft_parens_with_nesting uu____4370 in
                  let uu____4371 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4369 uu____4371 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4368 in
              FStar_Pprint.op_Hat_Hat uu____4366 uu____4367 in
            FStar_Pprint.group uu____4365 in
          let uu____4372 =
            let uu____4373 = p_noSeqTerm e3 in jump2 uu____4373 in
          FStar_Pprint.op_Hat_Hat uu____4364 uu____4372 in
        FStar_Pprint.group uu____4363
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4374;_},e1::e2::e3::[])
        ->
        let uu____4380 =
          let uu____4381 =
            let uu____4382 =
              let uu____4383 = p_atomicTermNotQUident e1 in
              let uu____4384 =
                let uu____4385 =
                  let uu____4386 =
                    let uu____4387 = p_term e2 in
                    soft_brackets_with_nesting uu____4387 in
                  let uu____4388 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4386 uu____4388 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4385 in
              FStar_Pprint.op_Hat_Hat uu____4383 uu____4384 in
            FStar_Pprint.group uu____4382 in
          let uu____4389 =
            let uu____4390 = p_noSeqTerm e3 in jump2 uu____4390 in
          FStar_Pprint.op_Hat_Hat uu____4381 uu____4389 in
        FStar_Pprint.group uu____4380
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4400 =
          let uu____4401 = str "requires" in
          let uu____4402 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4401 uu____4402 in
        FStar_Pprint.group uu____4400
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4412 =
          let uu____4413 = str "ensures" in
          let uu____4414 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4413 uu____4414 in
        FStar_Pprint.group uu____4412
    | FStar_Parser_AST.Attributes es ->
        let uu____4418 =
          let uu____4419 = str "attributes" in
          let uu____4420 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4419 uu____4420 in
        FStar_Pprint.group uu____4418
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4424 = is_unit e3 in
        if uu____4424
        then
          let uu____4425 =
            let uu____4426 =
              let uu____4427 = str "if" in
              let uu____4428 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4427 uu____4428 in
            let uu____4429 =
              let uu____4430 = str "then" in
              let uu____4431 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4430 uu____4431 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4426 uu____4429 in
          FStar_Pprint.group uu____4425
        else
          (let e2_doc =
             let uu____4434 =
               let uu____4435 = unparen e2 in uu____4435.FStar_Parser_AST.tm in
             match uu____4434 with
             | FStar_Parser_AST.If (uu____4436,uu____4437,e31) when
                 is_unit e31 ->
                 let uu____4439 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4439
             | uu____4440 -> p_noSeqTerm e2 in
           let uu____4441 =
             let uu____4442 =
               let uu____4443 = str "if" in
               let uu____4444 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4443 uu____4444 in
             let uu____4445 =
               let uu____4446 =
                 let uu____4447 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4447 e2_doc in
               let uu____4448 =
                 let uu____4449 = str "else" in
                 let uu____4450 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4449 uu____4450 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4446 uu____4448 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4442 uu____4445 in
           FStar_Pprint.group uu____4441)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4473 =
          let uu____4474 =
            let uu____4475 = str "try" in
            let uu____4476 = p_noSeqTerm e1 in prefix2 uu____4475 uu____4476 in
          let uu____4477 =
            let uu____4478 = str "with" in
            let uu____4479 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4478 uu____4479 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4474 uu____4477 in
        FStar_Pprint.group uu____4473
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4510 =
          let uu____4511 =
            let uu____4512 = str "match" in
            let uu____4513 = p_noSeqTerm e1 in
            let uu____4514 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4512 uu____4513 uu____4514 in
          let uu____4515 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4511 uu____4515 in
        FStar_Pprint.group uu____4510
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4526 =
          let uu____4527 =
            let uu____4528 = str "let open" in
            let uu____4529 = p_quident uid in
            let uu____4530 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4528 uu____4529 uu____4530 in
          let uu____4531 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4527 uu____4531 in
        FStar_Pprint.group uu____4526
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4548 = str "let" in
          let uu____4549 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4548 uu____4549 in
        let uu____4550 =
          let uu____4551 =
            let uu____4552 =
              let uu____4553 = str "and" in
              precede_break_separate_map let_doc uu____4553 p_letbinding lbs in
            let uu____4558 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4552 uu____4558 in
          FStar_Pprint.group uu____4551 in
        let uu____4559 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4550 uu____4559
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4562;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4565;
                                                         FStar_Parser_AST.level
                                                           = uu____4566;_})
        when matches_var maybe_x x ->
        let uu____4593 =
          let uu____4594 = str "function" in
          let uu____4595 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4594 uu____4595 in
        FStar_Pprint.group uu____4593
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4606 =
          let uu____4607 = p_lident id1 in
          let uu____4608 =
            let uu____4609 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4609 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4607 uu____4608 in
        FStar_Pprint.group uu____4606
    | uu____4610 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4613 =
      let uu____4614 = unparen e in uu____4614.FStar_Parser_AST.tm in
    match uu____4613 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4630 =
          let uu____4631 =
            let uu____4632 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4632 FStar_Pprint.space in
          let uu____4633 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4631 uu____4633 FStar_Pprint.dot in
        let uu____4634 =
          let uu____4635 = p_trigger trigger in
          let uu____4636 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4635 uu____4636 in
        prefix2 uu____4630 uu____4634
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4652 =
          let uu____4653 =
            let uu____4654 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4654 FStar_Pprint.space in
          let uu____4655 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4653 uu____4655 FStar_Pprint.dot in
        let uu____4656 =
          let uu____4657 = p_trigger trigger in
          let uu____4658 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4657 uu____4658 in
        prefix2 uu____4652 uu____4656
    | uu____4659 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4661 =
      let uu____4662 = unparen e in uu____4662.FStar_Parser_AST.tm in
    match uu____4661 with
    | FStar_Parser_AST.QForall uu____4663 -> str "forall"
    | FStar_Parser_AST.QExists uu____4676 -> str "exists"
    | uu____4689 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___58_4690  ->
    match uu___58_4690 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4702 =
          let uu____4703 =
            let uu____4704 = str "pattern" in
            let uu____4705 =
              let uu____4706 =
                let uu____4707 = p_disjunctivePats pats in jump2 uu____4707 in
              let uu____4708 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4706 uu____4708 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4704 uu____4705 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4703 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4702
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4714 = str "\\/" in
    FStar_Pprint.separate_map uu____4714 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4720 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4720
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4722 =
      let uu____4723 = unparen e in uu____4723.FStar_Parser_AST.tm in
    match uu____4722 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4730 =
          let uu____4731 = str "fun" in
          let uu____4732 =
            let uu____4733 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4733 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4731 uu____4732 in
        let uu____4734 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4730 uu____4734
    | uu____4735 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4738  ->
    match uu____4738 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4757 =
            let uu____4758 = unparen e in uu____4758.FStar_Parser_AST.tm in
          match uu____4757 with
          | FStar_Parser_AST.Match uu____4761 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4776 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4792);
                 FStar_Parser_AST.prange = uu____4793;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4795);
                                                               FStar_Parser_AST.range
                                                                 = uu____4796;
                                                               FStar_Parser_AST.level
                                                                 = uu____4797;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4824 -> (fun x  -> x) in
        let uu____4826 =
          let uu____4827 =
            let uu____4828 =
              let uu____4829 =
                let uu____4830 =
                  let uu____4831 = p_disjunctivePattern pat in
                  let uu____4832 =
                    let uu____4833 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4833 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4831 uu____4832 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4830 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4829 in
            FStar_Pprint.group uu____4828 in
          let uu____4834 =
            let uu____4835 = p_term e in maybe_paren uu____4835 in
          op_Hat_Slash_Plus_Hat uu____4827 uu____4834 in
        FStar_Pprint.group uu____4826
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___59_4836  ->
    match uu___59_4836 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4840 = str "when" in
        let uu____4841 =
          let uu____4842 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4842 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4840 uu____4841
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4844 =
      let uu____4845 = unparen e in uu____4845.FStar_Parser_AST.tm in
    match uu____4844 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4846;_},e1::e2::[])
        ->
        let uu____4851 = str "<==>" in
        let uu____4852 = p_tmImplies e1 in
        let uu____4853 = p_tmIff e2 in
        infix0 uu____4851 uu____4852 uu____4853
    | uu____4854 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4856 =
      let uu____4857 = unparen e in uu____4857.FStar_Parser_AST.tm in
    match uu____4856 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4858;_},e1::e2::[])
        ->
        let uu____4863 = str "==>" in
        let uu____4864 = p_tmArrow p_tmFormula e1 in
        let uu____4865 = p_tmImplies e2 in
        infix0 uu____4863 uu____4864 uu____4865
    | uu____4866 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4871 =
        let uu____4872 = unparen e in uu____4872.FStar_Parser_AST.tm in
      match uu____4871 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4879 =
            let uu____4880 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4885 = p_binder false b in
                   let uu____4886 =
                     let uu____4887 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4887 in
                   FStar_Pprint.op_Hat_Hat uu____4885 uu____4886) bs in
            let uu____4888 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4880 uu____4888 in
          FStar_Pprint.group uu____4879
      | uu____4889 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4891 =
      let uu____4892 = unparen e in uu____4892.FStar_Parser_AST.tm in
    match uu____4891 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4893;_},e1::e2::[])
        ->
        let uu____4898 = str "\\/" in
        let uu____4899 = p_tmFormula e1 in
        let uu____4900 = p_tmConjunction e2 in
        infix0 uu____4898 uu____4899 uu____4900
    | uu____4901 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4903 =
      let uu____4904 = unparen e in uu____4904.FStar_Parser_AST.tm in
    match uu____4903 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4905;_},e1::e2::[])
        ->
        let uu____4910 = str "/\\" in
        let uu____4911 = p_tmConjunction e1 in
        let uu____4912 = p_tmTuple e2 in
        infix0 uu____4910 uu____4911 uu____4912
    | uu____4913 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4916 =
      let uu____4917 = unparen e in uu____4917.FStar_Parser_AST.tm in
    match uu____4916 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4932 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4932
          (fun uu____4940  ->
             match uu____4940 with | (e1,uu____4946) -> p_tmEq e1) args
    | uu____4947 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4952 =
             let uu____4953 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4953 in
           FStar_Pprint.group uu____4952)
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
      let uu____5004 =
        let uu____5005 = unparen e in uu____5005.FStar_Parser_AST.tm in
      match uu____5004 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5012 = levels op1 in
          (match uu____5012 with
           | (left1,mine,right1) ->
               let uu____5022 =
                 let uu____5023 = FStar_All.pipe_left str op1 in
                 let uu____5024 = p_tmEq' left1 e1 in
                 let uu____5025 = p_tmEq' right1 e2 in
                 infix0 uu____5023 uu____5024 uu____5025 in
               paren_if curr mine uu____5022)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5026;_},e1::e2::[])
          ->
          let uu____5031 =
            let uu____5032 = p_tmEq e1 in
            let uu____5033 =
              let uu____5034 =
                let uu____5035 =
                  let uu____5036 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5036 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5035 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5034 in
            FStar_Pprint.op_Hat_Hat uu____5032 uu____5033 in
          FStar_Pprint.group uu____5031
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5037;_},e1::[])
          ->
          let uu____5041 = levels "-" in
          (match uu____5041 with
           | (left1,mine,right1) ->
               let uu____5051 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5051)
      | uu____5052 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5115 =
        let uu____5116 = unparen e in uu____5116.FStar_Parser_AST.tm in
      match uu____5115 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5119)::(e2,uu____5121)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5141 = is_list e in Prims.op_Negation uu____5141)
          ->
          let op = "::" in
          let uu____5143 = levels op in
          (match uu____5143 with
           | (left1,mine,right1) ->
               let uu____5153 =
                 let uu____5154 = str op in
                 let uu____5155 = p_tmNoEq' left1 e1 in
                 let uu____5156 = p_tmNoEq' right1 e2 in
                 infix0 uu____5154 uu____5155 uu____5156 in
               paren_if curr mine uu____5153)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5164 = levels op in
          (match uu____5164 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5178 = p_binder false b in
                 let uu____5179 =
                   let uu____5180 =
                     let uu____5181 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5181 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5180 in
                 FStar_Pprint.op_Hat_Hat uu____5178 uu____5179 in
               let uu____5182 =
                 let uu____5183 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5184 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5183 uu____5184 in
               paren_if curr mine uu____5182)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5191 = levels op1 in
          (match uu____5191 with
           | (left1,mine,right1) ->
               let uu____5201 =
                 let uu____5202 = str op1 in
                 let uu____5203 = p_tmNoEq' left1 e1 in
                 let uu____5204 = p_tmNoEq' right1 e2 in
                 infix0 uu____5202 uu____5203 uu____5204 in
               paren_if curr mine uu____5201)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5207 =
            let uu____5208 = p_lidentOrUnderscore lid in
            let uu____5209 =
              let uu____5210 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5210 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5208 uu____5209 in
          FStar_Pprint.group uu____5207
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5231 =
            let uu____5232 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5233 =
              let uu____5234 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5234 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5232 uu____5233 in
          braces_with_nesting uu____5231
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5239;_},e1::[])
          ->
          let uu____5243 =
            let uu____5244 = str "~" in
            let uu____5245 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5244 uu____5245 in
          FStar_Pprint.group uu____5243
      | uu____5246 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5248 = p_appTerm e in
    let uu____5249 =
      let uu____5250 =
        let uu____5251 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5251 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5250 in
    FStar_Pprint.op_Hat_Hat uu____5248 uu____5249
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5256 =
            let uu____5257 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5257 t phi in
          soft_parens_with_nesting uu____5256
      | FStar_Parser_AST.TAnnotated uu____5258 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5263 ->
          let uu____5264 =
            let uu____5265 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5265 in
          failwith uu____5264
      | FStar_Parser_AST.TVariable uu____5266 ->
          let uu____5267 =
            let uu____5268 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5268 in
          failwith uu____5267
      | FStar_Parser_AST.NoName uu____5269 ->
          let uu____5270 =
            let uu____5271 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5271 in
          failwith uu____5270
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5272  ->
    match uu____5272 with
    | (lid,e) ->
        let uu____5279 =
          let uu____5280 = p_qlident lid in
          let uu____5281 =
            let uu____5282 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5282 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5280 uu____5281 in
        FStar_Pprint.group uu____5279
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5284 =
      let uu____5285 = unparen e in uu____5285.FStar_Parser_AST.tm in
    match uu____5284 with
    | FStar_Parser_AST.App uu____5286 when is_general_application e ->
        let uu____5293 = head_and_args e in
        (match uu____5293 with
         | (head1,args) ->
             let uu____5318 =
               let uu____5329 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5329
               then
                 let uu____5359 =
                   FStar_Util.take
                     (fun uu____5383  ->
                        match uu____5383 with
                        | (uu____5388,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5359 with
                 | (fs_typ_args,args1) ->
                     let uu____5426 =
                       let uu____5427 = p_indexingTerm head1 in
                       let uu____5428 =
                         let uu____5429 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5429 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5427 uu____5428 in
                     (uu____5426, args1)
               else
                 (let uu____5441 = p_indexingTerm head1 in (uu____5441, args)) in
             (match uu____5318 with
              | (head_doc,args1) ->
                  let uu____5462 =
                    let uu____5463 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5463 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5462))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5483 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5483)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5501 =
               let uu____5502 = p_quident lid in
               let uu____5503 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5502 uu____5503 in
             FStar_Pprint.group uu____5501
         | hd1::tl1 ->
             let uu____5520 =
               let uu____5521 =
                 let uu____5522 =
                   let uu____5523 = p_quident lid in
                   let uu____5524 = p_argTerm hd1 in
                   prefix2 uu____5523 uu____5524 in
                 FStar_Pprint.group uu____5522 in
               let uu____5525 =
                 let uu____5526 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5526 in
               FStar_Pprint.op_Hat_Hat uu____5521 uu____5525 in
             FStar_Pprint.group uu____5520)
    | uu____5531 -> p_indexingTerm e
and p_argTerm:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____5540 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5540 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5542 = str "#" in
        let uu____5543 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5542 uu____5543
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5545  ->
    match uu____5545 with | (e,uu____5551) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5556 =
        let uu____5557 = unparen e in uu____5557.FStar_Parser_AST.tm in
      match uu____5556 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5558;_},e1::e2::[])
          ->
          let uu____5563 =
            let uu____5564 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5565 =
              let uu____5566 =
                let uu____5567 = p_term e2 in
                soft_parens_with_nesting uu____5567 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5566 in
            FStar_Pprint.op_Hat_Hat uu____5564 uu____5565 in
          FStar_Pprint.group uu____5563
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5568;_},e1::e2::[])
          ->
          let uu____5573 =
            let uu____5574 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5575 =
              let uu____5576 =
                let uu____5577 = p_term e2 in
                soft_brackets_with_nesting uu____5577 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5576 in
            FStar_Pprint.op_Hat_Hat uu____5574 uu____5575 in
          FStar_Pprint.group uu____5573
      | uu____5578 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5581 =
      let uu____5582 = unparen e in uu____5582.FStar_Parser_AST.tm in
    match uu____5581 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5585 = p_quident lid in
        let uu____5586 =
          let uu____5587 =
            let uu____5588 = p_term e1 in soft_parens_with_nesting uu____5588 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5587 in
        FStar_Pprint.op_Hat_Hat uu____5585 uu____5586
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5594 = str (FStar_Ident.text_of_id op) in
        let uu____5595 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5594 uu____5595
    | uu____5596 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5598 =
      let uu____5599 = unparen e in uu____5599.FStar_Parser_AST.tm in
    match uu____5598 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5605 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5612 = str (FStar_Ident.text_of_id op) in
        let uu____5613 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5612 uu____5613
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5617 =
          let uu____5618 =
            let uu____5619 = str (FStar_Ident.text_of_id op) in
            let uu____5620 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5619 uu____5620 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5618 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5617
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5635 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5636 =
          let uu____5637 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5638 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5637 p_tmEq uu____5638 in
        let uu____5645 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5635 uu____5636 uu____5645
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5648 =
          let uu____5649 = p_atomicTermNotQUident e1 in
          let uu____5650 =
            let uu____5651 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5651 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5649 uu____5650 in
        FStar_Pprint.group uu____5648
    | uu____5652 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5654 =
      let uu____5655 = unparen e in uu____5655.FStar_Parser_AST.tm in
    match uu____5654 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5659 = p_quident constr_lid in
        let uu____5660 =
          let uu____5661 =
            let uu____5662 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5662 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5661 in
        FStar_Pprint.op_Hat_Hat uu____5659 uu____5660
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5664 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5664 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5666 = p_term e1 in soft_parens_with_nesting uu____5666
    | uu____5667 when is_array e ->
        let es = extract_from_list e in
        let uu____5671 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5672 =
          let uu____5673 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5673 p_noSeqTerm es in
        let uu____5674 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5671 uu____5672 uu____5674
    | uu____5675 when is_list e ->
        let uu____5676 =
          let uu____5677 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5678 = extract_from_list e in
          separate_map_or_flow uu____5677 p_noSeqTerm uu____5678 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5676 FStar_Pprint.rbracket
    | uu____5681 when is_lex_list e ->
        let uu____5682 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5683 =
          let uu____5684 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5685 = extract_from_list e in
          separate_map_or_flow uu____5684 p_noSeqTerm uu____5685 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5682 uu____5683 FStar_Pprint.rbracket
    | uu____5688 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5692 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5693 =
          let uu____5694 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5694 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5692 uu____5693 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5698 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5699 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5698 uu____5699
    | FStar_Parser_AST.Op (op,args) when
        let uu____5706 = handleable_op op args in
        Prims.op_Negation uu____5706 ->
        let uu____5707 =
          let uu____5708 =
            let uu____5709 =
              let uu____5710 =
                let uu____5711 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5711
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5710 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5709 in
          Prims.strcat "Operation " uu____5708 in
        failwith uu____5707
    | FStar_Parser_AST.Uvar uu____5712 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5713 = p_term e in soft_parens_with_nesting uu____5713
    | FStar_Parser_AST.Const uu____5714 ->
        let uu____5715 = p_term e in soft_parens_with_nesting uu____5715
    | FStar_Parser_AST.Op uu____5716 ->
        let uu____5723 = p_term e in soft_parens_with_nesting uu____5723
    | FStar_Parser_AST.Tvar uu____5724 ->
        let uu____5725 = p_term e in soft_parens_with_nesting uu____5725
    | FStar_Parser_AST.Var uu____5726 ->
        let uu____5727 = p_term e in soft_parens_with_nesting uu____5727
    | FStar_Parser_AST.Name uu____5728 ->
        let uu____5729 = p_term e in soft_parens_with_nesting uu____5729
    | FStar_Parser_AST.Construct uu____5730 ->
        let uu____5741 = p_term e in soft_parens_with_nesting uu____5741
    | FStar_Parser_AST.Abs uu____5742 ->
        let uu____5749 = p_term e in soft_parens_with_nesting uu____5749
    | FStar_Parser_AST.App uu____5750 ->
        let uu____5757 = p_term e in soft_parens_with_nesting uu____5757
    | FStar_Parser_AST.Let uu____5758 ->
        let uu____5771 = p_term e in soft_parens_with_nesting uu____5771
    | FStar_Parser_AST.LetOpen uu____5772 ->
        let uu____5777 = p_term e in soft_parens_with_nesting uu____5777
    | FStar_Parser_AST.Seq uu____5778 ->
        let uu____5783 = p_term e in soft_parens_with_nesting uu____5783
    | FStar_Parser_AST.Bind uu____5784 ->
        let uu____5791 = p_term e in soft_parens_with_nesting uu____5791
    | FStar_Parser_AST.If uu____5792 ->
        let uu____5799 = p_term e in soft_parens_with_nesting uu____5799
    | FStar_Parser_AST.Match uu____5800 ->
        let uu____5815 = p_term e in soft_parens_with_nesting uu____5815
    | FStar_Parser_AST.TryWith uu____5816 ->
        let uu____5831 = p_term e in soft_parens_with_nesting uu____5831
    | FStar_Parser_AST.Ascribed uu____5832 ->
        let uu____5841 = p_term e in soft_parens_with_nesting uu____5841
    | FStar_Parser_AST.Record uu____5842 ->
        let uu____5855 = p_term e in soft_parens_with_nesting uu____5855
    | FStar_Parser_AST.Project uu____5856 ->
        let uu____5861 = p_term e in soft_parens_with_nesting uu____5861
    | FStar_Parser_AST.Product uu____5862 ->
        let uu____5869 = p_term e in soft_parens_with_nesting uu____5869
    | FStar_Parser_AST.Sum uu____5870 ->
        let uu____5877 = p_term e in soft_parens_with_nesting uu____5877
    | FStar_Parser_AST.QForall uu____5878 ->
        let uu____5891 = p_term e in soft_parens_with_nesting uu____5891
    | FStar_Parser_AST.QExists uu____5892 ->
        let uu____5905 = p_term e in soft_parens_with_nesting uu____5905
    | FStar_Parser_AST.Refine uu____5906 ->
        let uu____5911 = p_term e in soft_parens_with_nesting uu____5911
    | FStar_Parser_AST.NamedTyp uu____5912 ->
        let uu____5917 = p_term e in soft_parens_with_nesting uu____5917
    | FStar_Parser_AST.Requires uu____5918 ->
        let uu____5925 = p_term e in soft_parens_with_nesting uu____5925
    | FStar_Parser_AST.Ensures uu____5926 ->
        let uu____5933 = p_term e in soft_parens_with_nesting uu____5933
    | FStar_Parser_AST.Assign uu____5934 ->
        let uu____5939 = p_term e in soft_parens_with_nesting uu____5939
    | FStar_Parser_AST.Attributes uu____5940 ->
        let uu____5943 = p_term e in soft_parens_with_nesting uu____5943
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___62_5944  ->
    match uu___62_5944 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5948 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5948
    | FStar_Const.Const_string (s,uu____5950) ->
        let uu____5951 = str s in FStar_Pprint.dquotes uu____5951
    | FStar_Const.Const_bytearray (bytes,uu____5953) ->
        let uu____5958 =
          let uu____5959 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5959 in
        let uu____5960 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5958 uu____5960
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___60_5978 =
          match uu___60_5978 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___61_5982 =
          match uu___61_5982 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5993  ->
               match uu____5993 with
               | (s,w) ->
                   let uu____6000 = signedness s in
                   let uu____6001 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6000 uu____6001)
            sign_width_opt in
        let uu____6002 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6002 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6004 = FStar_Range.string_of_range r in str uu____6004
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6006 = p_quident lid in
        let uu____6007 =
          let uu____6008 =
            let uu____6009 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6009 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6008 in
        FStar_Pprint.op_Hat_Hat uu____6006 uu____6007
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6011 = str "u#" in
    let uu____6012 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6011 uu____6012
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6014 =
      let uu____6015 = unparen u in uu____6015.FStar_Parser_AST.tm in
    match uu____6014 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6016;_},u1::u2::[])
        ->
        let uu____6021 =
          let uu____6022 = p_universeFrom u1 in
          let uu____6023 =
            let uu____6024 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6024 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6022 uu____6023 in
        FStar_Pprint.group uu____6021
    | FStar_Parser_AST.App uu____6025 ->
        let uu____6032 = head_and_args u in
        (match uu____6032 with
         | (head1,args) ->
             let uu____6057 =
               let uu____6058 = unparen head1 in
               uu____6058.FStar_Parser_AST.tm in
             (match uu____6057 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6060 =
                    let uu____6061 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6062 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6070  ->
                           match uu____6070 with
                           | (u1,uu____6076) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6061 uu____6062 in
                  FStar_Pprint.group uu____6060
              | uu____6077 ->
                  let uu____6078 =
                    let uu____6079 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6079 in
                  failwith uu____6078))
    | uu____6080 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6082 =
      let uu____6083 = unparen u in uu____6083.FStar_Parser_AST.tm in
    match uu____6082 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6106 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6106
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6107;_},uu____6108::uu____6109::[])
        ->
        let uu____6112 = p_universeFrom u in
        soft_parens_with_nesting uu____6112
    | FStar_Parser_AST.App uu____6113 ->
        let uu____6120 = p_universeFrom u in
        soft_parens_with_nesting uu____6120
    | uu____6121 ->
        let uu____6122 =
          let uu____6123 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6123 in
        failwith uu____6122
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
       | FStar_Parser_AST.Module (uu____6163,decls) ->
           let uu____6169 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6169
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6178,decls,uu____6180) ->
           let uu____6185 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6185
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6236  ->
         match uu____6236 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6276,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6282,decls,uu____6284) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6329 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6342;
                 FStar_Parser_AST.doc = uu____6343;
                 FStar_Parser_AST.quals = uu____6344;
                 FStar_Parser_AST.attrs = uu____6345;_}::uu____6346 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6352 =
                   let uu____6355 =
                     let uu____6358 = FStar_List.tl ds in d :: uu____6358 in
                   d0 :: uu____6355 in
                 (uu____6352, (d0.FStar_Parser_AST.drange))
             | uu____6363 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6329 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6421 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6421 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6517 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6517, comments1))))))