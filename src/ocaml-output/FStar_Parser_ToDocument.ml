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
      let uu____845 =
        let uu____846 = unparen e1 in uu____846.FStar_Parser_AST.tm in
      match uu____845 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____864 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____879 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____884 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____889 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___91_907  ->
    match uu___91_907 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___92_937  ->
      match uu___92_937 with
      | FStar_Util.Inl c ->
          let uu____943 = FStar_String.get s (Prims.parse_int "0") in
          uu____943 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____967 .
    Prims.string ->
      ('Auu____967,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____985  ->
      match uu____985 with
      | (assoc_levels,tokens) ->
          let uu____1010 = FStar_List.tryFind (matches_token s) tokens in
          uu____1010 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1033 .
    Prims.unit ->
      (associativity,('Auu____1033,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1044  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1061 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1061) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1072  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1097 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1097) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1108  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1129 .
    Prims.unit ->
      (associativity,('Auu____1129,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1140  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1157 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1157) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1168  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1189 .
    Prims.unit ->
      (associativity,('Auu____1189,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1200  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1217 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1217) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1228  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1245 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1245) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1256  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1281 .
    Prims.unit ->
      (associativity,('Auu____1281,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1292  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1309 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1309) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1320  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1337 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1337) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1348  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1365 .
    Prims.unit ->
      (associativity,('Auu____1365,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1376  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1393 .
    Prims.unit ->
      (associativity,('Auu____1393,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1404  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1421 .
    Prims.unit ->
      (associativity,('Auu____1421,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1432  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___93_1619 =
    match uu___93_1619 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1657  ->
         match uu____1657 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1734 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1734 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1782) ->
          assoc_levels
      | uu____1823 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1861 .
    ('Auu____1861,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1917 =
        FStar_List.tryFind
          (fun uu____1955  ->
             match uu____1955 with
             | (uu____1972,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1917 with
      | FStar_Pervasives_Native.Some ((uu____2010,l1,uu____2012),uu____2013)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2064 =
            let uu____2065 =
              let uu____2066 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2066 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2065 in
          failwith uu____2064 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2100 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2100) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2113  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2188 =
      let uu____2201 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2201 (operatorInfix0ad12 ()) in
    uu____2188 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2305 =
      let uu____2318 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2318 opinfix34 in
    uu____2305 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2380 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2380
    then Prims.parse_int "1"
    else
      (let uu____2382 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2382
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2391 . FStar_Ident.ident -> 'Auu____2391 Prims.list -> Prims.bool =
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
      | uu____2404 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2438 .
    ('Auu____2438 -> FStar_Pprint.document) ->
      'Auu____2438 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2470 = FStar_ST.op_Bang comment_stack in
          match uu____2470 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2532 = FStar_Range.range_before_pos crange print_pos in
              if uu____2532
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2572 =
                    let uu____2573 =
                      let uu____2574 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2574
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2573 in
                  comments_before_pos uu____2572 print_pos lookahead_pos))
              else
                (let uu____2576 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2576)) in
        let uu____2577 =
          let uu____2582 =
            let uu____2583 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2583 in
          let uu____2584 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2582 uu____2584 in
        match uu____2577 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2590 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2590
              else comments in
            let uu____2596 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2596
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2613 = FStar_ST.op_Bang comment_stack in
          match uu____2613 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2703 =
                    let uu____2704 =
                      let uu____2705 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2705 in
                    uu____2704 - lbegin in
                  max k uu____2703 in
                let doc2 =
                  let uu____2707 =
                    let uu____2708 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2709 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2708 uu____2709 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2707 in
                let uu____2710 =
                  let uu____2711 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2711 in
                place_comments_until_pos (Prims.parse_int "1") uu____2710
                  pos_end doc2))
          | uu____2712 ->
              let lnum =
                let uu____2720 =
                  let uu____2721 = FStar_Range.line_of_pos pos_end in
                  uu____2721 - lbegin in
                max (Prims.parse_int "1") uu____2720 in
              let uu____2722 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2722
let separate_map_with_comments:
  'Auu____2735 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2735 -> FStar_Pprint.document) ->
          'Auu____2735 Prims.list ->
            ('Auu____2735 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2783 x =
              match uu____2783 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2797 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2797 doc1 in
                  let uu____2798 =
                    let uu____2799 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2799 in
                  let uu____2800 =
                    let uu____2801 =
                      let uu____2802 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2802 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2801 in
                  (uu____2798, uu____2800) in
            let uu____2803 =
              let uu____2810 = FStar_List.hd xs in
              let uu____2811 = FStar_List.tl xs in (uu____2810, uu____2811) in
            match uu____2803 with
            | (x,xs1) ->
                let init1 =
                  let uu____2827 =
                    let uu____2828 =
                      let uu____2829 = extract_range x in
                      FStar_Range.end_of_range uu____2829 in
                    FStar_Range.line_of_pos uu____2828 in
                  let uu____2830 =
                    let uu____2831 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2831 in
                  (uu____2827, uu____2830) in
                let uu____2832 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2832
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3127 =
      let uu____3128 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3129 =
        let uu____3130 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3131 =
          let uu____3132 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3133 =
            let uu____3134 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3134 in
          FStar_Pprint.op_Hat_Hat uu____3132 uu____3133 in
        FStar_Pprint.op_Hat_Hat uu____3130 uu____3131 in
      FStar_Pprint.op_Hat_Hat uu____3128 uu____3129 in
    FStar_Pprint.group uu____3127
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3137 =
      let uu____3138 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3138 in
    let uu____3139 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3137 FStar_Pprint.space uu____3139
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3140  ->
    match uu____3140 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3174 =
                match uu____3174 with
                | (kwd,arg) ->
                    let uu____3181 = str "@" in
                    let uu____3182 =
                      let uu____3183 = str kwd in
                      let uu____3184 =
                        let uu____3185 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3185 in
                      FStar_Pprint.op_Hat_Hat uu____3183 uu____3184 in
                    FStar_Pprint.op_Hat_Hat uu____3181 uu____3182 in
              let uu____3186 =
                let uu____3187 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3187 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3186 in
        let uu____3192 =
          let uu____3193 =
            let uu____3194 =
              let uu____3195 =
                let uu____3196 = str doc1 in
                let uu____3197 =
                  let uu____3198 =
                    let uu____3199 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3199 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3198 in
                FStar_Pprint.op_Hat_Hat uu____3196 uu____3197 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3195 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3194 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3193 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3192
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3203 =
          let uu____3204 = str "val" in
          let uu____3205 =
            let uu____3206 =
              let uu____3207 = p_lident lid in
              let uu____3208 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3207 uu____3208 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3206 in
          FStar_Pprint.op_Hat_Hat uu____3204 uu____3205 in
        let uu____3209 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3203 uu____3209
    | FStar_Parser_AST.TopLevelLet (uu____3210,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3235 =
               let uu____3236 = str "let" in
               let uu____3237 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3236 uu____3237 in
             FStar_Pprint.group uu____3235) lbs
    | uu____3238 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3241 =
          let uu____3242 = str "open" in
          let uu____3243 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3242 uu____3243 in
        FStar_Pprint.group uu____3241
    | FStar_Parser_AST.Include uid ->
        let uu____3245 =
          let uu____3246 = str "include" in
          let uu____3247 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3246 uu____3247 in
        FStar_Pprint.group uu____3245
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3250 =
          let uu____3251 = str "module" in
          let uu____3252 =
            let uu____3253 =
              let uu____3254 = p_uident uid1 in
              let uu____3255 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3254 uu____3255 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3253 in
          FStar_Pprint.op_Hat_Hat uu____3251 uu____3252 in
        let uu____3256 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3250 uu____3256
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3258 =
          let uu____3259 = str "module" in
          let uu____3260 =
            let uu____3261 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3261 in
          FStar_Pprint.op_Hat_Hat uu____3259 uu____3260 in
        FStar_Pprint.group uu____3258
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3294 = str "effect" in
          let uu____3295 =
            let uu____3296 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3296 in
          FStar_Pprint.op_Hat_Hat uu____3294 uu____3295 in
        let uu____3297 =
          let uu____3298 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3298 FStar_Pprint.equals in
        let uu____3299 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3297 uu____3299
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3317 = str "type" in
        let uu____3318 = str "and" in
        precede_break_separate_map uu____3317 uu____3318 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3340 = str "let" in
          let uu____3341 =
            let uu____3342 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3342 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3340 uu____3341 in
        let uu____3343 =
          let uu____3344 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3344 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3343 p_letbinding lbs
          (fun uu____3352  ->
             match uu____3352 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3361 =
          let uu____3362 = str "val" in
          let uu____3363 =
            let uu____3364 =
              let uu____3365 = p_lident lid in
              let uu____3366 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3365 uu____3366 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3364 in
          FStar_Pprint.op_Hat_Hat uu____3362 uu____3363 in
        let uu____3367 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3361 uu____3367
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3371 =
            let uu____3372 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3372 FStar_Util.is_upper in
          if uu____3371
          then FStar_Pprint.empty
          else
            (let uu____3382 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3382 FStar_Pprint.space) in
        let uu____3383 =
          let uu____3384 =
            let uu____3385 = p_ident id1 in
            let uu____3386 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3385 uu____3386 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3384 in
        let uu____3387 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3383 uu____3387
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3394 = str "exception" in
        let uu____3395 =
          let uu____3396 =
            let uu____3397 = p_uident uid in
            let uu____3398 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3403 = str "of" in
                   let uu____3404 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3403 uu____3404) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3397 uu____3398 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3396 in
        FStar_Pprint.op_Hat_Hat uu____3394 uu____3395
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3406 = str "new_effect" in
        let uu____3407 =
          let uu____3408 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3408 in
        FStar_Pprint.op_Hat_Hat uu____3406 uu____3407
    | FStar_Parser_AST.SubEffect se ->
        let uu____3410 = str "sub_effect" in
        let uu____3411 =
          let uu____3412 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3412 in
        FStar_Pprint.op_Hat_Hat uu____3410 uu____3411
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3415 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3415 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3416 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3417) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___94_3434  ->
    match uu___94_3434 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3436 = str "#set-options" in
        let uu____3437 =
          let uu____3438 =
            let uu____3439 = str s in FStar_Pprint.dquotes uu____3439 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3438 in
        FStar_Pprint.op_Hat_Hat uu____3436 uu____3437
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3443 = str "#reset-options" in
        let uu____3444 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3448 =
                 let uu____3449 = str s in FStar_Pprint.dquotes uu____3449 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3448) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3443 uu____3444
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
  fun uu____3464  ->
    match uu____3464 with
    | (typedecl,fsdoc_opt) ->
        let uu____3477 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3478 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3477 uu____3478
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___95_3479  ->
    match uu___95_3479 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3494 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3510 =
          let uu____3511 = p_typ t in prefix2 FStar_Pprint.equals uu____3511 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3555 =
          match uu____3555 with
          | (lid1,t,doc_opt) ->
              let uu____3571 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3571 in
        let p_fields uu____3585 =
          let uu____3586 =
            let uu____3587 =
              let uu____3588 =
                let uu____3589 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3589 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3588 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3587 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3586 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3653 =
          match uu____3653 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3679 =
                  let uu____3680 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3680 in
                FStar_Range.extend_to_end_of_line uu____3679 in
              let p_constructorBranch decl =
                let uu____3713 =
                  let uu____3714 =
                    let uu____3715 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3715 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3714 in
                FStar_Pprint.group uu____3713 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3735 =
          let uu____3736 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3736 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3751  ->
             let uu____3752 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3752)
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
            let uu____3767 = p_ident lid in
            let uu____3768 =
              let uu____3769 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3769 in
            FStar_Pprint.op_Hat_Hat uu____3767 uu____3768
          else
            (let binders_doc =
               let uu____3772 = p_typars bs in
               let uu____3773 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3777 =
                        let uu____3778 =
                          let uu____3779 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3779 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3778 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3777) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3772 uu____3773 in
             let uu____3780 = p_ident lid in
             let uu____3781 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3780 binders_doc uu____3781)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3782  ->
    match uu____3782 with
    | (lid,t,doc_opt) ->
        let uu____3798 =
          let uu____3799 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3800 =
            let uu____3801 = p_lident lid in
            let uu____3802 =
              let uu____3803 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3803 in
            FStar_Pprint.op_Hat_Hat uu____3801 uu____3802 in
          FStar_Pprint.op_Hat_Hat uu____3799 uu____3800 in
        FStar_Pprint.group uu____3798
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3804  ->
    match uu____3804 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3832 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3833 =
          let uu____3834 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3835 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3840 =
                   let uu____3841 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3841 in
                 let uu____3842 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3840 uu____3842) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3834 uu____3835 in
        FStar_Pprint.op_Hat_Hat uu____3832 uu____3833
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3843  ->
    match uu____3843 with
    | (pat,uu____3849) ->
        let uu____3850 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3861 =
                let uu____3862 =
                  let uu____3863 =
                    let uu____3864 =
                      let uu____3865 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3865 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3864 in
                  FStar_Pprint.group uu____3863 in
                FStar_Pprint.op_Hat_Hat break1 uu____3862 in
              (pat1, uu____3861)
          | uu____3866 -> (pat, FStar_Pprint.empty) in
        (match uu____3850 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3870);
                     FStar_Parser_AST.prange = uu____3871;_},pats)
                  ->
                  let uu____3881 =
                    let uu____3882 = p_lident x in
                    let uu____3883 =
                      let uu____3884 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____3884 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3882 uu____3883 in
                  FStar_Pprint.group uu____3881
              | uu____3885 ->
                  let uu____3886 =
                    let uu____3887 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____3887 ascr_doc in
                  FStar_Pprint.group uu____3886))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3888  ->
    match uu____3888 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____3896 =
          let uu____3897 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____3897 in
        let uu____3898 = p_term e in prefix2 uu____3896 uu____3898
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___96_3899  ->
    match uu___96_3899 with
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
        let uu____3924 = p_uident uid in
        let uu____3925 = p_binders true bs in
        let uu____3926 =
          let uu____3927 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____3927 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3924 uu____3925 uu____3926
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
          let uu____3936 =
            let uu____3937 =
              let uu____3938 =
                let uu____3939 = p_uident uid in
                let uu____3940 = p_binders true bs in
                let uu____3941 =
                  let uu____3942 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____3942 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3939 uu____3940 uu____3941 in
              FStar_Pprint.group uu____3938 in
            let uu____3943 =
              let uu____3944 = str "with" in
              let uu____3945 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____3944 uu____3945 in
            FStar_Pprint.op_Hat_Slash_Hat uu____3937 uu____3943 in
          braces_with_nesting uu____3936
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3975 =
          let uu____3976 = p_lident lid in
          let uu____3977 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____3976 uu____3977 in
        let uu____3978 = p_simpleTerm e in prefix2 uu____3975 uu____3978
    | uu____3979 ->
        let uu____3980 =
          let uu____3981 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3981 in
        failwith uu____3980
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4036 =
        match uu____4036 with
        | (kwd,t) ->
            let uu____4043 =
              let uu____4044 = str kwd in
              let uu____4045 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4044 uu____4045 in
            let uu____4046 = p_simpleTerm t in prefix2 uu____4043 uu____4046 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4051 =
      let uu____4052 =
        let uu____4053 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4054 =
          let uu____4055 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4055 in
        FStar_Pprint.op_Hat_Hat uu____4053 uu____4054 in
      let uu____4056 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4052 uu____4056 in
    let uu____4057 =
      let uu____4058 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4058 in
    FStar_Pprint.op_Hat_Hat uu____4051 uu____4057
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___97_4059  ->
    match uu___97_4059 with
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
    let uu____4061 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4061
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___98_4062  ->
    match uu___98_4062 with
    | FStar_Parser_AST.Rec  ->
        let uu____4063 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4063
    | FStar_Parser_AST.Mutable  ->
        let uu____4064 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4064
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___99_4065  ->
    match uu___99_4065 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4070 =
          let uu____4071 =
            let uu____4072 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4072 in
          FStar_Pprint.separate_map uu____4071 p_tuplePattern pats in
        FStar_Pprint.group uu____4070
    | uu____4073 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4080 =
          let uu____4081 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4081 p_constructorPattern pats in
        FStar_Pprint.group uu____4080
    | uu____4082 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4085;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4090 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4091 = p_constructorPattern hd1 in
        let uu____4092 = p_constructorPattern tl1 in
        infix0 uu____4090 uu____4091 uu____4092
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4094;_},pats)
        ->
        let uu____4100 = p_quident uid in
        let uu____4101 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4100 uu____4101
    | uu____4102 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4106 =
          let uu____4111 =
            let uu____4112 = unparen t in uu____4112.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4111) in
        (match uu____4106 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4117;
               FStar_Parser_AST.blevel = uu____4118;
               FStar_Parser_AST.aqual = uu____4119;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4125 =
               let uu____4126 = p_ident lid in
               p_refinement aqual uu____4126 t1 phi in
             soft_parens_with_nesting uu____4125
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4128;
               FStar_Parser_AST.blevel = uu____4129;
               FStar_Parser_AST.aqual = uu____4130;_},phi))
             ->
             let uu____4132 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4132
         | uu____4133 ->
             let uu____4138 =
               let uu____4139 = p_tuplePattern pat in
               let uu____4140 =
                 let uu____4141 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4142 =
                   let uu____4143 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4143 in
                 FStar_Pprint.op_Hat_Hat uu____4141 uu____4142 in
               FStar_Pprint.op_Hat_Hat uu____4139 uu____4140 in
             soft_parens_with_nesting uu____4138)
    | FStar_Parser_AST.PatList pats ->
        let uu____4147 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4147 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4162 =
          match uu____4162 with
          | (lid,pat) ->
              let uu____4169 = p_qlident lid in
              let uu____4170 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4169 uu____4170 in
        let uu____4171 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4171
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4181 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4182 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4183 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4181 uu____4182 uu____4183
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4194 =
          let uu____4195 =
            let uu____4196 = str (FStar_Ident.text_of_id op) in
            let uu____4197 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4196 uu____4197 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4195 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4194
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4205 = FStar_Pprint.optional p_aqual aqual in
        let uu____4206 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4205 uu____4206
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4208 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4211;
           FStar_Parser_AST.prange = uu____4212;_},uu____4213)
        ->
        let uu____4218 = p_tuplePattern p in
        soft_parens_with_nesting uu____4218
    | FStar_Parser_AST.PatTuple (uu____4219,false ) ->
        let uu____4224 = p_tuplePattern p in
        soft_parens_with_nesting uu____4224
    | uu____4225 ->
        let uu____4226 =
          let uu____4227 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4227 in
        failwith uu____4226
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4231 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4232 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4231 uu____4232
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4237 =
              let uu____4238 = unparen t in uu____4238.FStar_Parser_AST.tm in
            match uu____4237 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4241;
                   FStar_Parser_AST.blevel = uu____4242;
                   FStar_Parser_AST.aqual = uu____4243;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4245 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4245 t1 phi
            | uu____4246 ->
                let uu____4247 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4248 =
                  let uu____4249 = p_lident lid in
                  let uu____4250 =
                    let uu____4251 =
                      let uu____4252 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4253 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4252 uu____4253 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4251 in
                  FStar_Pprint.op_Hat_Hat uu____4249 uu____4250 in
                FStar_Pprint.op_Hat_Hat uu____4247 uu____4248 in
          if is_atomic
          then
            let uu____4254 =
              let uu____4255 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4255 in
            FStar_Pprint.group uu____4254
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4257 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4263 =
            let uu____4264 = unparen t in uu____4264.FStar_Parser_AST.tm in
          (match uu____4263 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4266;
                  FStar_Parser_AST.blevel = uu____4267;
                  FStar_Parser_AST.aqual = uu____4268;_},phi)
               ->
               if is_atomic
               then
                 let uu____4270 =
                   let uu____4271 =
                     let uu____4272 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4272 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4271 in
                 FStar_Pprint.group uu____4270
               else
                 (let uu____4274 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4274)
           | uu____4275 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4283 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4284 =
            let uu____4285 =
              let uu____4286 =
                let uu____4287 = p_appTerm t in
                let uu____4288 =
                  let uu____4289 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4289 in
                FStar_Pprint.op_Hat_Hat uu____4287 uu____4288 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4286 in
            FStar_Pprint.op_Hat_Hat binder uu____4285 in
          FStar_Pprint.op_Hat_Hat uu____4283 uu____4284
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
    let uu____4303 =
      let uu____4304 = unparen e in uu____4304.FStar_Parser_AST.tm in
    match uu____4303 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4307 =
          let uu____4308 =
            let uu____4309 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4309 FStar_Pprint.semi in
          FStar_Pprint.group uu____4308 in
        let uu____4310 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4307 uu____4310
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4314 =
          let uu____4315 =
            let uu____4316 =
              let uu____4317 = p_lident x in
              let uu____4318 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4317 uu____4318 in
            let uu____4319 =
              let uu____4320 = p_noSeqTerm e1 in
              let uu____4321 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4320 uu____4321 in
            op_Hat_Slash_Plus_Hat uu____4316 uu____4319 in
          FStar_Pprint.group uu____4315 in
        let uu____4322 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4314 uu____4322
    | uu____4323 ->
        let uu____4324 = p_noSeqTerm e in FStar_Pprint.group uu____4324
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4327 =
      let uu____4328 = unparen e in uu____4328.FStar_Parser_AST.tm in
    match uu____4327 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4333 =
          let uu____4334 = p_tmIff e1 in
          let uu____4335 =
            let uu____4336 =
              let uu____4337 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4337 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4336 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4334 uu____4335 in
        FStar_Pprint.group uu____4333
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4343 =
          let uu____4344 = p_tmIff e1 in
          let uu____4345 =
            let uu____4346 =
              let uu____4347 =
                let uu____4348 = p_typ t in
                let uu____4349 =
                  let uu____4350 = str "by" in
                  let uu____4351 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4350 uu____4351 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4348 uu____4349 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4347 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4346 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4344 uu____4345 in
        FStar_Pprint.group uu____4343
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4352;_},e1::e2::e3::[])
        ->
        let uu____4358 =
          let uu____4359 =
            let uu____4360 =
              let uu____4361 = p_atomicTermNotQUident e1 in
              let uu____4362 =
                let uu____4363 =
                  let uu____4364 =
                    let uu____4365 = p_term e2 in
                    soft_parens_with_nesting uu____4365 in
                  let uu____4366 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4364 uu____4366 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4363 in
              FStar_Pprint.op_Hat_Hat uu____4361 uu____4362 in
            FStar_Pprint.group uu____4360 in
          let uu____4367 =
            let uu____4368 = p_noSeqTerm e3 in jump2 uu____4368 in
          FStar_Pprint.op_Hat_Hat uu____4359 uu____4367 in
        FStar_Pprint.group uu____4358
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4369;_},e1::e2::e3::[])
        ->
        let uu____4375 =
          let uu____4376 =
            let uu____4377 =
              let uu____4378 = p_atomicTermNotQUident e1 in
              let uu____4379 =
                let uu____4380 =
                  let uu____4381 =
                    let uu____4382 = p_term e2 in
                    soft_brackets_with_nesting uu____4382 in
                  let uu____4383 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4381 uu____4383 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4380 in
              FStar_Pprint.op_Hat_Hat uu____4378 uu____4379 in
            FStar_Pprint.group uu____4377 in
          let uu____4384 =
            let uu____4385 = p_noSeqTerm e3 in jump2 uu____4385 in
          FStar_Pprint.op_Hat_Hat uu____4376 uu____4384 in
        FStar_Pprint.group uu____4375
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4395 =
          let uu____4396 = str "requires" in
          let uu____4397 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4396 uu____4397 in
        FStar_Pprint.group uu____4395
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4407 =
          let uu____4408 = str "ensures" in
          let uu____4409 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4408 uu____4409 in
        FStar_Pprint.group uu____4407
    | FStar_Parser_AST.Attributes es ->
        let uu____4413 =
          let uu____4414 = str "attributes" in
          let uu____4415 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4414 uu____4415 in
        FStar_Pprint.group uu____4413
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4419 = is_unit e3 in
        if uu____4419
        then
          let uu____4420 =
            let uu____4421 =
              let uu____4422 = str "if" in
              let uu____4423 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4422 uu____4423 in
            let uu____4424 =
              let uu____4425 = str "then" in
              let uu____4426 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4425 uu____4426 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4421 uu____4424 in
          FStar_Pprint.group uu____4420
        else
          (let e2_doc =
             let uu____4429 =
               let uu____4430 = unparen e2 in uu____4430.FStar_Parser_AST.tm in
             match uu____4429 with
             | FStar_Parser_AST.If (uu____4431,uu____4432,e31) when
                 is_unit e31 ->
                 let uu____4434 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4434
             | uu____4435 -> p_noSeqTerm e2 in
           let uu____4436 =
             let uu____4437 =
               let uu____4438 = str "if" in
               let uu____4439 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4438 uu____4439 in
             let uu____4440 =
               let uu____4441 =
                 let uu____4442 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4442 e2_doc in
               let uu____4443 =
                 let uu____4444 = str "else" in
                 let uu____4445 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4444 uu____4445 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4441 uu____4443 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4437 uu____4440 in
           FStar_Pprint.group uu____4436)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4468 =
          let uu____4469 =
            let uu____4470 = str "try" in
            let uu____4471 = p_noSeqTerm e1 in prefix2 uu____4470 uu____4471 in
          let uu____4472 =
            let uu____4473 = str "with" in
            let uu____4474 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4473 uu____4474 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4469 uu____4472 in
        FStar_Pprint.group uu____4468
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4505 =
          let uu____4506 =
            let uu____4507 = str "match" in
            let uu____4508 = p_noSeqTerm e1 in
            let uu____4509 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4507 uu____4508 uu____4509 in
          let uu____4510 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4506 uu____4510 in
        FStar_Pprint.group uu____4505
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4521 =
          let uu____4522 =
            let uu____4523 = str "let open" in
            let uu____4524 = p_quident uid in
            let uu____4525 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4523 uu____4524 uu____4525 in
          let uu____4526 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4522 uu____4526 in
        FStar_Pprint.group uu____4521
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4543 = str "let" in
          let uu____4544 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4543 uu____4544 in
        let uu____4545 =
          let uu____4546 =
            let uu____4547 =
              let uu____4548 = str "and" in
              precede_break_separate_map let_doc uu____4548 p_letbinding lbs in
            let uu____4553 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4547 uu____4553 in
          FStar_Pprint.group uu____4546 in
        let uu____4554 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4545 uu____4554
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4557;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4560;
                                                         FStar_Parser_AST.level
                                                           = uu____4561;_})
        when matches_var maybe_x x ->
        let uu____4588 =
          let uu____4589 = str "function" in
          let uu____4590 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4589 uu____4590 in
        FStar_Pprint.group uu____4588
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4601 =
          let uu____4602 = p_lident id1 in
          let uu____4603 =
            let uu____4604 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4604 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4602 uu____4603 in
        FStar_Pprint.group uu____4601
    | uu____4605 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4608 =
      let uu____4609 = unparen e in uu____4609.FStar_Parser_AST.tm in
    match uu____4608 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4625 =
          let uu____4626 =
            let uu____4627 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4627 FStar_Pprint.space in
          let uu____4628 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4626 uu____4628 FStar_Pprint.dot in
        let uu____4629 =
          let uu____4630 = p_trigger trigger in
          let uu____4631 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4630 uu____4631 in
        prefix2 uu____4625 uu____4629
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4647 =
          let uu____4648 =
            let uu____4649 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4649 FStar_Pprint.space in
          let uu____4650 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4648 uu____4650 FStar_Pprint.dot in
        let uu____4651 =
          let uu____4652 = p_trigger trigger in
          let uu____4653 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4652 uu____4653 in
        prefix2 uu____4647 uu____4651
    | uu____4654 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4656 =
      let uu____4657 = unparen e in uu____4657.FStar_Parser_AST.tm in
    match uu____4656 with
    | FStar_Parser_AST.QForall uu____4658 -> str "forall"
    | FStar_Parser_AST.QExists uu____4671 -> str "exists"
    | uu____4684 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___100_4685  ->
    match uu___100_4685 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4697 =
          let uu____4698 =
            let uu____4699 = str "pattern" in
            let uu____4700 =
              let uu____4701 =
                let uu____4702 = p_disjunctivePats pats in jump2 uu____4702 in
              let uu____4703 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4701 uu____4703 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4699 uu____4700 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4698 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4697
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4709 = str "\\/" in
    FStar_Pprint.separate_map uu____4709 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4715 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4715
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4717 =
      let uu____4718 = unparen e in uu____4718.FStar_Parser_AST.tm in
    match uu____4717 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4725 =
          let uu____4726 = str "fun" in
          let uu____4727 =
            let uu____4728 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4728 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4726 uu____4727 in
        let uu____4729 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4725 uu____4729
    | uu____4730 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4733  ->
    match uu____4733 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4752 =
            let uu____4753 = unparen e in uu____4753.FStar_Parser_AST.tm in
          match uu____4752 with
          | FStar_Parser_AST.Match uu____4756 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4771 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4787);
                 FStar_Parser_AST.prange = uu____4788;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4790);
                                                               FStar_Parser_AST.range
                                                                 = uu____4791;
                                                               FStar_Parser_AST.level
                                                                 = uu____4792;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4819 -> (fun x  -> x) in
        let uu____4821 =
          let uu____4822 =
            let uu____4823 =
              let uu____4824 =
                let uu____4825 =
                  let uu____4826 = p_disjunctivePattern pat in
                  let uu____4827 =
                    let uu____4828 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4828 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4826 uu____4827 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4825 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4824 in
            FStar_Pprint.group uu____4823 in
          let uu____4829 =
            let uu____4830 = p_term e in maybe_paren uu____4830 in
          op_Hat_Slash_Plus_Hat uu____4822 uu____4829 in
        FStar_Pprint.group uu____4821
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___101_4831  ->
    match uu___101_4831 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4835 = str "when" in
        let uu____4836 =
          let uu____4837 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4837 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4835 uu____4836
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4839 =
      let uu____4840 = unparen e in uu____4840.FStar_Parser_AST.tm in
    match uu____4839 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4841;_},e1::e2::[])
        ->
        let uu____4846 = str "<==>" in
        let uu____4847 = p_tmImplies e1 in
        let uu____4848 = p_tmIff e2 in
        infix0 uu____4846 uu____4847 uu____4848
    | uu____4849 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4851 =
      let uu____4852 = unparen e in uu____4852.FStar_Parser_AST.tm in
    match uu____4851 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4853;_},e1::e2::[])
        ->
        let uu____4858 = str "==>" in
        let uu____4859 = p_tmArrow p_tmFormula e1 in
        let uu____4860 = p_tmImplies e2 in
        infix0 uu____4858 uu____4859 uu____4860
    | uu____4861 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4866 =
        let uu____4867 = unparen e in uu____4867.FStar_Parser_AST.tm in
      match uu____4866 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4874 =
            let uu____4875 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4880 = p_binder false b in
                   let uu____4881 =
                     let uu____4882 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4882 in
                   FStar_Pprint.op_Hat_Hat uu____4880 uu____4881) bs in
            let uu____4883 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4875 uu____4883 in
          FStar_Pprint.group uu____4874
      | uu____4884 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4886 =
      let uu____4887 = unparen e in uu____4887.FStar_Parser_AST.tm in
    match uu____4886 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4888;_},e1::e2::[])
        ->
        let uu____4893 = str "\\/" in
        let uu____4894 = p_tmFormula e1 in
        let uu____4895 = p_tmConjunction e2 in
        infix0 uu____4893 uu____4894 uu____4895
    | uu____4896 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4898 =
      let uu____4899 = unparen e in uu____4899.FStar_Parser_AST.tm in
    match uu____4898 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4900;_},e1::e2::[])
        ->
        let uu____4905 = str "/\\" in
        let uu____4906 = p_tmConjunction e1 in
        let uu____4907 = p_tmTuple e2 in
        infix0 uu____4905 uu____4906 uu____4907
    | uu____4908 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4911 =
      let uu____4912 = unparen e in uu____4912.FStar_Parser_AST.tm in
    match uu____4911 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4927 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____4927
          (fun uu____4935  ->
             match uu____4935 with | (e1,uu____4941) -> p_tmEq e1) args
    | uu____4942 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4947 =
             let uu____4948 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4948 in
           FStar_Pprint.group uu____4947)
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
      let uu____4993 =
        let uu____4994 = unparen e in uu____4994.FStar_Parser_AST.tm in
      match uu____4993 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5001 = levels op1 in
          (match uu____5001 with
           | (left1,mine,right1) ->
               let uu____5011 =
                 let uu____5012 = FStar_All.pipe_left str op1 in
                 let uu____5013 = p_tmEq' left1 e1 in
                 let uu____5014 = p_tmEq' right1 e2 in
                 infix0 uu____5012 uu____5013 uu____5014 in
               paren_if curr mine uu____5011)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5015;_},e1::e2::[])
          ->
          let uu____5020 =
            let uu____5021 = p_tmEq e1 in
            let uu____5022 =
              let uu____5023 =
                let uu____5024 =
                  let uu____5025 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5025 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5024 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5023 in
            FStar_Pprint.op_Hat_Hat uu____5021 uu____5022 in
          FStar_Pprint.group uu____5020
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5026;_},e1::[])
          ->
          let uu____5030 = levels "-" in
          (match uu____5030 with
           | (left1,mine,right1) ->
               let uu____5040 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5040)
      | uu____5041 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5096 =
        let uu____5097 = unparen e in uu____5097.FStar_Parser_AST.tm in
      match uu____5096 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5100)::(e2,uu____5102)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5122 = is_list e in Prims.op_Negation uu____5122)
          ->
          let op = "::" in
          let uu____5124 = levels op in
          (match uu____5124 with
           | (left1,mine,right1) ->
               let uu____5134 =
                 let uu____5135 = str op in
                 let uu____5136 = p_tmNoEq' left1 e1 in
                 let uu____5137 = p_tmNoEq' right1 e2 in
                 infix0 uu____5135 uu____5136 uu____5137 in
               paren_if curr mine uu____5134)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5145 = levels op in
          (match uu____5145 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5159 = p_binder false b in
                 let uu____5160 =
                   let uu____5161 =
                     let uu____5162 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5162 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5161 in
                 FStar_Pprint.op_Hat_Hat uu____5159 uu____5160 in
               let uu____5163 =
                 let uu____5164 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5165 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5164 uu____5165 in
               paren_if curr mine uu____5163)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5172 = levels op1 in
          (match uu____5172 with
           | (left1,mine,right1) ->
               let uu____5182 =
                 let uu____5183 = str op1 in
                 let uu____5184 = p_tmNoEq' left1 e1 in
                 let uu____5185 = p_tmNoEq' right1 e2 in
                 infix0 uu____5183 uu____5184 uu____5185 in
               paren_if curr mine uu____5182)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5188 =
            let uu____5189 = p_lidentOrUnderscore lid in
            let uu____5190 =
              let uu____5191 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5191 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5189 uu____5190 in
          FStar_Pprint.group uu____5188
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5212 =
            let uu____5213 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5214 =
              let uu____5215 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5215 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5213 uu____5214 in
          braces_with_nesting uu____5212
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5220;_},e1::[])
          ->
          let uu____5224 =
            let uu____5225 = str "~" in
            let uu____5226 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5225 uu____5226 in
          FStar_Pprint.group uu____5224
      | uu____5227 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5229 = p_appTerm e in
    let uu____5230 =
      let uu____5231 =
        let uu____5232 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5232 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5231 in
    FStar_Pprint.op_Hat_Hat uu____5229 uu____5230
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5237 =
            let uu____5238 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5238 t phi in
          soft_parens_with_nesting uu____5237
      | FStar_Parser_AST.TAnnotated uu____5239 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5244 ->
          let uu____5245 =
            let uu____5246 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5246 in
          failwith uu____5245
      | FStar_Parser_AST.TVariable uu____5247 ->
          let uu____5248 =
            let uu____5249 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5249 in
          failwith uu____5248
      | FStar_Parser_AST.NoName uu____5250 ->
          let uu____5251 =
            let uu____5252 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5252 in
          failwith uu____5251
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5253  ->
    match uu____5253 with
    | (lid,e) ->
        let uu____5260 =
          let uu____5261 = p_qlident lid in
          let uu____5262 =
            let uu____5263 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5263 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5261 uu____5262 in
        FStar_Pprint.group uu____5260
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5265 =
      let uu____5266 = unparen e in uu____5266.FStar_Parser_AST.tm in
    match uu____5265 with
    | FStar_Parser_AST.App uu____5267 when is_general_application e ->
        let uu____5274 = head_and_args e in
        (match uu____5274 with
         | (head1,args) ->
             let uu____5299 =
               let uu____5310 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5310
               then
                 let uu____5331 =
                   FStar_Util.take
                     (fun uu____5355  ->
                        match uu____5355 with
                        | (uu____5360,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5331 with
                 | (fs_typ_args,args1) ->
                     let uu____5398 =
                       let uu____5399 = p_indexingTerm head1 in
                       let uu____5400 =
                         let uu____5401 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5401 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5399 uu____5400 in
                     (uu____5398, args1)
               else
                 (let uu____5413 = p_indexingTerm head1 in (uu____5413, args)) in
             (match uu____5299 with
              | (head_doc,args1) ->
                  let uu____5434 =
                    let uu____5435 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5435 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5434))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5455 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5455)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5473 =
               let uu____5474 = p_quident lid in
               let uu____5475 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5474 uu____5475 in
             FStar_Pprint.group uu____5473
         | hd1::tl1 ->
             let uu____5492 =
               let uu____5493 =
                 let uu____5494 =
                   let uu____5495 = p_quident lid in
                   let uu____5496 = p_argTerm hd1 in
                   prefix2 uu____5495 uu____5496 in
                 FStar_Pprint.group uu____5494 in
               let uu____5497 =
                 let uu____5498 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5498 in
               FStar_Pprint.op_Hat_Hat uu____5493 uu____5497 in
             FStar_Pprint.group uu____5492)
    | uu____5503 -> p_indexingTerm e
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
         (let uu____5512 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5512 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5514 = str "#" in
        let uu____5515 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5514 uu____5515
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5517  ->
    match uu____5517 with | (e,uu____5523) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5528 =
        let uu____5529 = unparen e in uu____5529.FStar_Parser_AST.tm in
      match uu____5528 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5530;_},e1::e2::[])
          ->
          let uu____5535 =
            let uu____5536 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5537 =
              let uu____5538 =
                let uu____5539 = p_term e2 in
                soft_parens_with_nesting uu____5539 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5538 in
            FStar_Pprint.op_Hat_Hat uu____5536 uu____5537 in
          FStar_Pprint.group uu____5535
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5540;_},e1::e2::[])
          ->
          let uu____5545 =
            let uu____5546 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5547 =
              let uu____5548 =
                let uu____5549 = p_term e2 in
                soft_brackets_with_nesting uu____5549 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5548 in
            FStar_Pprint.op_Hat_Hat uu____5546 uu____5547 in
          FStar_Pprint.group uu____5545
      | uu____5550 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5553 =
      let uu____5554 = unparen e in uu____5554.FStar_Parser_AST.tm in
    match uu____5553 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5557 = p_quident lid in
        let uu____5558 =
          let uu____5559 =
            let uu____5560 = p_term e1 in soft_parens_with_nesting uu____5560 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5559 in
        FStar_Pprint.op_Hat_Hat uu____5557 uu____5558
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5566 = str (FStar_Ident.text_of_id op) in
        let uu____5567 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5566 uu____5567
    | uu____5568 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5570 =
      let uu____5571 = unparen e in uu____5571.FStar_Parser_AST.tm in
    match uu____5570 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5584 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5591 = str (FStar_Ident.text_of_id op) in
        let uu____5592 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5591 uu____5592
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5596 =
          let uu____5597 =
            let uu____5598 = str (FStar_Ident.text_of_id op) in
            let uu____5599 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5598 uu____5599 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5597 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5596
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5614 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5615 =
          let uu____5616 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5617 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5616 p_tmEq uu____5617 in
        let uu____5624 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5614 uu____5615 uu____5624
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5627 =
          let uu____5628 = p_atomicTermNotQUident e1 in
          let uu____5629 =
            let uu____5630 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5630 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5628 uu____5629 in
        FStar_Pprint.group uu____5627
    | uu____5631 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5633 =
      let uu____5634 = unparen e in uu____5634.FStar_Parser_AST.tm in
    match uu____5633 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5638 = p_quident constr_lid in
        let uu____5639 =
          let uu____5640 =
            let uu____5641 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5641 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5640 in
        FStar_Pprint.op_Hat_Hat uu____5638 uu____5639
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5643 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5643 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5645 = p_term e1 in soft_parens_with_nesting uu____5645
    | uu____5646 when is_array e ->
        let es = extract_from_list e in
        let uu____5650 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5651 =
          let uu____5652 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5652 p_noSeqTerm es in
        let uu____5653 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5650 uu____5651 uu____5653
    | uu____5654 when is_list e ->
        let uu____5655 =
          let uu____5656 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5657 = extract_from_list e in
          separate_map_or_flow uu____5656 p_noSeqTerm uu____5657 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5655 FStar_Pprint.rbracket
    | uu____5660 when is_lex_list e ->
        let uu____5661 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5662 =
          let uu____5663 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5664 = extract_from_list e in
          separate_map_or_flow uu____5663 p_noSeqTerm uu____5664 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5661 uu____5662 FStar_Pprint.rbracket
    | uu____5667 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5671 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5672 =
          let uu____5673 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5673 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5671 uu____5672 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5677 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5678 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5677 uu____5678
    | FStar_Parser_AST.Op (op,args) when
        let uu____5685 = handleable_op op args in
        Prims.op_Negation uu____5685 ->
        let uu____5686 =
          let uu____5687 =
            let uu____5688 =
              let uu____5689 =
                let uu____5690 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5690
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5689 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5688 in
          Prims.strcat "Operation " uu____5687 in
        failwith uu____5686
    | FStar_Parser_AST.Uvar uu____5691 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5692 = p_term e in soft_parens_with_nesting uu____5692
    | FStar_Parser_AST.Const uu____5693 ->
        let uu____5694 = p_term e in soft_parens_with_nesting uu____5694
    | FStar_Parser_AST.Op uu____5695 ->
        let uu____5702 = p_term e in soft_parens_with_nesting uu____5702
    | FStar_Parser_AST.Tvar uu____5703 ->
        let uu____5704 = p_term e in soft_parens_with_nesting uu____5704
    | FStar_Parser_AST.Var uu____5705 ->
        let uu____5706 = p_term e in soft_parens_with_nesting uu____5706
    | FStar_Parser_AST.Name uu____5707 ->
        let uu____5708 = p_term e in soft_parens_with_nesting uu____5708
    | FStar_Parser_AST.Construct uu____5709 ->
        let uu____5720 = p_term e in soft_parens_with_nesting uu____5720
    | FStar_Parser_AST.Abs uu____5721 ->
        let uu____5728 = p_term e in soft_parens_with_nesting uu____5728
    | FStar_Parser_AST.App uu____5729 ->
        let uu____5736 = p_term e in soft_parens_with_nesting uu____5736
    | FStar_Parser_AST.Let uu____5737 ->
        let uu____5750 = p_term e in soft_parens_with_nesting uu____5750
    | FStar_Parser_AST.LetOpen uu____5751 ->
        let uu____5756 = p_term e in soft_parens_with_nesting uu____5756
    | FStar_Parser_AST.Seq uu____5757 ->
        let uu____5762 = p_term e in soft_parens_with_nesting uu____5762
    | FStar_Parser_AST.Bind uu____5763 ->
        let uu____5770 = p_term e in soft_parens_with_nesting uu____5770
    | FStar_Parser_AST.If uu____5771 ->
        let uu____5778 = p_term e in soft_parens_with_nesting uu____5778
    | FStar_Parser_AST.Match uu____5779 ->
        let uu____5794 = p_term e in soft_parens_with_nesting uu____5794
    | FStar_Parser_AST.TryWith uu____5795 ->
        let uu____5810 = p_term e in soft_parens_with_nesting uu____5810
    | FStar_Parser_AST.Ascribed uu____5811 ->
        let uu____5820 = p_term e in soft_parens_with_nesting uu____5820
    | FStar_Parser_AST.Record uu____5821 ->
        let uu____5834 = p_term e in soft_parens_with_nesting uu____5834
    | FStar_Parser_AST.Project uu____5835 ->
        let uu____5840 = p_term e in soft_parens_with_nesting uu____5840
    | FStar_Parser_AST.Product uu____5841 ->
        let uu____5848 = p_term e in soft_parens_with_nesting uu____5848
    | FStar_Parser_AST.Sum uu____5849 ->
        let uu____5856 = p_term e in soft_parens_with_nesting uu____5856
    | FStar_Parser_AST.QForall uu____5857 ->
        let uu____5870 = p_term e in soft_parens_with_nesting uu____5870
    | FStar_Parser_AST.QExists uu____5871 ->
        let uu____5884 = p_term e in soft_parens_with_nesting uu____5884
    | FStar_Parser_AST.Refine uu____5885 ->
        let uu____5890 = p_term e in soft_parens_with_nesting uu____5890
    | FStar_Parser_AST.NamedTyp uu____5891 ->
        let uu____5896 = p_term e in soft_parens_with_nesting uu____5896
    | FStar_Parser_AST.Requires uu____5897 ->
        let uu____5904 = p_term e in soft_parens_with_nesting uu____5904
    | FStar_Parser_AST.Ensures uu____5905 ->
        let uu____5912 = p_term e in soft_parens_with_nesting uu____5912
    | FStar_Parser_AST.Assign uu____5913 ->
        let uu____5918 = p_term e in soft_parens_with_nesting uu____5918
    | FStar_Parser_AST.Attributes uu____5919 ->
        let uu____5922 = p_term e in soft_parens_with_nesting uu____5922
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___104_5923  ->
    match uu___104_5923 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5927 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____5927
    | FStar_Const.Const_string (s,uu____5941) ->
        let uu____5942 = str s in FStar_Pprint.dquotes uu____5942
    | FStar_Const.Const_bytearray (bytes,uu____5944) ->
        let uu____5949 =
          let uu____5950 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____5950 in
        let uu____5951 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____5949 uu____5951
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___102_5969 =
          match uu___102_5969 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___103_5973 =
          match uu___103_5973 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5984  ->
               match uu____5984 with
               | (s,w) ->
                   let uu____5991 = signedness s in
                   let uu____5992 = width w in
                   FStar_Pprint.op_Hat_Hat uu____5991 uu____5992)
            sign_width_opt in
        let uu____5993 = str repr in
        FStar_Pprint.op_Hat_Hat uu____5993 ending
    | FStar_Const.Const_range r ->
        let uu____5995 = FStar_Range.string_of_range r in str uu____5995
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5997 = p_quident lid in
        let uu____5998 =
          let uu____5999 =
            let uu____6000 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6000 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5999 in
        FStar_Pprint.op_Hat_Hat uu____5997 uu____5998
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6002 = str "u#" in
    let uu____6003 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6002 uu____6003
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6005 =
      let uu____6006 = unparen u in uu____6006.FStar_Parser_AST.tm in
    match uu____6005 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6007;_},u1::u2::[])
        ->
        let uu____6012 =
          let uu____6013 = p_universeFrom u1 in
          let uu____6014 =
            let uu____6015 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6015 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6013 uu____6014 in
        FStar_Pprint.group uu____6012
    | FStar_Parser_AST.App uu____6016 ->
        let uu____6023 = head_and_args u in
        (match uu____6023 with
         | (head1,args) ->
             let uu____6048 =
               let uu____6049 = unparen head1 in
               uu____6049.FStar_Parser_AST.tm in
             (match uu____6048 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6051 =
                    let uu____6052 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6053 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6061  ->
                           match uu____6061 with
                           | (u1,uu____6067) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6052 uu____6053 in
                  FStar_Pprint.group uu____6051
              | uu____6068 ->
                  let uu____6069 =
                    let uu____6070 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6070 in
                  failwith uu____6069))
    | uu____6071 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6073 =
      let uu____6074 = unparen u in uu____6074.FStar_Parser_AST.tm in
    match uu____6073 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6097 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6097
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6098;_},uu____6099::uu____6100::[])
        ->
        let uu____6103 = p_universeFrom u in
        soft_parens_with_nesting uu____6103
    | FStar_Parser_AST.App uu____6104 ->
        let uu____6111 = p_universeFrom u in
        soft_parens_with_nesting uu____6111
    | uu____6112 ->
        let uu____6113 =
          let uu____6114 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6114 in
        failwith uu____6113
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
       | FStar_Parser_AST.Module (uu____6151,decls) ->
           let uu____6157 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6157
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6166,decls,uu____6168) ->
           let uu____6173 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6173
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6216  ->
         match uu____6216 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6258,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6264,decls,uu____6266) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6302 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6315;
                 FStar_Parser_AST.doc = uu____6316;
                 FStar_Parser_AST.quals = uu____6317;
                 FStar_Parser_AST.attrs = uu____6318;_}::uu____6319 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6325 =
                   let uu____6328 =
                     let uu____6331 = FStar_List.tl ds in d :: uu____6331 in
                   d0 :: uu____6328 in
                 (uu____6325, (d0.FStar_Parser_AST.drange))
             | uu____6336 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6302 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6397 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6397 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6490 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6490, comments1))))))