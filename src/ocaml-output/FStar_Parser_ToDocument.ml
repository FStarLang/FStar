open Prims
let should_print_fs_typ_app: Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false
let with_fs_typ_app:
  'Auu____15 'Auu____16 .
    Prims.bool -> ('Auu____16 -> 'Auu____15) -> 'Auu____16 -> 'Auu____15
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
    let uu____188 =
      let uu____189 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____189 in
    if uu____188
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____238 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____247 'Auu____248 .
    'Auu____248 ->
      ('Auu____247 -> 'Auu____248) ->
        'Auu____247 FStar_Pervasives_Native.option -> 'Auu____248
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
  'Auu____302 .
    FStar_Pprint.document ->
      ('Auu____302 -> FStar_Pprint.document) ->
        'Auu____302 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____324 =
          let uu____325 =
            let uu____326 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____326 in
          FStar_Pprint.separate_map uu____325 f l in
        FStar_Pprint.group uu____324
let precede_break_separate_map:
  'Auu____332 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____332 -> FStar_Pprint.document) ->
          'Auu____332 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____358 =
            let uu____359 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____360 =
              let uu____361 = FStar_List.hd l in
              FStar_All.pipe_right uu____361 f in
            FStar_Pprint.precede uu____359 uu____360 in
          let uu____362 =
            let uu____363 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____369 =
                   let uu____370 =
                     let uu____371 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____371 in
                   FStar_Pprint.op_Hat_Hat sep uu____370 in
                 FStar_Pprint.op_Hat_Hat break1 uu____369) uu____363 in
          FStar_Pprint.op_Hat_Hat uu____358 uu____362
let concat_break_map:
  'Auu____375 .
    ('Auu____375 -> FStar_Pprint.document) ->
      'Auu____375 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____393 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____397 = f x in FStar_Pprint.op_Hat_Hat uu____397 break1)
          l in
      FStar_Pprint.group uu____393
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
    let uu____419 = str "begin" in
    let uu____420 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____419 contents uu____420
let separate_map_or_flow:
  'Auu____425 .
    FStar_Pprint.document ->
      ('Auu____425 -> FStar_Pprint.document) ->
        'Auu____425 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
  'Auu____457 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____457 -> FStar_Pprint.document) ->
                  'Auu____457 Prims.list -> FStar_Pprint.document
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
                    (let uu____502 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____502
                       closing)
let soft_surround_map_or_flow:
  'Auu____512 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____512 -> FStar_Pprint.document) ->
                  'Auu____512 Prims.list -> FStar_Pprint.document
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
                    (let uu____557 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____557
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____570  ->
    match uu____570 with
    | (comment,keywords) ->
        let uu____595 =
          let uu____596 =
            let uu____599 = str comment in
            let uu____600 =
              let uu____603 =
                let uu____606 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____615  ->
                       match uu____615 with
                       | (k,v1) ->
                           let uu____622 =
                             let uu____625 = str k in
                             let uu____626 =
                               let uu____629 =
                                 let uu____632 = str v1 in [uu____632] in
                               FStar_Pprint.rarrow :: uu____629 in
                             uu____625 :: uu____626 in
                           FStar_Pprint.concat uu____622) keywords in
                [uu____606] in
              FStar_Pprint.space :: uu____603 in
            uu____599 :: uu____600 in
          FStar_Pprint.concat uu____596 in
        FStar_Pprint.group uu____595
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____636 =
      let uu____637 = unparen e in uu____637.FStar_Parser_AST.tm in
    match uu____636 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____638 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____645 =
        let uu____646 = unparen t in uu____646.FStar_Parser_AST.tm in
      match uu____645 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____648 -> false
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
        let uu____665 =
          let uu____666 = unparen e in uu____666.FStar_Parser_AST.tm in
        match uu____665 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____679::(e2,uu____681)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____704 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____714 =
      let uu____715 = unparen e in uu____715.FStar_Parser_AST.tm in
    match uu____714 with
    | FStar_Parser_AST.Construct (uu____718,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____729,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____750 = extract_from_list e2 in e1 :: uu____750
    | uu____753 ->
        let uu____754 =
          let uu____755 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____755 in
        failwith uu____754
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____761 =
      let uu____762 = unparen e in uu____762.FStar_Parser_AST.tm in
    match uu____761 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____764;
           FStar_Parser_AST.level = uu____765;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____767 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____771 =
      let uu____772 = unparen e in uu____772.FStar_Parser_AST.tm in
    match uu____771 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____775;
           FStar_Parser_AST.level = uu____776;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____778;
                                                        FStar_Parser_AST.level
                                                          = uu____779;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____781;
                                                   FStar_Parser_AST.level =
                                                     uu____782;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____784;
                FStar_Parser_AST.level = uu____785;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____787;
           FStar_Parser_AST.level = uu____788;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____790 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____796 =
      let uu____797 = unparen e in uu____797.FStar_Parser_AST.tm in
    match uu____796 with
    | FStar_Parser_AST.Var uu____800 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____801;
           FStar_Parser_AST.range = uu____802;
           FStar_Parser_AST.level = uu____803;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____804;
                                                        FStar_Parser_AST.range
                                                          = uu____805;
                                                        FStar_Parser_AST.level
                                                          = uu____806;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____808;
                                                   FStar_Parser_AST.level =
                                                     uu____809;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____810;
                FStar_Parser_AST.range = uu____811;
                FStar_Parser_AST.level = uu____812;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____814;
           FStar_Parser_AST.level = uu____815;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____817 = extract_from_ref_set e1 in
        let uu____820 = extract_from_ref_set e2 in
        FStar_List.append uu____817 uu____820
    | uu____823 ->
        let uu____824 =
          let uu____825 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____825 in
        failwith uu____824
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____831 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____831
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____835 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____835
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
      let uu____882 =
        let uu____883 = unparen e1 in uu____883.FStar_Parser_AST.tm in
      match uu____882 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____901 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____915 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____919 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____923 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___123_940  ->
    match uu___123_940 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___124_956  ->
      match uu___124_956 with
      | FStar_Util.Inl c ->
          let uu____962 = FStar_String.get s (Prims.parse_int "0") in
          uu____962 = c
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
  'Auu____1032 .
    Prims.unit ->
      (associativity,('Auu____1032,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1043  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1059 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1059) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1070  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1094 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1094) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1105  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1125 .
    Prims.unit ->
      (associativity,('Auu____1125,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1136  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1152 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1152) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1163  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1183 .
    Prims.unit ->
      (associativity,('Auu____1183,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1194  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1210 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1210) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1221  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1237 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1237) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1248  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1272 .
    Prims.unit ->
      (associativity,('Auu____1272,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1283  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1299 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1299) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1310  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1326 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1326) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1337  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1353 .
    Prims.unit ->
      (associativity,('Auu____1353,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1364  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1380 .
    Prims.unit ->
      (associativity,('Auu____1380,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1391  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1407 .
    Prims.unit ->
      (associativity,('Auu____1407,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1418  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___125_1605 =
    match uu___125_1605 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1643  ->
         match uu____1643 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1718 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1718 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1766) ->
          assoc_levels
      | uu____1807 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1841 .
    ('Auu____1841,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1897 =
        FStar_List.tryFind
          (fun uu____1935  ->
             match uu____1935 with
             | (uu____1952,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1897 with
      | FStar_Pervasives_Native.Some ((uu____1990,l1,uu____1992),uu____1993)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2044 =
            let uu____2045 =
              let uu____2046 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2046 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2045 in
          failwith uu____2044 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2078 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2078) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2091  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2165 =
      let uu____2178 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2178 (operatorInfix0ad12 ()) in
    uu____2165 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2281 =
      let uu____2294 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2294 opinfix34 in
    uu____2281 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2355 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2355
    then Prims.parse_int "1"
    else
      (let uu____2357 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2357
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2363 . FStar_Ident.ident -> 'Auu____2363 Prims.list -> Prims.bool =
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
      | uu____2376 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2406 .
    ('Auu____2406 -> FStar_Pprint.document) ->
      'Auu____2406 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2438 = FStar_ST.op_Bang comment_stack in
          match uu____2438 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2524 = FStar_Range.range_before_pos crange print_pos in
              if uu____2524
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2588 =
                    let uu____2589 =
                      let uu____2590 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2590
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2589 in
                  comments_before_pos uu____2588 print_pos lookahead_pos))
              else
                (let uu____2592 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2592)) in
        let uu____2593 =
          let uu____2598 =
            let uu____2599 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2599 in
          let uu____2600 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2598 uu____2600 in
        match uu____2593 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2606 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2606
              else comments in
            let uu____2612 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2612
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2625 = FStar_ST.op_Bang comment_stack in
          match uu____2625 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2763 =
                    let uu____2764 =
                      let uu____2765 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2765 in
                    uu____2764 - lbegin in
                  max k uu____2763 in
                let doc2 =
                  let uu____2767 =
                    let uu____2768 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2769 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2768 uu____2769 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2767 in
                let uu____2770 =
                  let uu____2771 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2771 in
                place_comments_until_pos (Prims.parse_int "1") uu____2770
                  pos_end doc2))
          | uu____2772 ->
              let lnum =
                let uu____2780 =
                  let uu____2781 = FStar_Range.line_of_pos pos_end in
                  uu____2781 - lbegin in
                max (Prims.parse_int "1") uu____2780 in
              let uu____2782 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2782
let separate_map_with_comments:
  'Auu____2789 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2789 -> FStar_Pprint.document) ->
          'Auu____2789 Prims.list ->
            ('Auu____2789 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2837 x =
              match uu____2837 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2851 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2851 doc1 in
                  let uu____2852 =
                    let uu____2853 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2853 in
                  let uu____2854 =
                    let uu____2855 =
                      let uu____2856 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2856 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2855 in
                  (uu____2852, uu____2854) in
            let uu____2857 =
              let uu____2864 = FStar_List.hd xs in
              let uu____2865 = FStar_List.tl xs in (uu____2864, uu____2865) in
            match uu____2857 with
            | (x,xs1) ->
                let init1 =
                  let uu____2881 =
                    let uu____2882 =
                      let uu____2883 = extract_range x in
                      FStar_Range.end_of_range uu____2883 in
                    FStar_Range.line_of_pos uu____2882 in
                  let uu____2884 =
                    let uu____2885 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2885 in
                  (uu____2881, uu____2884) in
                let uu____2886 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2886
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3181 =
      let uu____3182 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3183 =
        let uu____3184 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3185 =
          let uu____3186 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3187 =
            let uu____3188 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3188 in
          FStar_Pprint.op_Hat_Hat uu____3186 uu____3187 in
        FStar_Pprint.op_Hat_Hat uu____3184 uu____3185 in
      FStar_Pprint.op_Hat_Hat uu____3182 uu____3183 in
    FStar_Pprint.group uu____3181
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3191 =
      let uu____3192 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3192 in
    let uu____3193 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3191 FStar_Pprint.space uu____3193
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3194  ->
    match uu____3194 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3228 =
                match uu____3228 with
                | (kwd,arg) ->
                    let uu____3235 = str "@" in
                    let uu____3236 =
                      let uu____3237 = str kwd in
                      let uu____3238 =
                        let uu____3239 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3239 in
                      FStar_Pprint.op_Hat_Hat uu____3237 uu____3238 in
                    FStar_Pprint.op_Hat_Hat uu____3235 uu____3236 in
              let uu____3240 =
                let uu____3241 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3241 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3240 in
        let uu____3246 =
          let uu____3247 =
            let uu____3248 =
              let uu____3249 =
                let uu____3250 = str doc1 in
                let uu____3251 =
                  let uu____3252 =
                    let uu____3253 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3253 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3252 in
                FStar_Pprint.op_Hat_Hat uu____3250 uu____3251 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3249 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3248 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3247 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3246
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3257 =
          let uu____3258 = str "val" in
          let uu____3259 =
            let uu____3260 =
              let uu____3261 = p_lident lid in
              let uu____3262 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3261 uu____3262 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3260 in
          FStar_Pprint.op_Hat_Hat uu____3258 uu____3259 in
        let uu____3263 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3257 uu____3263
    | FStar_Parser_AST.TopLevelLet (uu____3264,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3289 =
               let uu____3290 = str "let" in
               let uu____3291 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3290 uu____3291 in
             FStar_Pprint.group uu____3289) lbs
    | uu____3292 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3295 =
          let uu____3296 = str "open" in
          let uu____3297 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3296 uu____3297 in
        FStar_Pprint.group uu____3295
    | FStar_Parser_AST.Include uid ->
        let uu____3299 =
          let uu____3300 = str "include" in
          let uu____3301 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3300 uu____3301 in
        FStar_Pprint.group uu____3299
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3304 =
          let uu____3305 = str "module" in
          let uu____3306 =
            let uu____3307 =
              let uu____3308 = p_uident uid1 in
              let uu____3309 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3308 uu____3309 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3307 in
          FStar_Pprint.op_Hat_Hat uu____3305 uu____3306 in
        let uu____3310 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3304 uu____3310
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3312 =
          let uu____3313 = str "module" in
          let uu____3314 =
            let uu____3315 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3315 in
          FStar_Pprint.op_Hat_Hat uu____3313 uu____3314 in
        FStar_Pprint.group uu____3312
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3348 = str "effect" in
          let uu____3349 =
            let uu____3350 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3350 in
          FStar_Pprint.op_Hat_Hat uu____3348 uu____3349 in
        let uu____3351 =
          let uu____3352 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3352 FStar_Pprint.equals in
        let uu____3353 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3351 uu____3353
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3371 = str "type" in
        let uu____3372 = str "and" in
        precede_break_separate_map uu____3371 uu____3372 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3394 = str "let" in
          let uu____3395 =
            let uu____3396 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3396 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3394 uu____3395 in
        let uu____3397 =
          let uu____3398 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3398 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3397 p_letbinding lbs
          (fun uu____3406  ->
             match uu____3406 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3415 =
          let uu____3416 = str "val" in
          let uu____3417 =
            let uu____3418 =
              let uu____3419 = p_lident lid in
              let uu____3420 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3419 uu____3420 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3418 in
          FStar_Pprint.op_Hat_Hat uu____3416 uu____3417 in
        let uu____3421 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3415 uu____3421
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3425 =
            let uu____3426 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3426 FStar_Util.is_upper in
          if uu____3425
          then FStar_Pprint.empty
          else
            (let uu____3428 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3428 FStar_Pprint.space) in
        let uu____3429 =
          let uu____3430 =
            let uu____3431 = p_ident id in
            let uu____3432 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3431 uu____3432 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3430 in
        let uu____3433 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3429 uu____3433
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3440 = str "exception" in
        let uu____3441 =
          let uu____3442 =
            let uu____3443 = p_uident uid in
            let uu____3444 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3449 = str "of" in
                   let uu____3450 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3449 uu____3450) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3443 uu____3444 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3442 in
        FStar_Pprint.op_Hat_Hat uu____3440 uu____3441
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3452 = str "new_effect" in
        let uu____3453 =
          let uu____3454 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3454 in
        FStar_Pprint.op_Hat_Hat uu____3452 uu____3453
    | FStar_Parser_AST.SubEffect se ->
        let uu____3456 = str "sub_effect" in
        let uu____3457 =
          let uu____3458 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3458 in
        FStar_Pprint.op_Hat_Hat uu____3456 uu____3457
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3461 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3461 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3462 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3463) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___126_3480  ->
    match uu___126_3480 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3482 = str "#set-options" in
        let uu____3483 =
          let uu____3484 =
            let uu____3485 = str s in FStar_Pprint.dquotes uu____3485 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3484 in
        FStar_Pprint.op_Hat_Hat uu____3482 uu____3483
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3489 = str "#reset-options" in
        let uu____3490 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3494 =
                 let uu____3495 = str s in FStar_Pprint.dquotes uu____3495 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3494) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3489 uu____3490
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
  fun uu____3546  ->
    match uu____3546 with
    | (typedecl,fsdoc_opt) ->
        let uu____3559 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3560 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3559 uu____3560
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___127_3561  ->
    match uu___127_3561 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3576 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3592 =
          let uu____3593 = p_typ t in prefix2 FStar_Pprint.equals uu____3593 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3637 =
          match uu____3637 with
          | (lid1,t,doc_opt) ->
              let uu____3653 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3653 in
        let p_fields uu____3667 =
          let uu____3668 =
            let uu____3669 =
              let uu____3670 =
                let uu____3671 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3671 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3670 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3669 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3668 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3735 =
          match uu____3735 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3761 =
                  let uu____3762 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3762 in
                FStar_Range.extend_to_end_of_line uu____3761 in
              let p_constructorBranch decl =
                let uu____3795 =
                  let uu____3796 =
                    let uu____3797 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3797 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3796 in
                FStar_Pprint.group uu____3795 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3817 =
          let uu____3818 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3818 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3833  ->
             let uu____3834 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3834)
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
            let uu____3849 = p_ident lid in
            let uu____3850 =
              let uu____3851 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3851 in
            FStar_Pprint.op_Hat_Hat uu____3849 uu____3850
          else
            (let binders_doc =
               let uu____3854 = p_typars bs in
               let uu____3855 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3859 =
                        let uu____3860 =
                          let uu____3861 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3861 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3860 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3859) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3854 uu____3855 in
             let uu____3862 = p_ident lid in
             let uu____3863 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3862 binders_doc uu____3863)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3864  ->
    match uu____3864 with
    | (lid,t,doc_opt) ->
        let uu____3880 =
          let uu____3881 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3882 =
            let uu____3883 = p_lident lid in
            let uu____3884 =
              let uu____3885 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3885 in
            FStar_Pprint.op_Hat_Hat uu____3883 uu____3884 in
          FStar_Pprint.op_Hat_Hat uu____3881 uu____3882 in
        FStar_Pprint.group uu____3880
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3886  ->
    match uu____3886 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3914 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3915 =
          let uu____3916 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3917 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3922 =
                   let uu____3923 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3923 in
                 let uu____3924 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3922 uu____3924) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3916 uu____3917 in
        FStar_Pprint.op_Hat_Hat uu____3914 uu____3915
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3925  ->
    match uu____3925 with
    | (pat,uu____3931) ->
        let uu____3932 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3943 =
                let uu____3944 =
                  let uu____3945 =
                    let uu____3946 =
                      let uu____3947 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3947 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3946 in
                  FStar_Pprint.group uu____3945 in
                FStar_Pprint.op_Hat_Hat break1 uu____3944 in
              (pat1, uu____3943)
          | uu____3948 -> (pat, FStar_Pprint.empty) in
        (match uu____3932 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3952);
                     FStar_Parser_AST.prange = uu____3953;_},pats)
                  ->
                  let uu____3963 =
                    let uu____3964 = p_lident x in
                    let uu____3965 =
                      let uu____3966 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____3966 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3964 uu____3965 in
                  FStar_Pprint.group uu____3963
              | uu____3967 ->
                  let uu____3968 =
                    let uu____3969 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____3969 ascr_doc in
                  FStar_Pprint.group uu____3968))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3970  ->
    match uu____3970 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____3978 =
          let uu____3979 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____3979 in
        let uu____3980 = p_term e in prefix2 uu____3978 uu____3980
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___128_3981  ->
    match uu___128_3981 with
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
        let uu____4006 = p_uident uid in
        let uu____4007 = p_binders true bs in
        let uu____4008 =
          let uu____4009 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____4009 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4006 uu____4007 uu____4008
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
          let uu____4018 =
            let uu____4019 =
              let uu____4020 =
                let uu____4021 = p_uident uid in
                let uu____4022 = p_binders true bs in
                let uu____4023 =
                  let uu____4024 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____4024 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4021 uu____4022 uu____4023 in
              FStar_Pprint.group uu____4020 in
            let uu____4025 =
              let uu____4026 = str "with" in
              let uu____4027 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____4026 uu____4027 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4019 uu____4025 in
          braces_with_nesting uu____4018
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4057 =
          let uu____4058 = p_lident lid in
          let uu____4059 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____4058 uu____4059 in
        let uu____4060 = p_simpleTerm e in prefix2 uu____4057 uu____4060
    | uu____4061 ->
        let uu____4062 =
          let uu____4063 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4063 in
        failwith uu____4062
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4118 =
        match uu____4118 with
        | (kwd,t) ->
            let uu____4125 =
              let uu____4126 = str kwd in
              let uu____4127 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4126 uu____4127 in
            let uu____4128 = p_simpleTerm t in prefix2 uu____4125 uu____4128 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4133 =
      let uu____4134 =
        let uu____4135 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4136 =
          let uu____4137 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4137 in
        FStar_Pprint.op_Hat_Hat uu____4135 uu____4136 in
      let uu____4138 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4134 uu____4138 in
    let uu____4139 =
      let uu____4140 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4140 in
    FStar_Pprint.op_Hat_Hat uu____4133 uu____4139
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___129_4141  ->
    match uu___129_4141 with
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
    let uu____4143 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4143
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___130_4144  ->
    match uu___130_4144 with
    | FStar_Parser_AST.Rec  ->
        let uu____4145 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4145
    | FStar_Parser_AST.Mutable  ->
        let uu____4146 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4146
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___131_4147  ->
    match uu___131_4147 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4152 =
          let uu____4153 =
            let uu____4154 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4154 in
          FStar_Pprint.separate_map uu____4153 p_tuplePattern pats in
        FStar_Pprint.group uu____4152
    | uu____4155 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4162 =
          let uu____4163 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4163 p_constructorPattern pats in
        FStar_Pprint.group uu____4162
    | uu____4164 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4167;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4172 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4173 = p_constructorPattern hd1 in
        let uu____4174 = p_constructorPattern tl1 in
        infix0 uu____4172 uu____4173 uu____4174
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4176;_},pats)
        ->
        let uu____4182 = p_quident uid in
        let uu____4183 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4182 uu____4183
    | uu____4184 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4188 =
          let uu____4193 =
            let uu____4194 = unparen t in uu____4194.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4193) in
        (match uu____4188 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4199;
               FStar_Parser_AST.blevel = uu____4200;
               FStar_Parser_AST.aqual = uu____4201;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4207 =
               let uu____4208 = p_ident lid in
               p_refinement aqual uu____4208 t1 phi in
             soft_parens_with_nesting uu____4207
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4210;
               FStar_Parser_AST.blevel = uu____4211;
               FStar_Parser_AST.aqual = uu____4212;_},phi))
             ->
             let uu____4214 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4214
         | uu____4215 ->
             let uu____4220 =
               let uu____4221 = p_tuplePattern pat in
               let uu____4222 =
                 let uu____4223 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4224 =
                   let uu____4225 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4225 in
                 FStar_Pprint.op_Hat_Hat uu____4223 uu____4224 in
               FStar_Pprint.op_Hat_Hat uu____4221 uu____4222 in
             soft_parens_with_nesting uu____4220)
    | FStar_Parser_AST.PatList pats ->
        let uu____4229 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4229 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4244 =
          match uu____4244 with
          | (lid,pat) ->
              let uu____4251 = p_qlident lid in
              let uu____4252 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4251 uu____4252 in
        let uu____4253 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4253
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4263 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4264 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4265 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4263 uu____4264 uu____4265
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4276 =
          let uu____4277 =
            let uu____4278 = str (FStar_Ident.text_of_id op) in
            let uu____4279 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4278 uu____4279 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4277 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4276
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4287 = FStar_Pprint.optional p_aqual aqual in
        let uu____4288 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4287 uu____4288
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4290 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4293;
           FStar_Parser_AST.prange = uu____4294;_},uu____4295)
        ->
        let uu____4300 = p_tuplePattern p in
        soft_parens_with_nesting uu____4300
    | FStar_Parser_AST.PatTuple (uu____4301,false ) ->
        let uu____4306 = p_tuplePattern p in
        soft_parens_with_nesting uu____4306
    | uu____4307 ->
        let uu____4308 =
          let uu____4309 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4309 in
        failwith uu____4308
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4313 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4314 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4313 uu____4314
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4319 =
              let uu____4320 = unparen t in uu____4320.FStar_Parser_AST.tm in
            match uu____4319 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4323;
                   FStar_Parser_AST.blevel = uu____4324;
                   FStar_Parser_AST.aqual = uu____4325;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4327 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4327 t1 phi
            | uu____4328 ->
                let uu____4329 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4330 =
                  let uu____4331 = p_lident lid in
                  let uu____4332 =
                    let uu____4333 =
                      let uu____4334 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4335 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4334 uu____4335 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4333 in
                  FStar_Pprint.op_Hat_Hat uu____4331 uu____4332 in
                FStar_Pprint.op_Hat_Hat uu____4329 uu____4330 in
          if is_atomic
          then
            let uu____4336 =
              let uu____4337 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4337 in
            FStar_Pprint.group uu____4336
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4339 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4345 =
            let uu____4346 = unparen t in uu____4346.FStar_Parser_AST.tm in
          (match uu____4345 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4348;
                  FStar_Parser_AST.blevel = uu____4349;
                  FStar_Parser_AST.aqual = uu____4350;_},phi)
               ->
               if is_atomic
               then
                 let uu____4352 =
                   let uu____4353 =
                     let uu____4354 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4354 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4353 in
                 FStar_Pprint.group uu____4352
               else
                 (let uu____4356 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4356)
           | uu____4357 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4365 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4366 =
            let uu____4367 =
              let uu____4368 =
                let uu____4369 = p_appTerm t in
                let uu____4370 =
                  let uu____4371 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4371 in
                FStar_Pprint.op_Hat_Hat uu____4369 uu____4370 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4368 in
            FStar_Pprint.op_Hat_Hat binder uu____4367 in
          FStar_Pprint.op_Hat_Hat uu____4365 uu____4366
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
    let uu____4385 =
      let uu____4386 = unparen e in uu____4386.FStar_Parser_AST.tm in
    match uu____4385 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4389 =
          let uu____4390 =
            let uu____4391 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4391 FStar_Pprint.semi in
          FStar_Pprint.group uu____4390 in
        let uu____4392 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4389 uu____4392
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4396 =
          let uu____4397 =
            let uu____4398 =
              let uu____4399 = p_lident x in
              let uu____4400 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4399 uu____4400 in
            let uu____4401 =
              let uu____4402 = p_noSeqTerm e1 in
              let uu____4403 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4402 uu____4403 in
            op_Hat_Slash_Plus_Hat uu____4398 uu____4401 in
          FStar_Pprint.group uu____4397 in
        let uu____4404 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4396 uu____4404
    | uu____4405 ->
        let uu____4406 = p_noSeqTerm e in FStar_Pprint.group uu____4406
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4409 =
      let uu____4410 = unparen e in uu____4410.FStar_Parser_AST.tm in
    match uu____4409 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4415 =
          let uu____4416 = p_tmIff e1 in
          let uu____4417 =
            let uu____4418 =
              let uu____4419 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4419 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4418 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4416 uu____4417 in
        FStar_Pprint.group uu____4415
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4425 =
          let uu____4426 = p_tmIff e1 in
          let uu____4427 =
            let uu____4428 =
              let uu____4429 =
                let uu____4430 = p_typ t in
                let uu____4431 =
                  let uu____4432 = str "by" in
                  let uu____4433 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4432 uu____4433 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4430 uu____4431 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4429 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4428 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4426 uu____4427 in
        FStar_Pprint.group uu____4425
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4434;_},e1::e2::e3::[])
        ->
        let uu____4440 =
          let uu____4441 =
            let uu____4442 =
              let uu____4443 = p_atomicTermNotQUident e1 in
              let uu____4444 =
                let uu____4445 =
                  let uu____4446 =
                    let uu____4447 = p_term e2 in
                    soft_parens_with_nesting uu____4447 in
                  let uu____4448 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4446 uu____4448 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4445 in
              FStar_Pprint.op_Hat_Hat uu____4443 uu____4444 in
            FStar_Pprint.group uu____4442 in
          let uu____4449 =
            let uu____4450 = p_noSeqTerm e3 in jump2 uu____4450 in
          FStar_Pprint.op_Hat_Hat uu____4441 uu____4449 in
        FStar_Pprint.group uu____4440
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4451;_},e1::e2::e3::[])
        ->
        let uu____4457 =
          let uu____4458 =
            let uu____4459 =
              let uu____4460 = p_atomicTermNotQUident e1 in
              let uu____4461 =
                let uu____4462 =
                  let uu____4463 =
                    let uu____4464 = p_term e2 in
                    soft_brackets_with_nesting uu____4464 in
                  let uu____4465 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4463 uu____4465 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4462 in
              FStar_Pprint.op_Hat_Hat uu____4460 uu____4461 in
            FStar_Pprint.group uu____4459 in
          let uu____4466 =
            let uu____4467 = p_noSeqTerm e3 in jump2 uu____4467 in
          FStar_Pprint.op_Hat_Hat uu____4458 uu____4466 in
        FStar_Pprint.group uu____4457
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4477 =
          let uu____4478 = str "requires" in
          let uu____4479 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4478 uu____4479 in
        FStar_Pprint.group uu____4477
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4489 =
          let uu____4490 = str "ensures" in
          let uu____4491 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4490 uu____4491 in
        FStar_Pprint.group uu____4489
    | FStar_Parser_AST.Attributes es ->
        let uu____4495 =
          let uu____4496 = str "attributes" in
          let uu____4497 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4496 uu____4497 in
        FStar_Pprint.group uu____4495
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4501 = is_unit e3 in
        if uu____4501
        then
          let uu____4502 =
            let uu____4503 =
              let uu____4504 = str "if" in
              let uu____4505 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4504 uu____4505 in
            let uu____4506 =
              let uu____4507 = str "then" in
              let uu____4508 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4507 uu____4508 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4503 uu____4506 in
          FStar_Pprint.group uu____4502
        else
          (let e2_doc =
             let uu____4511 =
               let uu____4512 = unparen e2 in uu____4512.FStar_Parser_AST.tm in
             match uu____4511 with
             | FStar_Parser_AST.If (uu____4513,uu____4514,e31) when
                 is_unit e31 ->
                 let uu____4516 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4516
             | uu____4517 -> p_noSeqTerm e2 in
           let uu____4518 =
             let uu____4519 =
               let uu____4520 = str "if" in
               let uu____4521 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4520 uu____4521 in
             let uu____4522 =
               let uu____4523 =
                 let uu____4524 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4524 e2_doc in
               let uu____4525 =
                 let uu____4526 = str "else" in
                 let uu____4527 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4526 uu____4527 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4523 uu____4525 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4519 uu____4522 in
           FStar_Pprint.group uu____4518)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4550 =
          let uu____4551 =
            let uu____4552 = str "try" in
            let uu____4553 = p_noSeqTerm e1 in prefix2 uu____4552 uu____4553 in
          let uu____4554 =
            let uu____4555 = str "with" in
            let uu____4556 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4555 uu____4556 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4551 uu____4554 in
        FStar_Pprint.group uu____4550
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4587 =
          let uu____4588 =
            let uu____4589 = str "match" in
            let uu____4590 = p_noSeqTerm e1 in
            let uu____4591 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4589 uu____4590 uu____4591 in
          let uu____4592 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4588 uu____4592 in
        FStar_Pprint.group uu____4587
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4603 =
          let uu____4604 =
            let uu____4605 = str "let open" in
            let uu____4606 = p_quident uid in
            let uu____4607 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4605 uu____4606 uu____4607 in
          let uu____4608 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4604 uu____4608 in
        FStar_Pprint.group uu____4603
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4625 = str "let" in
          let uu____4626 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4625 uu____4626 in
        let uu____4627 =
          let uu____4628 =
            let uu____4629 =
              let uu____4630 = str "and" in
              precede_break_separate_map let_doc uu____4630 p_letbinding lbs in
            let uu____4635 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4629 uu____4635 in
          FStar_Pprint.group uu____4628 in
        let uu____4636 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4627 uu____4636
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4639;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4642;
                                                         FStar_Parser_AST.level
                                                           = uu____4643;_})
        when matches_var maybe_x x ->
        let uu____4670 =
          let uu____4671 = str "function" in
          let uu____4672 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4671 uu____4672 in
        FStar_Pprint.group uu____4670
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4683 =
          let uu____4684 = p_lident id in
          let uu____4685 =
            let uu____4686 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4686 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4684 uu____4685 in
        FStar_Pprint.group uu____4683
    | uu____4687 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4690 =
      let uu____4691 = unparen e in uu____4691.FStar_Parser_AST.tm in
    match uu____4690 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4707 =
          let uu____4708 =
            let uu____4709 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4709 FStar_Pprint.space in
          let uu____4710 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4708 uu____4710 FStar_Pprint.dot in
        let uu____4711 =
          let uu____4712 = p_trigger trigger in
          let uu____4713 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4712 uu____4713 in
        prefix2 uu____4707 uu____4711
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4729 =
          let uu____4730 =
            let uu____4731 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4731 FStar_Pprint.space in
          let uu____4732 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4730 uu____4732 FStar_Pprint.dot in
        let uu____4733 =
          let uu____4734 = p_trigger trigger in
          let uu____4735 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4734 uu____4735 in
        prefix2 uu____4729 uu____4733
    | uu____4736 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4738 =
      let uu____4739 = unparen e in uu____4739.FStar_Parser_AST.tm in
    match uu____4738 with
    | FStar_Parser_AST.QForall uu____4740 -> str "forall"
    | FStar_Parser_AST.QExists uu____4753 -> str "exists"
    | uu____4766 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___132_4767  ->
    match uu___132_4767 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4779 =
          let uu____4780 =
            let uu____4781 = str "pattern" in
            let uu____4782 =
              let uu____4783 =
                let uu____4784 = p_disjunctivePats pats in jump2 uu____4784 in
              let uu____4785 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4783 uu____4785 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4781 uu____4782 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4780 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4779
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4791 = str "\\/" in
    FStar_Pprint.separate_map uu____4791 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4797 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4797
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4799 =
      let uu____4800 = unparen e in uu____4800.FStar_Parser_AST.tm in
    match uu____4799 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4807 =
          let uu____4808 = str "fun" in
          let uu____4809 =
            let uu____4810 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4810 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4808 uu____4809 in
        let uu____4811 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4807 uu____4811
    | uu____4812 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4815  ->
    match uu____4815 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4834 =
            let uu____4835 = unparen e in uu____4835.FStar_Parser_AST.tm in
          match uu____4834 with
          | FStar_Parser_AST.Match uu____4838 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4853 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4869);
                 FStar_Parser_AST.prange = uu____4870;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4872);
                                                               FStar_Parser_AST.range
                                                                 = uu____4873;
                                                               FStar_Parser_AST.level
                                                                 = uu____4874;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4901 -> (fun x  -> x) in
        let uu____4903 =
          let uu____4904 =
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = p_disjunctivePattern pat in
                  let uu____4909 =
                    let uu____4910 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4910 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4908 uu____4909 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4907 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4906 in
            FStar_Pprint.group uu____4905 in
          let uu____4911 =
            let uu____4912 = p_term e in maybe_paren uu____4912 in
          op_Hat_Slash_Plus_Hat uu____4904 uu____4911 in
        FStar_Pprint.group uu____4903
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___133_4913  ->
    match uu___133_4913 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4917 = str "when" in
        let uu____4918 =
          let uu____4919 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4919 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4917 uu____4918
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4921 =
      let uu____4922 = unparen e in uu____4922.FStar_Parser_AST.tm in
    match uu____4921 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4923;_},e1::e2::[])
        ->
        let uu____4928 = str "<==>" in
        let uu____4929 = p_tmImplies e1 in
        let uu____4930 = p_tmIff e2 in
        infix0 uu____4928 uu____4929 uu____4930
    | uu____4931 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4933 =
      let uu____4934 = unparen e in uu____4934.FStar_Parser_AST.tm in
    match uu____4933 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4935;_},e1::e2::[])
        ->
        let uu____4940 = str "==>" in
        let uu____4941 = p_tmArrow p_tmFormula e1 in
        let uu____4942 = p_tmImplies e2 in
        infix0 uu____4940 uu____4941 uu____4942
    | uu____4943 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4948 =
        let uu____4949 = unparen e in uu____4949.FStar_Parser_AST.tm in
      match uu____4948 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4956 =
            let uu____4957 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4962 = p_binder false b in
                   let uu____4963 =
                     let uu____4964 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4964 in
                   FStar_Pprint.op_Hat_Hat uu____4962 uu____4963) bs in
            let uu____4965 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____4957 uu____4965 in
          FStar_Pprint.group uu____4956
      | uu____4966 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4968 =
      let uu____4969 = unparen e in uu____4969.FStar_Parser_AST.tm in
    match uu____4968 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4970;_},e1::e2::[])
        ->
        let uu____4975 = str "\\/" in
        let uu____4976 = p_tmFormula e1 in
        let uu____4977 = p_tmConjunction e2 in
        infix0 uu____4975 uu____4976 uu____4977
    | uu____4978 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4980 =
      let uu____4981 = unparen e in uu____4981.FStar_Parser_AST.tm in
    match uu____4980 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4982;_},e1::e2::[])
        ->
        let uu____4987 = str "/\\" in
        let uu____4988 = p_tmConjunction e1 in
        let uu____4989 = p_tmTuple e2 in
        infix0 uu____4987 uu____4988 uu____4989
    | uu____4990 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4993 =
      let uu____4994 = unparen e in uu____4994.FStar_Parser_AST.tm in
    match uu____4993 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5009 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5009
          (fun uu____5017  ->
             match uu____5017 with | (e1,uu____5023) -> p_tmEq e1) args
    | uu____5024 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5029 =
             let uu____5030 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5030 in
           FStar_Pprint.group uu____5029)
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
      let uu____5075 =
        let uu____5076 = unparen e in uu____5076.FStar_Parser_AST.tm in
      match uu____5075 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5083 = levels op1 in
          (match uu____5083 with
           | (left1,mine,right1) ->
               let uu____5093 =
                 let uu____5094 = FStar_All.pipe_left str op1 in
                 let uu____5095 = p_tmEq' left1 e1 in
                 let uu____5096 = p_tmEq' right1 e2 in
                 infix0 uu____5094 uu____5095 uu____5096 in
               paren_if curr mine uu____5093)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5097;_},e1::e2::[])
          ->
          let uu____5102 =
            let uu____5103 = p_tmEq e1 in
            let uu____5104 =
              let uu____5105 =
                let uu____5106 =
                  let uu____5107 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5107 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5106 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5105 in
            FStar_Pprint.op_Hat_Hat uu____5103 uu____5104 in
          FStar_Pprint.group uu____5102
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5108;_},e1::[])
          ->
          let uu____5112 = levels "-" in
          (match uu____5112 with
           | (left1,mine,right1) ->
               let uu____5122 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5122)
      | uu____5123 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5178 =
        let uu____5179 = unparen e in uu____5179.FStar_Parser_AST.tm in
      match uu____5178 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5182)::(e2,uu____5184)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5204 = is_list e in Prims.op_Negation uu____5204)
          ->
          let op = "::" in
          let uu____5206 = levels op in
          (match uu____5206 with
           | (left1,mine,right1) ->
               let uu____5216 =
                 let uu____5217 = str op in
                 let uu____5218 = p_tmNoEq' left1 e1 in
                 let uu____5219 = p_tmNoEq' right1 e2 in
                 infix0 uu____5217 uu____5218 uu____5219 in
               paren_if curr mine uu____5216)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5227 = levels op in
          (match uu____5227 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5241 = p_binder false b in
                 let uu____5242 =
                   let uu____5243 =
                     let uu____5244 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5244 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5243 in
                 FStar_Pprint.op_Hat_Hat uu____5241 uu____5242 in
               let uu____5245 =
                 let uu____5246 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5247 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5246 uu____5247 in
               paren_if curr mine uu____5245)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5254 = levels op1 in
          (match uu____5254 with
           | (left1,mine,right1) ->
               let uu____5264 =
                 let uu____5265 = str op1 in
                 let uu____5266 = p_tmNoEq' left1 e1 in
                 let uu____5267 = p_tmNoEq' right1 e2 in
                 infix0 uu____5265 uu____5266 uu____5267 in
               paren_if curr mine uu____5264)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5270 =
            let uu____5271 = p_lidentOrUnderscore lid in
            let uu____5272 =
              let uu____5273 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5273 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5271 uu____5272 in
          FStar_Pprint.group uu____5270
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5294 =
            let uu____5295 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5296 =
              let uu____5297 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5297 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5295 uu____5296 in
          braces_with_nesting uu____5294
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5302;_},e1::[])
          ->
          let uu____5306 =
            let uu____5307 = str "~" in
            let uu____5308 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5307 uu____5308 in
          FStar_Pprint.group uu____5306
      | uu____5309 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5311 = p_appTerm e in
    let uu____5312 =
      let uu____5313 =
        let uu____5314 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5314 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5313 in
    FStar_Pprint.op_Hat_Hat uu____5311 uu____5312
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5319 =
            let uu____5320 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5320 t phi in
          soft_parens_with_nesting uu____5319
      | FStar_Parser_AST.TAnnotated uu____5321 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5326 ->
          let uu____5327 =
            let uu____5328 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5328 in
          failwith uu____5327
      | FStar_Parser_AST.TVariable uu____5329 ->
          let uu____5330 =
            let uu____5331 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5331 in
          failwith uu____5330
      | FStar_Parser_AST.NoName uu____5332 ->
          let uu____5333 =
            let uu____5334 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5334 in
          failwith uu____5333
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5335  ->
    match uu____5335 with
    | (lid,e) ->
        let uu____5342 =
          let uu____5343 = p_qlident lid in
          let uu____5344 =
            let uu____5345 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5345 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5343 uu____5344 in
        FStar_Pprint.group uu____5342
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5347 =
      let uu____5348 = unparen e in uu____5348.FStar_Parser_AST.tm in
    match uu____5347 with
    | FStar_Parser_AST.App uu____5349 when is_general_application e ->
        let uu____5356 = head_and_args e in
        (match uu____5356 with
         | (head1,args) ->
             let uu____5381 =
               let uu____5392 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5392
               then
                 let uu____5449 =
                   FStar_Util.take
                     (fun uu____5473  ->
                        match uu____5473 with
                        | (uu____5478,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5449 with
                 | (fs_typ_args,args1) ->
                     let uu____5516 =
                       let uu____5517 = p_indexingTerm head1 in
                       let uu____5518 =
                         let uu____5519 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5519 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5517 uu____5518 in
                     (uu____5516, args1)
               else
                 (let uu____5531 = p_indexingTerm head1 in (uu____5531, args)) in
             (match uu____5381 with
              | (head_doc,args1) ->
                  let uu____5552 =
                    let uu____5553 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5553 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5552))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5573 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5573)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5591 =
               let uu____5592 = p_quident lid in
               let uu____5593 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5592 uu____5593 in
             FStar_Pprint.group uu____5591
         | hd1::tl1 ->
             let uu____5610 =
               let uu____5611 =
                 let uu____5612 =
                   let uu____5613 = p_quident lid in
                   let uu____5614 = p_argTerm hd1 in
                   prefix2 uu____5613 uu____5614 in
                 FStar_Pprint.group uu____5612 in
               let uu____5615 =
                 let uu____5616 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5616 in
               FStar_Pprint.op_Hat_Hat uu____5611 uu____5615 in
             FStar_Pprint.group uu____5610)
    | uu____5621 -> p_indexingTerm e
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
         (let uu____5630 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5630 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5632 = str "#" in
        let uu____5633 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5632 uu____5633
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5635  ->
    match uu____5635 with | (e,uu____5641) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5646 =
        let uu____5647 = unparen e in uu____5647.FStar_Parser_AST.tm in
      match uu____5646 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5648;_},e1::e2::[])
          ->
          let uu____5653 =
            let uu____5654 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5655 =
              let uu____5656 =
                let uu____5657 = p_term e2 in
                soft_parens_with_nesting uu____5657 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5656 in
            FStar_Pprint.op_Hat_Hat uu____5654 uu____5655 in
          FStar_Pprint.group uu____5653
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5658;_},e1::e2::[])
          ->
          let uu____5663 =
            let uu____5664 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5665 =
              let uu____5666 =
                let uu____5667 = p_term e2 in
                soft_brackets_with_nesting uu____5667 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5666 in
            FStar_Pprint.op_Hat_Hat uu____5664 uu____5665 in
          FStar_Pprint.group uu____5663
      | uu____5668 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5671 =
      let uu____5672 = unparen e in uu____5672.FStar_Parser_AST.tm in
    match uu____5671 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5675 = p_quident lid in
        let uu____5676 =
          let uu____5677 =
            let uu____5678 = p_term e1 in soft_parens_with_nesting uu____5678 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5677 in
        FStar_Pprint.op_Hat_Hat uu____5675 uu____5676
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5684 = str (FStar_Ident.text_of_id op) in
        let uu____5685 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5684 uu____5685
    | uu____5686 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5688 =
      let uu____5689 = unparen e in uu____5689.FStar_Parser_AST.tm in
    match uu____5688 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5694 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5701 = str (FStar_Ident.text_of_id op) in
        let uu____5702 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5701 uu____5702
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5706 =
          let uu____5707 =
            let uu____5708 = str (FStar_Ident.text_of_id op) in
            let uu____5709 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5708 uu____5709 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5707 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5706
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5724 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5725 =
          let uu____5726 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5727 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5726 p_tmEq uu____5727 in
        let uu____5734 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5724 uu____5725 uu____5734
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5737 =
          let uu____5738 = p_atomicTermNotQUident e1 in
          let uu____5739 =
            let uu____5740 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5740 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5738 uu____5739 in
        FStar_Pprint.group uu____5737
    | uu____5741 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5743 =
      let uu____5744 = unparen e in uu____5744.FStar_Parser_AST.tm in
    match uu____5743 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5748 = p_quident constr_lid in
        let uu____5749 =
          let uu____5750 =
            let uu____5751 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5751 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5750 in
        FStar_Pprint.op_Hat_Hat uu____5748 uu____5749
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5753 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5753 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5755 = p_term e1 in soft_parens_with_nesting uu____5755
    | uu____5756 when is_array e ->
        let es = extract_from_list e in
        let uu____5760 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5761 =
          let uu____5762 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5762 p_noSeqTerm es in
        let uu____5763 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5760 uu____5761 uu____5763
    | uu____5764 when is_list e ->
        let uu____5765 =
          let uu____5766 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5767 = extract_from_list e in
          separate_map_or_flow uu____5766 p_noSeqTerm uu____5767 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5765 FStar_Pprint.rbracket
    | uu____5770 when is_lex_list e ->
        let uu____5771 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5772 =
          let uu____5773 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5774 = extract_from_list e in
          separate_map_or_flow uu____5773 p_noSeqTerm uu____5774 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5771 uu____5772 FStar_Pprint.rbracket
    | uu____5777 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5781 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5782 =
          let uu____5783 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5783 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5781 uu____5782 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5787 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5788 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5787 uu____5788
    | FStar_Parser_AST.Op (op,args) when
        let uu____5795 = handleable_op op args in
        Prims.op_Negation uu____5795 ->
        let uu____5796 =
          let uu____5797 =
            let uu____5798 =
              let uu____5799 =
                let uu____5800 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5800
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5799 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5798 in
          Prims.strcat "Operation " uu____5797 in
        failwith uu____5796
    | FStar_Parser_AST.Uvar uu____5801 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5802 = p_term e in soft_parens_with_nesting uu____5802
    | FStar_Parser_AST.Const uu____5803 ->
        let uu____5804 = p_term e in soft_parens_with_nesting uu____5804
    | FStar_Parser_AST.Op uu____5805 ->
        let uu____5812 = p_term e in soft_parens_with_nesting uu____5812
    | FStar_Parser_AST.Tvar uu____5813 ->
        let uu____5814 = p_term e in soft_parens_with_nesting uu____5814
    | FStar_Parser_AST.Var uu____5815 ->
        let uu____5816 = p_term e in soft_parens_with_nesting uu____5816
    | FStar_Parser_AST.Name uu____5817 ->
        let uu____5818 = p_term e in soft_parens_with_nesting uu____5818
    | FStar_Parser_AST.Construct uu____5819 ->
        let uu____5830 = p_term e in soft_parens_with_nesting uu____5830
    | FStar_Parser_AST.Abs uu____5831 ->
        let uu____5838 = p_term e in soft_parens_with_nesting uu____5838
    | FStar_Parser_AST.App uu____5839 ->
        let uu____5846 = p_term e in soft_parens_with_nesting uu____5846
    | FStar_Parser_AST.Let uu____5847 ->
        let uu____5860 = p_term e in soft_parens_with_nesting uu____5860
    | FStar_Parser_AST.LetOpen uu____5861 ->
        let uu____5866 = p_term e in soft_parens_with_nesting uu____5866
    | FStar_Parser_AST.Seq uu____5867 ->
        let uu____5872 = p_term e in soft_parens_with_nesting uu____5872
    | FStar_Parser_AST.Bind uu____5873 ->
        let uu____5880 = p_term e in soft_parens_with_nesting uu____5880
    | FStar_Parser_AST.If uu____5881 ->
        let uu____5888 = p_term e in soft_parens_with_nesting uu____5888
    | FStar_Parser_AST.Match uu____5889 ->
        let uu____5904 = p_term e in soft_parens_with_nesting uu____5904
    | FStar_Parser_AST.TryWith uu____5905 ->
        let uu____5920 = p_term e in soft_parens_with_nesting uu____5920
    | FStar_Parser_AST.Ascribed uu____5921 ->
        let uu____5930 = p_term e in soft_parens_with_nesting uu____5930
    | FStar_Parser_AST.Record uu____5931 ->
        let uu____5944 = p_term e in soft_parens_with_nesting uu____5944
    | FStar_Parser_AST.Project uu____5945 ->
        let uu____5950 = p_term e in soft_parens_with_nesting uu____5950
    | FStar_Parser_AST.Product uu____5951 ->
        let uu____5958 = p_term e in soft_parens_with_nesting uu____5958
    | FStar_Parser_AST.Sum uu____5959 ->
        let uu____5966 = p_term e in soft_parens_with_nesting uu____5966
    | FStar_Parser_AST.QForall uu____5967 ->
        let uu____5980 = p_term e in soft_parens_with_nesting uu____5980
    | FStar_Parser_AST.QExists uu____5981 ->
        let uu____5994 = p_term e in soft_parens_with_nesting uu____5994
    | FStar_Parser_AST.Refine uu____5995 ->
        let uu____6000 = p_term e in soft_parens_with_nesting uu____6000
    | FStar_Parser_AST.NamedTyp uu____6001 ->
        let uu____6006 = p_term e in soft_parens_with_nesting uu____6006
    | FStar_Parser_AST.Requires uu____6007 ->
        let uu____6014 = p_term e in soft_parens_with_nesting uu____6014
    | FStar_Parser_AST.Ensures uu____6015 ->
        let uu____6022 = p_term e in soft_parens_with_nesting uu____6022
    | FStar_Parser_AST.Assign uu____6023 ->
        let uu____6028 = p_term e in soft_parens_with_nesting uu____6028
    | FStar_Parser_AST.Attributes uu____6029 ->
        let uu____6032 = p_term e in soft_parens_with_nesting uu____6032
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___136_6033  ->
    match uu___136_6033 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6037 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6037
    | FStar_Const.Const_string (s,uu____6039) ->
        let uu____6040 = str s in FStar_Pprint.dquotes uu____6040
    | FStar_Const.Const_bytearray (bytes,uu____6042) ->
        let uu____6047 =
          let uu____6048 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6048 in
        let uu____6049 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6047 uu____6049
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___134_6067 =
          match uu___134_6067 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___135_6071 =
          match uu___135_6071 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6082  ->
               match uu____6082 with
               | (s,w) ->
                   let uu____6089 = signedness s in
                   let uu____6090 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6089 uu____6090)
            sign_width_opt in
        let uu____6091 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6091 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6093 = FStar_Range.string_of_range r in str uu____6093
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6095 = p_quident lid in
        let uu____6096 =
          let uu____6097 =
            let uu____6098 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6098 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6097 in
        FStar_Pprint.op_Hat_Hat uu____6095 uu____6096
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6100 = str "u#" in
    let uu____6101 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6100 uu____6101
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6103 =
      let uu____6104 = unparen u in uu____6104.FStar_Parser_AST.tm in
    match uu____6103 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6105;_},u1::u2::[])
        ->
        let uu____6110 =
          let uu____6111 = p_universeFrom u1 in
          let uu____6112 =
            let uu____6113 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6113 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6111 uu____6112 in
        FStar_Pprint.group uu____6110
    | FStar_Parser_AST.App uu____6114 ->
        let uu____6121 = head_and_args u in
        (match uu____6121 with
         | (head1,args) ->
             let uu____6146 =
               let uu____6147 = unparen head1 in
               uu____6147.FStar_Parser_AST.tm in
             (match uu____6146 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6149 =
                    let uu____6150 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6151 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6159  ->
                           match uu____6159 with
                           | (u1,uu____6165) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6150 uu____6151 in
                  FStar_Pprint.group uu____6149
              | uu____6166 ->
                  let uu____6167 =
                    let uu____6168 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6168 in
                  failwith uu____6167))
    | uu____6169 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6171 =
      let uu____6172 = unparen u in uu____6172.FStar_Parser_AST.tm in
    match uu____6171 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6195 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6195
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6196;_},uu____6197::uu____6198::[])
        ->
        let uu____6201 = p_universeFrom u in
        soft_parens_with_nesting uu____6201
    | FStar_Parser_AST.App uu____6202 ->
        let uu____6209 = p_universeFrom u in
        soft_parens_with_nesting uu____6209
    | uu____6210 ->
        let uu____6211 =
          let uu____6212 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6212 in
        failwith uu____6211
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
       | FStar_Parser_AST.Module (uu____6279,decls) ->
           let uu____6285 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6285
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6294,decls,uu____6296) ->
           let uu____6301 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6301
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6379  ->
         match uu____6379 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6419,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6425,decls,uu____6427) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6499 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6512;
                 FStar_Parser_AST.doc = uu____6513;
                 FStar_Parser_AST.quals = uu____6514;
                 FStar_Parser_AST.attrs = uu____6515;_}::uu____6516 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6522 =
                   let uu____6525 =
                     let uu____6528 = FStar_List.tl ds in d :: uu____6528 in
                   d0 :: uu____6525 in
                 (uu____6522, (d0.FStar_Parser_AST.drange))
             | uu____6533 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6499 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6618 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6618 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6795 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6795, comments1))))))