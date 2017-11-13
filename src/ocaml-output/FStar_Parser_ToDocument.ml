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
      let uu____900 =
        let uu____901 = unparen e1 in uu____901.FStar_Parser_AST.tm in
      match uu____900 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____919 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____933 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____937 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____941 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___60_958  ->
    match uu___60_958 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___61_983  ->
      match uu___61_983 with
      | FStar_Util.Inl c ->
          let uu____989 = FStar_String.get s (Prims.parse_int "0") in
          uu____989 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____1006 .
    Prims.string ->
      ('Auu____1006,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1024  ->
      match uu____1024 with
      | (assoc_levels,tokens) ->
          let uu____1049 = FStar_List.tryFind (matches_token s) tokens in
          uu____1049 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1071 .
    Prims.unit ->
      (associativity,('Auu____1071,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1082  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1098 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1098) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1109  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1133 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1133) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1144  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1164 .
    Prims.unit ->
      (associativity,('Auu____1164,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1175  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1191 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1191) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1202  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1222 .
    Prims.unit ->
      (associativity,('Auu____1222,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1233  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1249 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1249) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1260  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1276 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1276) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1287  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1311 .
    Prims.unit ->
      (associativity,('Auu____1311,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1322  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1338 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1338) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1349  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1365 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1365) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1376  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1392 .
    Prims.unit ->
      (associativity,('Auu____1392,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1403  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1419 .
    Prims.unit ->
      (associativity,('Auu____1419,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1430  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1446 .
    Prims.unit ->
      (associativity,('Auu____1446,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1457  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___62_1644 =
    match uu___62_1644 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1682  ->
         match uu____1682 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1757 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1757 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1805) ->
          assoc_levels
      | uu____1846 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1880 .
    ('Auu____1880,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1936 =
        FStar_List.tryFind
          (fun uu____1974  ->
             match uu____1974 with
             | (uu____1991,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____1936 with
      | FStar_Pervasives_Native.Some ((uu____2029,l1,uu____2031),uu____2032)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2083 =
            let uu____2084 =
              let uu____2085 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2085 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2084 in
          failwith uu____2083 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2117 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2117) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2130  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2204 =
      let uu____2217 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2217 (operatorInfix0ad12 ()) in
    uu____2204 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2320 =
      let uu____2333 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2333 opinfix34 in
    uu____2320 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2394 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2394
    then Prims.parse_int "1"
    else
      (let uu____2396 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2396
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2402 . FStar_Ident.ident -> 'Auu____2402 Prims.list -> Prims.bool =
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
      | uu____2415 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2445 .
    ('Auu____2445 -> FStar_Pprint.document) ->
      'Auu____2445 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2477 = FStar_ST.op_Bang comment_stack in
          match uu____2477 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2563 = FStar_Range.range_before_pos crange print_pos in
              if uu____2563
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2627 =
                    let uu____2628 =
                      let uu____2629 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2629
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2628 in
                  comments_before_pos uu____2627 print_pos lookahead_pos))
              else
                (let uu____2631 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2631)) in
        let uu____2632 =
          let uu____2637 =
            let uu____2638 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2638 in
          let uu____2639 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2637 uu____2639 in
        match uu____2632 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2645 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2645
              else comments in
            let uu____2651 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2651
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2664 = FStar_ST.op_Bang comment_stack in
          match uu____2664 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2802 =
                    let uu____2803 =
                      let uu____2804 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2804 in
                    uu____2803 - lbegin in
                  max k uu____2802 in
                let doc2 =
                  let uu____2806 =
                    let uu____2807 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2808 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2807 uu____2808 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2806 in
                let uu____2809 =
                  let uu____2810 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2810 in
                place_comments_until_pos (Prims.parse_int "1") uu____2809
                  pos_end doc2))
          | uu____2811 ->
              let lnum =
                let uu____2819 =
                  let uu____2820 = FStar_Range.line_of_pos pos_end in
                  uu____2820 - lbegin in
                max (Prims.parse_int "1") uu____2819 in
              let uu____2821 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2821
let separate_map_with_comments:
  'Auu____2828 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2828 -> FStar_Pprint.document) ->
          'Auu____2828 Prims.list ->
            ('Auu____2828 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2876 x =
              match uu____2876 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____2890 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2890 doc1 in
                  let uu____2891 =
                    let uu____2892 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____2892 in
                  let uu____2893 =
                    let uu____2894 =
                      let uu____2895 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____2895 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2894 in
                  (uu____2891, uu____2893) in
            let uu____2896 =
              let uu____2903 = FStar_List.hd xs in
              let uu____2904 = FStar_List.tl xs in (uu____2903, uu____2904) in
            match uu____2896 with
            | (x,xs1) ->
                let init1 =
                  let uu____2920 =
                    let uu____2921 =
                      let uu____2922 = extract_range x in
                      FStar_Range.end_of_range uu____2922 in
                    FStar_Range.line_of_pos uu____2921 in
                  let uu____2923 =
                    let uu____2924 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2924 in
                  (uu____2920, uu____2923) in
                let uu____2925 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____2925
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3220 =
      let uu____3221 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3222 =
        let uu____3223 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3224 =
          let uu____3225 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3226 =
            let uu____3227 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3227 in
          FStar_Pprint.op_Hat_Hat uu____3225 uu____3226 in
        FStar_Pprint.op_Hat_Hat uu____3223 uu____3224 in
      FStar_Pprint.op_Hat_Hat uu____3221 uu____3222 in
    FStar_Pprint.group uu____3220
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3230 =
      let uu____3231 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3231 in
    let uu____3232 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3230 FStar_Pprint.space uu____3232
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3233  ->
    match uu____3233 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3267 =
                match uu____3267 with
                | (kwd,arg) ->
                    let uu____3274 = str "@" in
                    let uu____3275 =
                      let uu____3276 = str kwd in
                      let uu____3277 =
                        let uu____3278 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3278 in
                      FStar_Pprint.op_Hat_Hat uu____3276 uu____3277 in
                    FStar_Pprint.op_Hat_Hat uu____3274 uu____3275 in
              let uu____3279 =
                let uu____3280 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3280 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3279 in
        let uu____3285 =
          let uu____3286 =
            let uu____3287 =
              let uu____3288 =
                let uu____3289 = str doc1 in
                let uu____3290 =
                  let uu____3291 =
                    let uu____3292 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3292 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3291 in
                FStar_Pprint.op_Hat_Hat uu____3289 uu____3290 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3288 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3287 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3286 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3285
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3296 =
          let uu____3297 = str "val" in
          let uu____3298 =
            let uu____3299 =
              let uu____3300 = p_lident lid in
              let uu____3301 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3300 uu____3301 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3299 in
          FStar_Pprint.op_Hat_Hat uu____3297 uu____3298 in
        let uu____3302 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3296 uu____3302
    | FStar_Parser_AST.TopLevelLet (uu____3303,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3328 =
               let uu____3329 = str "let" in
               let uu____3330 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3329 uu____3330 in
             FStar_Pprint.group uu____3328) lbs
    | uu____3331 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3334 =
          let uu____3335 = str "open" in
          let uu____3336 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3335 uu____3336 in
        FStar_Pprint.group uu____3334
    | FStar_Parser_AST.Include uid ->
        let uu____3338 =
          let uu____3339 = str "include" in
          let uu____3340 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3339 uu____3340 in
        FStar_Pprint.group uu____3338
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3343 =
          let uu____3344 = str "module" in
          let uu____3345 =
            let uu____3346 =
              let uu____3347 = p_uident uid1 in
              let uu____3348 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3347 uu____3348 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3346 in
          FStar_Pprint.op_Hat_Hat uu____3344 uu____3345 in
        let uu____3349 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3343 uu____3349
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3351 =
          let uu____3352 = str "module" in
          let uu____3353 =
            let uu____3354 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3354 in
          FStar_Pprint.op_Hat_Hat uu____3352 uu____3353 in
        FStar_Pprint.group uu____3351
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3387 = str "effect" in
          let uu____3388 =
            let uu____3389 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3389 in
          FStar_Pprint.op_Hat_Hat uu____3387 uu____3388 in
        let uu____3390 =
          let uu____3391 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3391 FStar_Pprint.equals in
        let uu____3392 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3390 uu____3392
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3410 = str "type" in
        let uu____3411 = str "and" in
        precede_break_separate_map uu____3410 uu____3411 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3433 = str "let" in
          let uu____3434 =
            let uu____3435 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3435 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3433 uu____3434 in
        let uu____3436 =
          let uu____3437 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3437 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3436 p_letbinding lbs
          (fun uu____3445  ->
             match uu____3445 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3454 =
          let uu____3455 = str "val" in
          let uu____3456 =
            let uu____3457 =
              let uu____3458 = p_lident lid in
              let uu____3459 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3458 uu____3459 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3457 in
          FStar_Pprint.op_Hat_Hat uu____3455 uu____3456 in
        let uu____3460 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3454 uu____3460
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3464 =
            let uu____3465 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3465 FStar_Util.is_upper in
          if uu____3464
          then FStar_Pprint.empty
          else
            (let uu____3473 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3473 FStar_Pprint.space) in
        let uu____3474 =
          let uu____3475 =
            let uu____3476 = p_ident id1 in
            let uu____3477 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3476 uu____3477 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3475 in
        let uu____3478 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3474 uu____3478
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3485 = str "exception" in
        let uu____3486 =
          let uu____3487 =
            let uu____3488 = p_uident uid in
            let uu____3489 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3494 = str "of" in
                   let uu____3495 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3494 uu____3495) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3488 uu____3489 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3487 in
        FStar_Pprint.op_Hat_Hat uu____3485 uu____3486
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3497 = str "new_effect" in
        let uu____3498 =
          let uu____3499 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3499 in
        FStar_Pprint.op_Hat_Hat uu____3497 uu____3498
    | FStar_Parser_AST.SubEffect se ->
        let uu____3501 = str "sub_effect" in
        let uu____3502 =
          let uu____3503 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3503 in
        FStar_Pprint.op_Hat_Hat uu____3501 uu____3502
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3506 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3506 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3507 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3508) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___63_3525  ->
    match uu___63_3525 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3527 = str "#set-options" in
        let uu____3528 =
          let uu____3529 =
            let uu____3530 = str s in FStar_Pprint.dquotes uu____3530 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3529 in
        FStar_Pprint.op_Hat_Hat uu____3527 uu____3528
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3534 = str "#reset-options" in
        let uu____3535 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3539 =
                 let uu____3540 = str s in FStar_Pprint.dquotes uu____3540 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3539) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3534 uu____3535
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
  fun uu____3591  ->
    match uu____3591 with
    | (typedecl,fsdoc_opt) ->
        let uu____3604 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3605 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3604 uu____3605
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___64_3606  ->
    match uu___64_3606 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3621 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3637 =
          let uu____3638 = p_typ t in prefix2 FStar_Pprint.equals uu____3638 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3682 =
          match uu____3682 with
          | (lid1,t,doc_opt) ->
              let uu____3698 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3698 in
        let p_fields uu____3712 =
          let uu____3713 =
            let uu____3714 =
              let uu____3715 =
                let uu____3716 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3716 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3715 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3714 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3713 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3780 =
          match uu____3780 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3806 =
                  let uu____3807 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3807 in
                FStar_Range.extend_to_end_of_line uu____3806 in
              let p_constructorBranch decl =
                let uu____3840 =
                  let uu____3841 =
                    let uu____3842 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3842 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3841 in
                FStar_Pprint.group uu____3840 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3862 =
          let uu____3863 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3863 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3878  ->
             let uu____3879 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____3879)
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
            let uu____3894 = p_ident lid in
            let uu____3895 =
              let uu____3896 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3896 in
            FStar_Pprint.op_Hat_Hat uu____3894 uu____3895
          else
            (let binders_doc =
               let uu____3899 = p_typars bs in
               let uu____3900 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3904 =
                        let uu____3905 =
                          let uu____3906 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3906 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3905 in
                      FStar_Pprint.op_Hat_Hat break1 uu____3904) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____3899 uu____3900 in
             let uu____3907 = p_ident lid in
             let uu____3908 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3907 binders_doc uu____3908)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3909  ->
    match uu____3909 with
    | (lid,t,doc_opt) ->
        let uu____3925 =
          let uu____3926 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____3927 =
            let uu____3928 = p_lident lid in
            let uu____3929 =
              let uu____3930 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3930 in
            FStar_Pprint.op_Hat_Hat uu____3928 uu____3929 in
          FStar_Pprint.op_Hat_Hat uu____3926 uu____3927 in
        FStar_Pprint.group uu____3925
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3931  ->
    match uu____3931 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____3959 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____3960 =
          let uu____3961 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____3962 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3967 =
                   let uu____3968 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3968 in
                 let uu____3969 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____3967 uu____3969) t_opt in
          FStar_Pprint.op_Hat_Hat uu____3961 uu____3962 in
        FStar_Pprint.op_Hat_Hat uu____3959 uu____3960
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3970  ->
    match uu____3970 with
    | (pat,uu____3976) ->
        let uu____3977 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3988 =
                let uu____3989 =
                  let uu____3990 =
                    let uu____3991 =
                      let uu____3992 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3992 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3991 in
                  FStar_Pprint.group uu____3990 in
                FStar_Pprint.op_Hat_Hat break1 uu____3989 in
              (pat1, uu____3988)
          | uu____3993 -> (pat, FStar_Pprint.empty) in
        (match uu____3977 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3997);
                     FStar_Parser_AST.prange = uu____3998;_},pats)
                  ->
                  let uu____4008 =
                    let uu____4009 = p_lident x in
                    let uu____4010 =
                      let uu____4011 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____4011 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4009 uu____4010 in
                  FStar_Pprint.group uu____4008
              | uu____4012 ->
                  let uu____4013 =
                    let uu____4014 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____4014 ascr_doc in
                  FStar_Pprint.group uu____4013))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4015  ->
    match uu____4015 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____4023 =
          let uu____4024 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____4024 in
        let uu____4025 = p_term e in prefix2 uu____4023 uu____4025
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___65_4026  ->
    match uu___65_4026 with
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
        let uu____4051 = p_uident uid in
        let uu____4052 = p_binders true bs in
        let uu____4053 =
          let uu____4054 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____4054 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4051 uu____4052 uu____4053
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
          let uu____4063 =
            let uu____4064 =
              let uu____4065 =
                let uu____4066 = p_uident uid in
                let uu____4067 = p_binders true bs in
                let uu____4068 =
                  let uu____4069 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____4069 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4066 uu____4067 uu____4068 in
              FStar_Pprint.group uu____4065 in
            let uu____4070 =
              let uu____4071 = str "with" in
              let uu____4072 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____4071 uu____4072 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4064 uu____4070 in
          braces_with_nesting uu____4063
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4102 =
          let uu____4103 = p_lident lid in
          let uu____4104 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____4103 uu____4104 in
        let uu____4105 = p_simpleTerm e in prefix2 uu____4102 uu____4105
    | uu____4106 ->
        let uu____4107 =
          let uu____4108 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4108 in
        failwith uu____4107
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4163 =
        match uu____4163 with
        | (kwd,t) ->
            let uu____4170 =
              let uu____4171 = str kwd in
              let uu____4172 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4171 uu____4172 in
            let uu____4173 = p_simpleTerm t in prefix2 uu____4170 uu____4173 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4178 =
      let uu____4179 =
        let uu____4180 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4181 =
          let uu____4182 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4182 in
        FStar_Pprint.op_Hat_Hat uu____4180 uu____4181 in
      let uu____4183 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4179 uu____4183 in
    let uu____4184 =
      let uu____4185 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4185 in
    FStar_Pprint.op_Hat_Hat uu____4178 uu____4184
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___66_4186  ->
    match uu___66_4186 with
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
    let uu____4188 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4188
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___67_4189  ->
    match uu___67_4189 with
    | FStar_Parser_AST.Rec  ->
        let uu____4190 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4190
    | FStar_Parser_AST.Mutable  ->
        let uu____4191 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4191
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___68_4192  ->
    match uu___68_4192 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4197 =
          let uu____4198 =
            let uu____4199 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4199 in
          FStar_Pprint.separate_map uu____4198 p_tuplePattern pats in
        FStar_Pprint.group uu____4197
    | uu____4200 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4207 =
          let uu____4208 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4208 p_constructorPattern pats in
        FStar_Pprint.group uu____4207
    | uu____4209 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4212;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4217 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4218 = p_constructorPattern hd1 in
        let uu____4219 = p_constructorPattern tl1 in
        infix0 uu____4217 uu____4218 uu____4219
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4221;_},pats)
        ->
        let uu____4227 = p_quident uid in
        let uu____4228 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4227 uu____4228
    | uu____4229 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4233 =
          let uu____4238 =
            let uu____4239 = unparen t in uu____4239.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4238) in
        (match uu____4233 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4244;
               FStar_Parser_AST.blevel = uu____4245;
               FStar_Parser_AST.aqual = uu____4246;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4252 =
               let uu____4253 = p_ident lid in
               p_refinement aqual uu____4253 t1 phi in
             soft_parens_with_nesting uu____4252
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4255;
               FStar_Parser_AST.blevel = uu____4256;
               FStar_Parser_AST.aqual = uu____4257;_},phi))
             ->
             let uu____4259 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4259
         | uu____4260 ->
             let uu____4265 =
               let uu____4266 = p_tuplePattern pat in
               let uu____4267 =
                 let uu____4268 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4269 =
                   let uu____4270 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4270 in
                 FStar_Pprint.op_Hat_Hat uu____4268 uu____4269 in
               FStar_Pprint.op_Hat_Hat uu____4266 uu____4267 in
             soft_parens_with_nesting uu____4265)
    | FStar_Parser_AST.PatList pats ->
        let uu____4274 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4274 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4289 =
          match uu____4289 with
          | (lid,pat) ->
              let uu____4296 = p_qlident lid in
              let uu____4297 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4296 uu____4297 in
        let uu____4298 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4298
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4308 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4309 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4310 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4308 uu____4309 uu____4310
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4321 =
          let uu____4322 =
            let uu____4323 = str (FStar_Ident.text_of_id op) in
            let uu____4324 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4323 uu____4324 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4322 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4321
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4332 = FStar_Pprint.optional p_aqual aqual in
        let uu____4333 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4332 uu____4333
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4335 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4338;
           FStar_Parser_AST.prange = uu____4339;_},uu____4340)
        ->
        let uu____4345 = p_tuplePattern p in
        soft_parens_with_nesting uu____4345
    | FStar_Parser_AST.PatTuple (uu____4346,false ) ->
        let uu____4351 = p_tuplePattern p in
        soft_parens_with_nesting uu____4351
    | uu____4352 ->
        let uu____4353 =
          let uu____4354 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4354 in
        failwith uu____4353
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4358 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4359 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4358 uu____4359
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4364 =
              let uu____4365 = unparen t in uu____4365.FStar_Parser_AST.tm in
            match uu____4364 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4368;
                   FStar_Parser_AST.blevel = uu____4369;
                   FStar_Parser_AST.aqual = uu____4370;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4372 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4372 t1 phi
            | uu____4373 ->
                let uu____4374 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4375 =
                  let uu____4376 = p_lident lid in
                  let uu____4377 =
                    let uu____4378 =
                      let uu____4379 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4380 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4379 uu____4380 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4378 in
                  FStar_Pprint.op_Hat_Hat uu____4376 uu____4377 in
                FStar_Pprint.op_Hat_Hat uu____4374 uu____4375 in
          if is_atomic
          then
            let uu____4381 =
              let uu____4382 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4382 in
            FStar_Pprint.group uu____4381
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4384 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4390 =
            let uu____4391 = unparen t in uu____4391.FStar_Parser_AST.tm in
          (match uu____4390 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4393;
                  FStar_Parser_AST.blevel = uu____4394;
                  FStar_Parser_AST.aqual = uu____4395;_},phi)
               ->
               if is_atomic
               then
                 let uu____4397 =
                   let uu____4398 =
                     let uu____4399 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4399 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4398 in
                 FStar_Pprint.group uu____4397
               else
                 (let uu____4401 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4401)
           | uu____4402 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4410 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4411 =
            let uu____4412 =
              let uu____4413 =
                let uu____4414 = p_appTerm t in
                let uu____4415 =
                  let uu____4416 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4416 in
                FStar_Pprint.op_Hat_Hat uu____4414 uu____4415 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4413 in
            FStar_Pprint.op_Hat_Hat binder uu____4412 in
          FStar_Pprint.op_Hat_Hat uu____4410 uu____4411
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
    let uu____4430 =
      let uu____4431 = unparen e in uu____4431.FStar_Parser_AST.tm in
    match uu____4430 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4434 =
          let uu____4435 =
            let uu____4436 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4436 FStar_Pprint.semi in
          FStar_Pprint.group uu____4435 in
        let uu____4437 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4434 uu____4437
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4441 =
          let uu____4442 =
            let uu____4443 =
              let uu____4444 = p_lident x in
              let uu____4445 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4444 uu____4445 in
            let uu____4446 =
              let uu____4447 = p_noSeqTerm e1 in
              let uu____4448 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4447 uu____4448 in
            op_Hat_Slash_Plus_Hat uu____4443 uu____4446 in
          FStar_Pprint.group uu____4442 in
        let uu____4449 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4441 uu____4449
    | uu____4450 ->
        let uu____4451 = p_noSeqTerm e in FStar_Pprint.group uu____4451
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4454 =
      let uu____4455 = unparen e in uu____4455.FStar_Parser_AST.tm in
    match uu____4454 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4460 =
          let uu____4461 = p_tmIff e1 in
          let uu____4462 =
            let uu____4463 =
              let uu____4464 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4464 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4463 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4461 uu____4462 in
        FStar_Pprint.group uu____4460
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4470 =
          let uu____4471 = p_tmIff e1 in
          let uu____4472 =
            let uu____4473 =
              let uu____4474 =
                let uu____4475 = p_typ t in
                let uu____4476 =
                  let uu____4477 = str "by" in
                  let uu____4478 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4477 uu____4478 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4475 uu____4476 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4474 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4473 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4471 uu____4472 in
        FStar_Pprint.group uu____4470
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4479;_},e1::e2::e3::[])
        ->
        let uu____4485 =
          let uu____4486 =
            let uu____4487 =
              let uu____4488 = p_atomicTermNotQUident e1 in
              let uu____4489 =
                let uu____4490 =
                  let uu____4491 =
                    let uu____4492 = p_term e2 in
                    soft_parens_with_nesting uu____4492 in
                  let uu____4493 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4491 uu____4493 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4490 in
              FStar_Pprint.op_Hat_Hat uu____4488 uu____4489 in
            FStar_Pprint.group uu____4487 in
          let uu____4494 =
            let uu____4495 = p_noSeqTerm e3 in jump2 uu____4495 in
          FStar_Pprint.op_Hat_Hat uu____4486 uu____4494 in
        FStar_Pprint.group uu____4485
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4496;_},e1::e2::e3::[])
        ->
        let uu____4502 =
          let uu____4503 =
            let uu____4504 =
              let uu____4505 = p_atomicTermNotQUident e1 in
              let uu____4506 =
                let uu____4507 =
                  let uu____4508 =
                    let uu____4509 = p_term e2 in
                    soft_brackets_with_nesting uu____4509 in
                  let uu____4510 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4508 uu____4510 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4507 in
              FStar_Pprint.op_Hat_Hat uu____4505 uu____4506 in
            FStar_Pprint.group uu____4504 in
          let uu____4511 =
            let uu____4512 = p_noSeqTerm e3 in jump2 uu____4512 in
          FStar_Pprint.op_Hat_Hat uu____4503 uu____4511 in
        FStar_Pprint.group uu____4502
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4522 =
          let uu____4523 = str "requires" in
          let uu____4524 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4523 uu____4524 in
        FStar_Pprint.group uu____4522
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4534 =
          let uu____4535 = str "ensures" in
          let uu____4536 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4535 uu____4536 in
        FStar_Pprint.group uu____4534
    | FStar_Parser_AST.Attributes es ->
        let uu____4540 =
          let uu____4541 = str "attributes" in
          let uu____4542 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4541 uu____4542 in
        FStar_Pprint.group uu____4540
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4546 = is_unit e3 in
        if uu____4546
        then
          let uu____4547 =
            let uu____4548 =
              let uu____4549 = str "if" in
              let uu____4550 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4549 uu____4550 in
            let uu____4551 =
              let uu____4552 = str "then" in
              let uu____4553 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4552 uu____4553 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4548 uu____4551 in
          FStar_Pprint.group uu____4547
        else
          (let e2_doc =
             let uu____4556 =
               let uu____4557 = unparen e2 in uu____4557.FStar_Parser_AST.tm in
             match uu____4556 with
             | FStar_Parser_AST.If (uu____4558,uu____4559,e31) when
                 is_unit e31 ->
                 let uu____4561 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4561
             | uu____4562 -> p_noSeqTerm e2 in
           let uu____4563 =
             let uu____4564 =
               let uu____4565 = str "if" in
               let uu____4566 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4565 uu____4566 in
             let uu____4567 =
               let uu____4568 =
                 let uu____4569 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4569 e2_doc in
               let uu____4570 =
                 let uu____4571 = str "else" in
                 let uu____4572 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4571 uu____4572 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4568 uu____4570 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4564 uu____4567 in
           FStar_Pprint.group uu____4563)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4595 =
          let uu____4596 =
            let uu____4597 = str "try" in
            let uu____4598 = p_noSeqTerm e1 in prefix2 uu____4597 uu____4598 in
          let uu____4599 =
            let uu____4600 = str "with" in
            let uu____4601 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4600 uu____4601 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4596 uu____4599 in
        FStar_Pprint.group uu____4595
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4632 =
          let uu____4633 =
            let uu____4634 = str "match" in
            let uu____4635 = p_noSeqTerm e1 in
            let uu____4636 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4634 uu____4635 uu____4636 in
          let uu____4637 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4633 uu____4637 in
        FStar_Pprint.group uu____4632
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4648 =
          let uu____4649 =
            let uu____4650 = str "let open" in
            let uu____4651 = p_quident uid in
            let uu____4652 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4650 uu____4651 uu____4652 in
          let uu____4653 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4649 uu____4653 in
        FStar_Pprint.group uu____4648
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4670 = str "let" in
          let uu____4671 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4670 uu____4671 in
        let uu____4672 =
          let uu____4673 =
            let uu____4674 =
              let uu____4675 = str "and" in
              precede_break_separate_map let_doc uu____4675 p_letbinding lbs in
            let uu____4680 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4674 uu____4680 in
          FStar_Pprint.group uu____4673 in
        let uu____4681 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4672 uu____4681
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4684;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4687;
                                                         FStar_Parser_AST.level
                                                           = uu____4688;_})
        when matches_var maybe_x x ->
        let uu____4715 =
          let uu____4716 = str "function" in
          let uu____4717 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4716 uu____4717 in
        FStar_Pprint.group uu____4715
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4728 =
          let uu____4729 = p_lident id1 in
          let uu____4730 =
            let uu____4731 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4731 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4729 uu____4730 in
        FStar_Pprint.group uu____4728
    | uu____4732 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4735 =
      let uu____4736 = unparen e in uu____4736.FStar_Parser_AST.tm in
    match uu____4735 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4752 =
          let uu____4753 =
            let uu____4754 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4754 FStar_Pprint.space in
          let uu____4755 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4753 uu____4755 FStar_Pprint.dot in
        let uu____4756 =
          let uu____4757 = p_trigger trigger in
          let uu____4758 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4757 uu____4758 in
        prefix2 uu____4752 uu____4756
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4774 =
          let uu____4775 =
            let uu____4776 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4776 FStar_Pprint.space in
          let uu____4777 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4775 uu____4777 FStar_Pprint.dot in
        let uu____4778 =
          let uu____4779 = p_trigger trigger in
          let uu____4780 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4779 uu____4780 in
        prefix2 uu____4774 uu____4778
    | uu____4781 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4783 =
      let uu____4784 = unparen e in uu____4784.FStar_Parser_AST.tm in
    match uu____4783 with
    | FStar_Parser_AST.QForall uu____4785 -> str "forall"
    | FStar_Parser_AST.QExists uu____4798 -> str "exists"
    | uu____4811 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___69_4812  ->
    match uu___69_4812 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4824 =
          let uu____4825 =
            let uu____4826 = str "pattern" in
            let uu____4827 =
              let uu____4828 =
                let uu____4829 = p_disjunctivePats pats in jump2 uu____4829 in
              let uu____4830 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4828 uu____4830 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4826 uu____4827 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4825 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4824
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4836 = str "\\/" in
    FStar_Pprint.separate_map uu____4836 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4842 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4842
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4844 =
      let uu____4845 = unparen e in uu____4845.FStar_Parser_AST.tm in
    match uu____4844 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4852 =
          let uu____4853 = str "fun" in
          let uu____4854 =
            let uu____4855 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4855 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4853 uu____4854 in
        let uu____4856 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4852 uu____4856
    | uu____4857 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4860  ->
    match uu____4860 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4879 =
            let uu____4880 = unparen e in uu____4880.FStar_Parser_AST.tm in
          match uu____4879 with
          | FStar_Parser_AST.Match uu____4883 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4898 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4914);
                 FStar_Parser_AST.prange = uu____4915;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4917);
                                                               FStar_Parser_AST.range
                                                                 = uu____4918;
                                                               FStar_Parser_AST.level
                                                                 = uu____4919;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4946 -> (fun x  -> x) in
        let uu____4948 =
          let uu____4949 =
            let uu____4950 =
              let uu____4951 =
                let uu____4952 =
                  let uu____4953 = p_disjunctivePattern pat in
                  let uu____4954 =
                    let uu____4955 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____4955 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____4953 uu____4954 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4952 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4951 in
            FStar_Pprint.group uu____4950 in
          let uu____4956 =
            let uu____4957 = p_term e in maybe_paren uu____4957 in
          op_Hat_Slash_Plus_Hat uu____4949 uu____4956 in
        FStar_Pprint.group uu____4948
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___70_4958  ->
    match uu___70_4958 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4962 = str "when" in
        let uu____4963 =
          let uu____4964 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____4964 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____4962 uu____4963
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4966 =
      let uu____4967 = unparen e in uu____4967.FStar_Parser_AST.tm in
    match uu____4966 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4968;_},e1::e2::[])
        ->
        let uu____4973 = str "<==>" in
        let uu____4974 = p_tmImplies e1 in
        let uu____4975 = p_tmIff e2 in
        infix0 uu____4973 uu____4974 uu____4975
    | uu____4976 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4978 =
      let uu____4979 = unparen e in uu____4979.FStar_Parser_AST.tm in
    match uu____4978 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4980;_},e1::e2::[])
        ->
        let uu____4985 = str "==>" in
        let uu____4986 = p_tmArrow p_tmFormula e1 in
        let uu____4987 = p_tmImplies e2 in
        infix0 uu____4985 uu____4986 uu____4987
    | uu____4988 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4993 =
        let uu____4994 = unparen e in uu____4994.FStar_Parser_AST.tm in
      match uu____4993 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5001 =
            let uu____5002 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5007 = p_binder false b in
                   let uu____5008 =
                     let uu____5009 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5009 in
                   FStar_Pprint.op_Hat_Hat uu____5007 uu____5008) bs in
            let uu____5010 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____5002 uu____5010 in
          FStar_Pprint.group uu____5001
      | uu____5011 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5013 =
      let uu____5014 = unparen e in uu____5014.FStar_Parser_AST.tm in
    match uu____5013 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5015;_},e1::e2::[])
        ->
        let uu____5020 = str "\\/" in
        let uu____5021 = p_tmFormula e1 in
        let uu____5022 = p_tmConjunction e2 in
        infix0 uu____5020 uu____5021 uu____5022
    | uu____5023 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5025 =
      let uu____5026 = unparen e in uu____5026.FStar_Parser_AST.tm in
    match uu____5025 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5027;_},e1::e2::[])
        ->
        let uu____5032 = str "/\\" in
        let uu____5033 = p_tmConjunction e1 in
        let uu____5034 = p_tmTuple e2 in
        infix0 uu____5032 uu____5033 uu____5034
    | uu____5035 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5038 =
      let uu____5039 = unparen e in uu____5039.FStar_Parser_AST.tm in
    match uu____5038 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5054 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5054
          (fun uu____5062  ->
             match uu____5062 with | (e1,uu____5068) -> p_tmEq e1) args
    | uu____5069 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5074 =
             let uu____5075 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5075 in
           FStar_Pprint.group uu____5074)
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
      let uu____5120 =
        let uu____5121 = unparen e in uu____5121.FStar_Parser_AST.tm in
      match uu____5120 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5128 = levels op1 in
          (match uu____5128 with
           | (left1,mine,right1) ->
               let uu____5138 =
                 let uu____5139 = FStar_All.pipe_left str op1 in
                 let uu____5140 = p_tmEq' left1 e1 in
                 let uu____5141 = p_tmEq' right1 e2 in
                 infix0 uu____5139 uu____5140 uu____5141 in
               paren_if curr mine uu____5138)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5142;_},e1::e2::[])
          ->
          let uu____5147 =
            let uu____5148 = p_tmEq e1 in
            let uu____5149 =
              let uu____5150 =
                let uu____5151 =
                  let uu____5152 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5152 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5151 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5150 in
            FStar_Pprint.op_Hat_Hat uu____5148 uu____5149 in
          FStar_Pprint.group uu____5147
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5153;_},e1::[])
          ->
          let uu____5157 = levels "-" in
          (match uu____5157 with
           | (left1,mine,right1) ->
               let uu____5167 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5167)
      | uu____5168 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5223 =
        let uu____5224 = unparen e in uu____5224.FStar_Parser_AST.tm in
      match uu____5223 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5227)::(e2,uu____5229)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5249 = is_list e in Prims.op_Negation uu____5249)
          ->
          let op = "::" in
          let uu____5251 = levels op in
          (match uu____5251 with
           | (left1,mine,right1) ->
               let uu____5261 =
                 let uu____5262 = str op in
                 let uu____5263 = p_tmNoEq' left1 e1 in
                 let uu____5264 = p_tmNoEq' right1 e2 in
                 infix0 uu____5262 uu____5263 uu____5264 in
               paren_if curr mine uu____5261)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5272 = levels op in
          (match uu____5272 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5286 = p_binder false b in
                 let uu____5287 =
                   let uu____5288 =
                     let uu____5289 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5289 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5288 in
                 FStar_Pprint.op_Hat_Hat uu____5286 uu____5287 in
               let uu____5290 =
                 let uu____5291 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5292 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5291 uu____5292 in
               paren_if curr mine uu____5290)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5299 = levels op1 in
          (match uu____5299 with
           | (left1,mine,right1) ->
               let uu____5309 =
                 let uu____5310 = str op1 in
                 let uu____5311 = p_tmNoEq' left1 e1 in
                 let uu____5312 = p_tmNoEq' right1 e2 in
                 infix0 uu____5310 uu____5311 uu____5312 in
               paren_if curr mine uu____5309)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5315 =
            let uu____5316 = p_lidentOrUnderscore lid in
            let uu____5317 =
              let uu____5318 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5318 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5316 uu____5317 in
          FStar_Pprint.group uu____5315
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5339 =
            let uu____5340 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5341 =
              let uu____5342 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5342 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5340 uu____5341 in
          braces_with_nesting uu____5339
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5347;_},e1::[])
          ->
          let uu____5351 =
            let uu____5352 = str "~" in
            let uu____5353 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5352 uu____5353 in
          FStar_Pprint.group uu____5351
      | uu____5354 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5356 = p_appTerm e in
    let uu____5357 =
      let uu____5358 =
        let uu____5359 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5359 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5358 in
    FStar_Pprint.op_Hat_Hat uu____5356 uu____5357
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5364 =
            let uu____5365 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5365 t phi in
          soft_parens_with_nesting uu____5364
      | FStar_Parser_AST.TAnnotated uu____5366 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5371 ->
          let uu____5372 =
            let uu____5373 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5373 in
          failwith uu____5372
      | FStar_Parser_AST.TVariable uu____5374 ->
          let uu____5375 =
            let uu____5376 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5376 in
          failwith uu____5375
      | FStar_Parser_AST.NoName uu____5377 ->
          let uu____5378 =
            let uu____5379 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5379 in
          failwith uu____5378
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5380  ->
    match uu____5380 with
    | (lid,e) ->
        let uu____5387 =
          let uu____5388 = p_qlident lid in
          let uu____5389 =
            let uu____5390 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5390 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5388 uu____5389 in
        FStar_Pprint.group uu____5387
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5392 =
      let uu____5393 = unparen e in uu____5393.FStar_Parser_AST.tm in
    match uu____5392 with
    | FStar_Parser_AST.App uu____5394 when is_general_application e ->
        let uu____5401 = head_and_args e in
        (match uu____5401 with
         | (head1,args) ->
             let uu____5426 =
               let uu____5437 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5437
               then
                 let uu____5494 =
                   FStar_Util.take
                     (fun uu____5518  ->
                        match uu____5518 with
                        | (uu____5523,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5494 with
                 | (fs_typ_args,args1) ->
                     let uu____5561 =
                       let uu____5562 = p_indexingTerm head1 in
                       let uu____5563 =
                         let uu____5564 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5564 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5562 uu____5563 in
                     (uu____5561, args1)
               else
                 (let uu____5576 = p_indexingTerm head1 in (uu____5576, args)) in
             (match uu____5426 with
              | (head_doc,args1) ->
                  let uu____5597 =
                    let uu____5598 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5598 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5597))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5618 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5618)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5636 =
               let uu____5637 = p_quident lid in
               let uu____5638 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5637 uu____5638 in
             FStar_Pprint.group uu____5636
         | hd1::tl1 ->
             let uu____5655 =
               let uu____5656 =
                 let uu____5657 =
                   let uu____5658 = p_quident lid in
                   let uu____5659 = p_argTerm hd1 in
                   prefix2 uu____5658 uu____5659 in
                 FStar_Pprint.group uu____5657 in
               let uu____5660 =
                 let uu____5661 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5661 in
               FStar_Pprint.op_Hat_Hat uu____5656 uu____5660 in
             FStar_Pprint.group uu____5655)
    | uu____5666 -> p_indexingTerm e
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
         (let uu____5675 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5675 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5677 = str "#" in
        let uu____5678 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5677 uu____5678
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5680  ->
    match uu____5680 with | (e,uu____5686) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5691 =
        let uu____5692 = unparen e in uu____5692.FStar_Parser_AST.tm in
      match uu____5691 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5693;_},e1::e2::[])
          ->
          let uu____5698 =
            let uu____5699 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5700 =
              let uu____5701 =
                let uu____5702 = p_term e2 in
                soft_parens_with_nesting uu____5702 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5701 in
            FStar_Pprint.op_Hat_Hat uu____5699 uu____5700 in
          FStar_Pprint.group uu____5698
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5703;_},e1::e2::[])
          ->
          let uu____5708 =
            let uu____5709 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5710 =
              let uu____5711 =
                let uu____5712 = p_term e2 in
                soft_brackets_with_nesting uu____5712 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5711 in
            FStar_Pprint.op_Hat_Hat uu____5709 uu____5710 in
          FStar_Pprint.group uu____5708
      | uu____5713 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5716 =
      let uu____5717 = unparen e in uu____5717.FStar_Parser_AST.tm in
    match uu____5716 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5720 = p_quident lid in
        let uu____5721 =
          let uu____5722 =
            let uu____5723 = p_term e1 in soft_parens_with_nesting uu____5723 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5722 in
        FStar_Pprint.op_Hat_Hat uu____5720 uu____5721
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5729 = str (FStar_Ident.text_of_id op) in
        let uu____5730 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5729 uu____5730
    | uu____5731 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5733 =
      let uu____5734 = unparen e in uu____5734.FStar_Parser_AST.tm in
    match uu____5733 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5745 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5752 = str (FStar_Ident.text_of_id op) in
        let uu____5753 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5752 uu____5753
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5757 =
          let uu____5758 =
            let uu____5759 = str (FStar_Ident.text_of_id op) in
            let uu____5760 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5759 uu____5760 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5758 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5757
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5775 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5776 =
          let uu____5777 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5778 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5777 p_tmEq uu____5778 in
        let uu____5785 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5775 uu____5776 uu____5785
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5788 =
          let uu____5789 = p_atomicTermNotQUident e1 in
          let uu____5790 =
            let uu____5791 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5791 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5789 uu____5790 in
        FStar_Pprint.group uu____5788
    | uu____5792 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5794 =
      let uu____5795 = unparen e in uu____5795.FStar_Parser_AST.tm in
    match uu____5794 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5799 = p_quident constr_lid in
        let uu____5800 =
          let uu____5801 =
            let uu____5802 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5802 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5801 in
        FStar_Pprint.op_Hat_Hat uu____5799 uu____5800
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5804 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5804 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5806 = p_term e1 in soft_parens_with_nesting uu____5806
    | uu____5807 when is_array e ->
        let es = extract_from_list e in
        let uu____5811 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5812 =
          let uu____5813 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5813 p_noSeqTerm es in
        let uu____5814 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5811 uu____5812 uu____5814
    | uu____5815 when is_list e ->
        let uu____5816 =
          let uu____5817 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5818 = extract_from_list e in
          separate_map_or_flow uu____5817 p_noSeqTerm uu____5818 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5816 FStar_Pprint.rbracket
    | uu____5821 when is_lex_list e ->
        let uu____5822 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5823 =
          let uu____5824 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5825 = extract_from_list e in
          separate_map_or_flow uu____5824 p_noSeqTerm uu____5825 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5822 uu____5823 FStar_Pprint.rbracket
    | uu____5828 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5832 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5833 =
          let uu____5834 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5834 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5832 uu____5833 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5838 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5839 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5838 uu____5839
    | FStar_Parser_AST.Op (op,args) when
        let uu____5846 = handleable_op op args in
        Prims.op_Negation uu____5846 ->
        let uu____5847 =
          let uu____5848 =
            let uu____5849 =
              let uu____5850 =
                let uu____5851 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5851
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5850 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5849 in
          Prims.strcat "Operation " uu____5848 in
        failwith uu____5847
    | FStar_Parser_AST.Uvar uu____5852 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5853 = p_term e in soft_parens_with_nesting uu____5853
    | FStar_Parser_AST.Const uu____5854 ->
        let uu____5855 = p_term e in soft_parens_with_nesting uu____5855
    | FStar_Parser_AST.Op uu____5856 ->
        let uu____5863 = p_term e in soft_parens_with_nesting uu____5863
    | FStar_Parser_AST.Tvar uu____5864 ->
        let uu____5865 = p_term e in soft_parens_with_nesting uu____5865
    | FStar_Parser_AST.Var uu____5866 ->
        let uu____5867 = p_term e in soft_parens_with_nesting uu____5867
    | FStar_Parser_AST.Name uu____5868 ->
        let uu____5869 = p_term e in soft_parens_with_nesting uu____5869
    | FStar_Parser_AST.Construct uu____5870 ->
        let uu____5881 = p_term e in soft_parens_with_nesting uu____5881
    | FStar_Parser_AST.Abs uu____5882 ->
        let uu____5889 = p_term e in soft_parens_with_nesting uu____5889
    | FStar_Parser_AST.App uu____5890 ->
        let uu____5897 = p_term e in soft_parens_with_nesting uu____5897
    | FStar_Parser_AST.Let uu____5898 ->
        let uu____5911 = p_term e in soft_parens_with_nesting uu____5911
    | FStar_Parser_AST.LetOpen uu____5912 ->
        let uu____5917 = p_term e in soft_parens_with_nesting uu____5917
    | FStar_Parser_AST.Seq uu____5918 ->
        let uu____5923 = p_term e in soft_parens_with_nesting uu____5923
    | FStar_Parser_AST.Bind uu____5924 ->
        let uu____5931 = p_term e in soft_parens_with_nesting uu____5931
    | FStar_Parser_AST.If uu____5932 ->
        let uu____5939 = p_term e in soft_parens_with_nesting uu____5939
    | FStar_Parser_AST.Match uu____5940 ->
        let uu____5955 = p_term e in soft_parens_with_nesting uu____5955
    | FStar_Parser_AST.TryWith uu____5956 ->
        let uu____5971 = p_term e in soft_parens_with_nesting uu____5971
    | FStar_Parser_AST.Ascribed uu____5972 ->
        let uu____5981 = p_term e in soft_parens_with_nesting uu____5981
    | FStar_Parser_AST.Record uu____5982 ->
        let uu____5995 = p_term e in soft_parens_with_nesting uu____5995
    | FStar_Parser_AST.Project uu____5996 ->
        let uu____6001 = p_term e in soft_parens_with_nesting uu____6001
    | FStar_Parser_AST.Product uu____6002 ->
        let uu____6009 = p_term e in soft_parens_with_nesting uu____6009
    | FStar_Parser_AST.Sum uu____6010 ->
        let uu____6017 = p_term e in soft_parens_with_nesting uu____6017
    | FStar_Parser_AST.QForall uu____6018 ->
        let uu____6031 = p_term e in soft_parens_with_nesting uu____6031
    | FStar_Parser_AST.QExists uu____6032 ->
        let uu____6045 = p_term e in soft_parens_with_nesting uu____6045
    | FStar_Parser_AST.Refine uu____6046 ->
        let uu____6051 = p_term e in soft_parens_with_nesting uu____6051
    | FStar_Parser_AST.NamedTyp uu____6052 ->
        let uu____6057 = p_term e in soft_parens_with_nesting uu____6057
    | FStar_Parser_AST.Requires uu____6058 ->
        let uu____6065 = p_term e in soft_parens_with_nesting uu____6065
    | FStar_Parser_AST.Ensures uu____6066 ->
        let uu____6073 = p_term e in soft_parens_with_nesting uu____6073
    | FStar_Parser_AST.Assign uu____6074 ->
        let uu____6079 = p_term e in soft_parens_with_nesting uu____6079
    | FStar_Parser_AST.Attributes uu____6080 ->
        let uu____6083 = p_term e in soft_parens_with_nesting uu____6083
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___73_6084  ->
    match uu___73_6084 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6088 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6088
    | FStar_Const.Const_string (s,uu____6099) ->
        let uu____6100 = str s in FStar_Pprint.dquotes uu____6100
    | FStar_Const.Const_bytearray (bytes,uu____6102) ->
        let uu____6107 =
          let uu____6108 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6108 in
        let uu____6109 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6107 uu____6109
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___71_6127 =
          match uu___71_6127 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___72_6131 =
          match uu___72_6131 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6142  ->
               match uu____6142 with
               | (s,w) ->
                   let uu____6149 = signedness s in
                   let uu____6150 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6149 uu____6150)
            sign_width_opt in
        let uu____6151 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6151 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6153 = FStar_Range.string_of_range r in str uu____6153
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6155 = p_quident lid in
        let uu____6156 =
          let uu____6157 =
            let uu____6158 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6158 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6157 in
        FStar_Pprint.op_Hat_Hat uu____6155 uu____6156
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6160 = str "u#" in
    let uu____6161 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6160 uu____6161
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6163 =
      let uu____6164 = unparen u in uu____6164.FStar_Parser_AST.tm in
    match uu____6163 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6165;_},u1::u2::[])
        ->
        let uu____6170 =
          let uu____6171 = p_universeFrom u1 in
          let uu____6172 =
            let uu____6173 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6173 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6171 uu____6172 in
        FStar_Pprint.group uu____6170
    | FStar_Parser_AST.App uu____6174 ->
        let uu____6181 = head_and_args u in
        (match uu____6181 with
         | (head1,args) ->
             let uu____6206 =
               let uu____6207 = unparen head1 in
               uu____6207.FStar_Parser_AST.tm in
             (match uu____6206 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6209 =
                    let uu____6210 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6211 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6219  ->
                           match uu____6219 with
                           | (u1,uu____6225) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6210 uu____6211 in
                  FStar_Pprint.group uu____6209
              | uu____6226 ->
                  let uu____6227 =
                    let uu____6228 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6228 in
                  failwith uu____6227))
    | uu____6229 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6231 =
      let uu____6232 = unparen u in uu____6232.FStar_Parser_AST.tm in
    match uu____6231 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6255 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6255
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6256;_},uu____6257::uu____6258::[])
        ->
        let uu____6261 = p_universeFrom u in
        soft_parens_with_nesting uu____6261
    | FStar_Parser_AST.App uu____6262 ->
        let uu____6269 = p_universeFrom u in
        soft_parens_with_nesting uu____6269
    | uu____6270 ->
        let uu____6271 =
          let uu____6272 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6272 in
        failwith uu____6271
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
       | FStar_Parser_AST.Module (uu____6339,decls) ->
           let uu____6345 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6345
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6354,decls,uu____6356) ->
           let uu____6361 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6361
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6439  ->
         match uu____6439 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6479,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6485,decls,uu____6487) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6559 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6572;
                 FStar_Parser_AST.doc = uu____6573;
                 FStar_Parser_AST.quals = uu____6574;
                 FStar_Parser_AST.attrs = uu____6575;_}::uu____6576 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6582 =
                   let uu____6585 =
                     let uu____6588 = FStar_List.tl ds in d :: uu____6588 in
                   d0 :: uu____6585 in
                 (uu____6582, (d0.FStar_Parser_AST.drange))
             | uu____6593 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6559 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6678 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6678 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6855 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6855, comments1))))))