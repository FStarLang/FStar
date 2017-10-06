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
    let uu____194 =
      let uu____195 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____195 in
    if uu____194
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____244 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____259 'Auu____260 .
    'Auu____260 ->
      ('Auu____259 -> 'Auu____260) ->
        'Auu____259 FStar_Pervasives_Native.option -> 'Auu____260
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
  'Auu____329 .
    FStar_Pprint.document ->
      ('Auu____329 -> FStar_Pprint.document) ->
        'Auu____329 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____351 =
          let uu____352 =
            let uu____353 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____353 in
          FStar_Pprint.separate_map uu____352 f l in
        FStar_Pprint.group uu____351
let precede_break_separate_map:
  'Auu____364 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____364 -> FStar_Pprint.document) ->
          'Auu____364 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____390 =
            let uu____391 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____392 =
              let uu____393 = FStar_List.hd l in
              FStar_All.pipe_right uu____393 f in
            FStar_Pprint.precede uu____391 uu____392 in
          let uu____394 =
            let uu____395 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____401 =
                   let uu____402 =
                     let uu____403 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____403 in
                   FStar_Pprint.op_Hat_Hat sep uu____402 in
                 FStar_Pprint.op_Hat_Hat break1 uu____401) uu____395 in
          FStar_Pprint.op_Hat_Hat uu____390 uu____394
let concat_break_map:
  'Auu____410 .
    ('Auu____410 -> FStar_Pprint.document) ->
      'Auu____410 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____428 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____432 = f x in FStar_Pprint.op_Hat_Hat uu____432 break1)
          l in
      FStar_Pprint.group uu____428
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
    let uu____461 = str "begin" in
    let uu____462 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____461 contents uu____462
let separate_map_or_flow:
  'Auu____471 .
    FStar_Pprint.document ->
      ('Auu____471 -> FStar_Pprint.document) ->
        'Auu____471 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
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
                    (let uu____557 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____557
                       closing)
let soft_surround_map_or_flow:
  'Auu____576 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____576 -> FStar_Pprint.document) ->
                  'Auu____576 Prims.list -> FStar_Pprint.document
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
                    (let uu____621 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____621
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____635  ->
    match uu____635 with
    | (comment,keywords) ->
        let uu____660 =
          let uu____661 =
            let uu____664 = str comment in
            let uu____665 =
              let uu____668 =
                let uu____671 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____680  ->
                       match uu____680 with
                       | (k,v1) ->
                           let uu____687 =
                             let uu____690 = str k in
                             let uu____691 =
                               let uu____694 =
                                 let uu____697 = str v1 in [uu____697] in
                               FStar_Pprint.rarrow :: uu____694 in
                             uu____690 :: uu____691 in
                           FStar_Pprint.concat uu____687) keywords in
                [uu____671] in
              FStar_Pprint.space :: uu____668 in
            uu____664 :: uu____665 in
          FStar_Pprint.concat uu____661 in
        FStar_Pprint.group uu____660
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____702 =
      let uu____703 = unparen e in uu____703.FStar_Parser_AST.tm in
    match uu____702 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____704 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____713 =
        let uu____714 = unparen t in uu____714.FStar_Parser_AST.tm in
      match uu____713 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____716 -> false
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
        let uu____738 =
          let uu____739 = unparen e in uu____739.FStar_Parser_AST.tm in
        match uu____738 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____752::(e2,uu____754)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____777 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____790 =
      let uu____791 = unparen e in uu____791.FStar_Parser_AST.tm in
    match uu____790 with
    | FStar_Parser_AST.Construct (uu____794,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____805,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____826 = extract_from_list e2 in e1 :: uu____826
    | uu____829 ->
        let uu____830 =
          let uu____831 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____831 in
        failwith uu____830
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____838 =
      let uu____839 = unparen e in uu____839.FStar_Parser_AST.tm in
    match uu____838 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____841;
           FStar_Parser_AST.level = uu____842;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____844 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____849 =
      let uu____850 = unparen e in uu____850.FStar_Parser_AST.tm in
    match uu____849 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____853;
           FStar_Parser_AST.level = uu____854;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____856;
                                                        FStar_Parser_AST.level
                                                          = uu____857;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____859;
                                                   FStar_Parser_AST.level =
                                                     uu____860;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____862;
                FStar_Parser_AST.level = uu____863;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____865;
           FStar_Parser_AST.level = uu____866;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____868 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____875 =
      let uu____876 = unparen e in uu____876.FStar_Parser_AST.tm in
    match uu____875 with
    | FStar_Parser_AST.Var uu____879 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____880;
           FStar_Parser_AST.range = uu____881;
           FStar_Parser_AST.level = uu____882;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____883;
                                                        FStar_Parser_AST.range
                                                          = uu____884;
                                                        FStar_Parser_AST.level
                                                          = uu____885;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____887;
                                                   FStar_Parser_AST.level =
                                                     uu____888;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____889;
                FStar_Parser_AST.range = uu____890;
                FStar_Parser_AST.level = uu____891;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____893;
           FStar_Parser_AST.level = uu____894;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____896 = extract_from_ref_set e1 in
        let uu____899 = extract_from_ref_set e2 in
        FStar_List.append uu____896 uu____899
    | uu____902 ->
        let uu____903 =
          let uu____904 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____904 in
        failwith uu____903
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____911 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____911
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____916 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____916
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
      let uu____983 =
        let uu____984 = unparen e1 in uu____984.FStar_Parser_AST.tm in
      match uu____983 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1002 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1017 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1022 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1027 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___91_1045  ->
    match uu___91_1045 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___92_1072  ->
      match uu___92_1072 with
      | FStar_Util.Inl c ->
          let uu____1078 = FStar_String.get s (Prims.parse_int "0") in
          uu____1078 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____1098 .
    Prims.string ->
      ('Auu____1098,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1116  ->
      match uu____1116 with
      | (assoc_levels,tokens) ->
          let uu____1141 = FStar_List.tryFind (matches_token s) tokens in
          uu____1141 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1164 .
    Prims.unit ->
      (associativity,('Auu____1164,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1175  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1192 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1192) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1203  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1228 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1228) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1239  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1260 .
    Prims.unit ->
      (associativity,('Auu____1260,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1271  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1288 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1288) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1299  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1320 .
    Prims.unit ->
      (associativity,('Auu____1320,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1331  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1348 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1348) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1359  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1376 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1376) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1387  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1412 .
    Prims.unit ->
      (associativity,('Auu____1412,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1423  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1440 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1440) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1451  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1468 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1468) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1479  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1496 .
    Prims.unit ->
      (associativity,('Auu____1496,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1507  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1524 .
    Prims.unit ->
      (associativity,('Auu____1524,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1535  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1552 .
    Prims.unit ->
      (associativity,('Auu____1552,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1563  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___93_1750 =
    match uu___93_1750 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1788  ->
         match uu____1788 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1865 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1865 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1913) ->
          assoc_levels
      | uu____1954 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1992 .
    ('Auu____1992,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2048 =
        FStar_List.tryFind
          (fun uu____2086  ->
             match uu____2086 with
             | (uu____2103,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____2048 with
      | FStar_Pervasives_Native.Some ((uu____2141,l1,uu____2143),uu____2144)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2195 =
            let uu____2196 =
              let uu____2197 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2197 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2196 in
          failwith uu____2195 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2231 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2231) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2244  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2319 =
      let uu____2332 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2332 (operatorInfix0ad12 ()) in
    uu____2319 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2436 =
      let uu____2449 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2449 opinfix34 in
    uu____2436 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2511 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2511
    then Prims.parse_int "1"
    else
      (let uu____2513 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2513
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2522 . FStar_Ident.ident -> 'Auu____2522 Prims.list -> Prims.bool =
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
      | uu____2535 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2569 .
    ('Auu____2569 -> FStar_Pprint.document) ->
      'Auu____2569 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2601 = FStar_ST.op_Bang comment_stack in
          match uu____2601 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2687 = FStar_Range.range_before_pos crange print_pos in
              if uu____2687
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2751 =
                    let uu____2752 =
                      let uu____2753 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2753
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2752 in
                  comments_before_pos uu____2751 print_pos lookahead_pos))
              else
                (let uu____2755 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2755)) in
        let uu____2756 =
          let uu____2761 =
            let uu____2762 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2762 in
          let uu____2763 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2761 uu____2763 in
        match uu____2756 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2769 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2769
              else comments in
            let uu____2775 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2775
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2792 = FStar_ST.op_Bang comment_stack in
          match uu____2792 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2930 =
                    let uu____2931 =
                      let uu____2932 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2932 in
                    uu____2931 - lbegin in
                  max k uu____2930 in
                let doc2 =
                  let uu____2934 =
                    let uu____2935 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2936 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2935 uu____2936 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2934 in
                let uu____2937 =
                  let uu____2938 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2938 in
                place_comments_until_pos (Prims.parse_int "1") uu____2937
                  pos_end doc2))
          | uu____2939 ->
              let lnum =
                let uu____2947 =
                  let uu____2948 = FStar_Range.line_of_pos pos_end in
                  uu____2948 - lbegin in
                max (Prims.parse_int "1") uu____2947 in
              let uu____2949 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2949
let separate_map_with_comments:
  'Auu____2962 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2962 -> FStar_Pprint.document) ->
          'Auu____2962 Prims.list ->
            ('Auu____2962 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3010 x =
              match uu____3010 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____3024 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3024 doc1 in
                  let uu____3025 =
                    let uu____3026 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____3026 in
                  let uu____3027 =
                    let uu____3028 =
                      let uu____3029 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____3029 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3028 in
                  (uu____3025, uu____3027) in
            let uu____3030 =
              let uu____3037 = FStar_List.hd xs in
              let uu____3038 = FStar_List.tl xs in (uu____3037, uu____3038) in
            match uu____3030 with
            | (x,xs1) ->
                let init1 =
                  let uu____3054 =
                    let uu____3055 =
                      let uu____3056 = extract_range x in
                      FStar_Range.end_of_range uu____3056 in
                    FStar_Range.line_of_pos uu____3055 in
                  let uu____3057 =
                    let uu____3058 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3058 in
                  (uu____3054, uu____3057) in
                let uu____3059 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____3059
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3354 =
      let uu____3355 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3356 =
        let uu____3357 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3358 =
          let uu____3359 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3360 =
            let uu____3361 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3361 in
          FStar_Pprint.op_Hat_Hat uu____3359 uu____3360 in
        FStar_Pprint.op_Hat_Hat uu____3357 uu____3358 in
      FStar_Pprint.op_Hat_Hat uu____3355 uu____3356 in
    FStar_Pprint.group uu____3354
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3364 =
      let uu____3365 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3365 in
    let uu____3366 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3364 FStar_Pprint.space uu____3366
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3367  ->
    match uu____3367 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3401 =
                match uu____3401 with
                | (kwd,arg) ->
                    let uu____3408 = str "@" in
                    let uu____3409 =
                      let uu____3410 = str kwd in
                      let uu____3411 =
                        let uu____3412 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3412 in
                      FStar_Pprint.op_Hat_Hat uu____3410 uu____3411 in
                    FStar_Pprint.op_Hat_Hat uu____3408 uu____3409 in
              let uu____3413 =
                let uu____3414 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3414 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3413 in
        let uu____3419 =
          let uu____3420 =
            let uu____3421 =
              let uu____3422 =
                let uu____3423 = str doc1 in
                let uu____3424 =
                  let uu____3425 =
                    let uu____3426 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3426 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3425 in
                FStar_Pprint.op_Hat_Hat uu____3423 uu____3424 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3422 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3421 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3420 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3419
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3430 =
          let uu____3431 = str "val" in
          let uu____3432 =
            let uu____3433 =
              let uu____3434 = p_lident lid in
              let uu____3435 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3434 uu____3435 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3433 in
          FStar_Pprint.op_Hat_Hat uu____3431 uu____3432 in
        let uu____3436 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3430 uu____3436
    | FStar_Parser_AST.TopLevelLet (uu____3437,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3462 =
               let uu____3463 = str "let" in
               let uu____3464 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3463 uu____3464 in
             FStar_Pprint.group uu____3462) lbs
    | uu____3465 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3468 =
          let uu____3469 = str "open" in
          let uu____3470 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3469 uu____3470 in
        FStar_Pprint.group uu____3468
    | FStar_Parser_AST.Include uid ->
        let uu____3472 =
          let uu____3473 = str "include" in
          let uu____3474 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3473 uu____3474 in
        FStar_Pprint.group uu____3472
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3477 =
          let uu____3478 = str "module" in
          let uu____3479 =
            let uu____3480 =
              let uu____3481 = p_uident uid1 in
              let uu____3482 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3481 uu____3482 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3480 in
          FStar_Pprint.op_Hat_Hat uu____3478 uu____3479 in
        let uu____3483 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3477 uu____3483
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3485 =
          let uu____3486 = str "module" in
          let uu____3487 =
            let uu____3488 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3488 in
          FStar_Pprint.op_Hat_Hat uu____3486 uu____3487 in
        FStar_Pprint.group uu____3485
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3521 = str "effect" in
          let uu____3522 =
            let uu____3523 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3523 in
          FStar_Pprint.op_Hat_Hat uu____3521 uu____3522 in
        let uu____3524 =
          let uu____3525 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3525 FStar_Pprint.equals in
        let uu____3526 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3524 uu____3526
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3544 = str "type" in
        let uu____3545 = str "and" in
        precede_break_separate_map uu____3544 uu____3545 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3567 = str "let" in
          let uu____3568 =
            let uu____3569 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3569 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3567 uu____3568 in
        let uu____3570 =
          let uu____3571 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3571 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3570 p_letbinding lbs
          (fun uu____3579  ->
             match uu____3579 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3588 =
          let uu____3589 = str "val" in
          let uu____3590 =
            let uu____3591 =
              let uu____3592 = p_lident lid in
              let uu____3593 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3592 uu____3593 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3591 in
          FStar_Pprint.op_Hat_Hat uu____3589 uu____3590 in
        let uu____3594 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3588 uu____3594
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3598 =
            let uu____3599 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3599 FStar_Util.is_upper in
          if uu____3598
          then FStar_Pprint.empty
          else
            (let uu____3607 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3607 FStar_Pprint.space) in
        let uu____3608 =
          let uu____3609 =
            let uu____3610 = p_ident id1 in
            let uu____3611 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3610 uu____3611 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3609 in
        let uu____3612 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3608 uu____3612
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3619 = str "exception" in
        let uu____3620 =
          let uu____3621 =
            let uu____3622 = p_uident uid in
            let uu____3623 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3628 = str "of" in
                   let uu____3629 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3628 uu____3629) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3622 uu____3623 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3621 in
        FStar_Pprint.op_Hat_Hat uu____3619 uu____3620
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3631 = str "new_effect" in
        let uu____3632 =
          let uu____3633 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3633 in
        FStar_Pprint.op_Hat_Hat uu____3631 uu____3632
    | FStar_Parser_AST.SubEffect se ->
        let uu____3635 = str "sub_effect" in
        let uu____3636 =
          let uu____3637 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3637 in
        FStar_Pprint.op_Hat_Hat uu____3635 uu____3636
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3640 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3640 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3641 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3642) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___94_3659  ->
    match uu___94_3659 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3661 = str "#set-options" in
        let uu____3662 =
          let uu____3663 =
            let uu____3664 = str s in FStar_Pprint.dquotes uu____3664 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3663 in
        FStar_Pprint.op_Hat_Hat uu____3661 uu____3662
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3668 = str "#reset-options" in
        let uu____3669 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3673 =
                 let uu____3674 = str s in FStar_Pprint.dquotes uu____3674 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3673) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3668 uu____3669
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
  fun uu____3725  ->
    match uu____3725 with
    | (typedecl,fsdoc_opt) ->
        let uu____3738 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3739 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3738 uu____3739
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___95_3740  ->
    match uu___95_3740 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3755 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3771 =
          let uu____3772 = p_typ t in prefix2 FStar_Pprint.equals uu____3772 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3816 =
          match uu____3816 with
          | (lid1,t,doc_opt) ->
              let uu____3832 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3832 in
        let p_fields uu____3846 =
          let uu____3847 =
            let uu____3848 =
              let uu____3849 =
                let uu____3850 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3850 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3849 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3848 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3847 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3914 =
          match uu____3914 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3940 =
                  let uu____3941 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3941 in
                FStar_Range.extend_to_end_of_line uu____3940 in
              let p_constructorBranch decl =
                let uu____3974 =
                  let uu____3975 =
                    let uu____3976 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3976 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3975 in
                FStar_Pprint.group uu____3974 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____3996 =
          let uu____3997 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____3997 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4012  ->
             let uu____4013 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____4013)
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
            let uu____4028 = p_ident lid in
            let uu____4029 =
              let uu____4030 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4030 in
            FStar_Pprint.op_Hat_Hat uu____4028 uu____4029
          else
            (let binders_doc =
               let uu____4033 = p_typars bs in
               let uu____4034 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4038 =
                        let uu____4039 =
                          let uu____4040 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4040 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4039 in
                      FStar_Pprint.op_Hat_Hat break1 uu____4038) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____4033 uu____4034 in
             let uu____4041 = p_ident lid in
             let uu____4042 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4041 binders_doc uu____4042)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4043  ->
    match uu____4043 with
    | (lid,t,doc_opt) ->
        let uu____4059 =
          let uu____4060 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____4061 =
            let uu____4062 = p_lident lid in
            let uu____4063 =
              let uu____4064 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4064 in
            FStar_Pprint.op_Hat_Hat uu____4062 uu____4063 in
          FStar_Pprint.op_Hat_Hat uu____4060 uu____4061 in
        FStar_Pprint.group uu____4059
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____4065  ->
    match uu____4065 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____4093 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____4094 =
          let uu____4095 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____4096 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4101 =
                   let uu____4102 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4102 in
                 let uu____4103 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____4101 uu____4103) t_opt in
          FStar_Pprint.op_Hat_Hat uu____4095 uu____4096 in
        FStar_Pprint.op_Hat_Hat uu____4093 uu____4094
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4104  ->
    match uu____4104 with
    | (pat,uu____4110) ->
        let uu____4111 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4122 =
                let uu____4123 =
                  let uu____4124 =
                    let uu____4125 =
                      let uu____4126 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4126 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4125 in
                  FStar_Pprint.group uu____4124 in
                FStar_Pprint.op_Hat_Hat break1 uu____4123 in
              (pat1, uu____4122)
          | uu____4127 -> (pat, FStar_Pprint.empty) in
        (match uu____4111 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4131);
                     FStar_Parser_AST.prange = uu____4132;_},pats)
                  ->
                  let uu____4142 =
                    let uu____4143 = p_lident x in
                    let uu____4144 =
                      let uu____4145 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____4145 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4143 uu____4144 in
                  FStar_Pprint.group uu____4142
              | uu____4146 ->
                  let uu____4147 =
                    let uu____4148 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____4148 ascr_doc in
                  FStar_Pprint.group uu____4147))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4149  ->
    match uu____4149 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____4157 =
          let uu____4158 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____4158 in
        let uu____4159 = p_term e in prefix2 uu____4157 uu____4159
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___96_4160  ->
    match uu___96_4160 with
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
        let uu____4185 = p_uident uid in
        let uu____4186 = p_binders true bs in
        let uu____4187 =
          let uu____4188 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____4188 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4185 uu____4186 uu____4187
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
          let uu____4197 =
            let uu____4198 =
              let uu____4199 =
                let uu____4200 = p_uident uid in
                let uu____4201 = p_binders true bs in
                let uu____4202 =
                  let uu____4203 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____4203 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4200 uu____4201 uu____4202 in
              FStar_Pprint.group uu____4199 in
            let uu____4204 =
              let uu____4205 = str "with" in
              let uu____4206 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____4205 uu____4206 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4198 uu____4204 in
          braces_with_nesting uu____4197
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4236 =
          let uu____4237 = p_lident lid in
          let uu____4238 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____4237 uu____4238 in
        let uu____4239 = p_simpleTerm e in prefix2 uu____4236 uu____4239
    | uu____4240 ->
        let uu____4241 =
          let uu____4242 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4242 in
        failwith uu____4241
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4297 =
        match uu____4297 with
        | (kwd,t) ->
            let uu____4304 =
              let uu____4305 = str kwd in
              let uu____4306 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4305 uu____4306 in
            let uu____4307 = p_simpleTerm t in prefix2 uu____4304 uu____4307 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4312 =
      let uu____4313 =
        let uu____4314 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4315 =
          let uu____4316 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4316 in
        FStar_Pprint.op_Hat_Hat uu____4314 uu____4315 in
      let uu____4317 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4313 uu____4317 in
    let uu____4318 =
      let uu____4319 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4319 in
    FStar_Pprint.op_Hat_Hat uu____4312 uu____4318
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___97_4320  ->
    match uu___97_4320 with
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
    let uu____4322 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4322
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___98_4323  ->
    match uu___98_4323 with
    | FStar_Parser_AST.Rec  ->
        let uu____4324 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4324
    | FStar_Parser_AST.Mutable  ->
        let uu____4325 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4325
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___99_4326  ->
    match uu___99_4326 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4331 =
          let uu____4332 =
            let uu____4333 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4333 in
          FStar_Pprint.separate_map uu____4332 p_tuplePattern pats in
        FStar_Pprint.group uu____4331
    | uu____4334 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4341 =
          let uu____4342 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4342 p_constructorPattern pats in
        FStar_Pprint.group uu____4341
    | uu____4343 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4346;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4351 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4352 = p_constructorPattern hd1 in
        let uu____4353 = p_constructorPattern tl1 in
        infix0 uu____4351 uu____4352 uu____4353
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4355;_},pats)
        ->
        let uu____4361 = p_quident uid in
        let uu____4362 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4361 uu____4362
    | uu____4363 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4367 =
          let uu____4372 =
            let uu____4373 = unparen t in uu____4373.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4372) in
        (match uu____4367 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4378;
               FStar_Parser_AST.blevel = uu____4379;
               FStar_Parser_AST.aqual = uu____4380;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4386 =
               let uu____4387 = p_ident lid in
               p_refinement aqual uu____4387 t1 phi in
             soft_parens_with_nesting uu____4386
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4389;
               FStar_Parser_AST.blevel = uu____4390;
               FStar_Parser_AST.aqual = uu____4391;_},phi))
             ->
             let uu____4393 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4393
         | uu____4394 ->
             let uu____4399 =
               let uu____4400 = p_tuplePattern pat in
               let uu____4401 =
                 let uu____4402 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4403 =
                   let uu____4404 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4404 in
                 FStar_Pprint.op_Hat_Hat uu____4402 uu____4403 in
               FStar_Pprint.op_Hat_Hat uu____4400 uu____4401 in
             soft_parens_with_nesting uu____4399)
    | FStar_Parser_AST.PatList pats ->
        let uu____4408 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4408 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4423 =
          match uu____4423 with
          | (lid,pat) ->
              let uu____4430 = p_qlident lid in
              let uu____4431 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4430 uu____4431 in
        let uu____4432 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4432
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4442 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4443 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4444 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4442 uu____4443 uu____4444
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4455 =
          let uu____4456 =
            let uu____4457 = str (FStar_Ident.text_of_id op) in
            let uu____4458 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4457 uu____4458 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4456 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4455
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4466 = FStar_Pprint.optional p_aqual aqual in
        let uu____4467 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4466 uu____4467
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4469 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4472;
           FStar_Parser_AST.prange = uu____4473;_},uu____4474)
        ->
        let uu____4479 = p_tuplePattern p in
        soft_parens_with_nesting uu____4479
    | FStar_Parser_AST.PatTuple (uu____4480,false ) ->
        let uu____4485 = p_tuplePattern p in
        soft_parens_with_nesting uu____4485
    | uu____4486 ->
        let uu____4487 =
          let uu____4488 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4488 in
        failwith uu____4487
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4492 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4493 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4492 uu____4493
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4498 =
              let uu____4499 = unparen t in uu____4499.FStar_Parser_AST.tm in
            match uu____4498 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4502;
                   FStar_Parser_AST.blevel = uu____4503;
                   FStar_Parser_AST.aqual = uu____4504;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4506 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4506 t1 phi
            | uu____4507 ->
                let uu____4508 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4509 =
                  let uu____4510 = p_lident lid in
                  let uu____4511 =
                    let uu____4512 =
                      let uu____4513 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4514 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4513 uu____4514 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4512 in
                  FStar_Pprint.op_Hat_Hat uu____4510 uu____4511 in
                FStar_Pprint.op_Hat_Hat uu____4508 uu____4509 in
          if is_atomic
          then
            let uu____4515 =
              let uu____4516 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4516 in
            FStar_Pprint.group uu____4515
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4518 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4524 =
            let uu____4525 = unparen t in uu____4525.FStar_Parser_AST.tm in
          (match uu____4524 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4527;
                  FStar_Parser_AST.blevel = uu____4528;
                  FStar_Parser_AST.aqual = uu____4529;_},phi)
               ->
               if is_atomic
               then
                 let uu____4531 =
                   let uu____4532 =
                     let uu____4533 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4533 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4532 in
                 FStar_Pprint.group uu____4531
               else
                 (let uu____4535 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4535)
           | uu____4536 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4544 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4545 =
            let uu____4546 =
              let uu____4547 =
                let uu____4548 = p_appTerm t in
                let uu____4549 =
                  let uu____4550 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4550 in
                FStar_Pprint.op_Hat_Hat uu____4548 uu____4549 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4547 in
            FStar_Pprint.op_Hat_Hat binder uu____4546 in
          FStar_Pprint.op_Hat_Hat uu____4544 uu____4545
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
    let uu____4564 =
      let uu____4565 = unparen e in uu____4565.FStar_Parser_AST.tm in
    match uu____4564 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4568 =
          let uu____4569 =
            let uu____4570 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4570 FStar_Pprint.semi in
          FStar_Pprint.group uu____4569 in
        let uu____4571 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4568 uu____4571
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4575 =
          let uu____4576 =
            let uu____4577 =
              let uu____4578 = p_lident x in
              let uu____4579 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4578 uu____4579 in
            let uu____4580 =
              let uu____4581 = p_noSeqTerm e1 in
              let uu____4582 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4581 uu____4582 in
            op_Hat_Slash_Plus_Hat uu____4577 uu____4580 in
          FStar_Pprint.group uu____4576 in
        let uu____4583 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4575 uu____4583
    | uu____4584 ->
        let uu____4585 = p_noSeqTerm e in FStar_Pprint.group uu____4585
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4588 =
      let uu____4589 = unparen e in uu____4589.FStar_Parser_AST.tm in
    match uu____4588 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4594 =
          let uu____4595 = p_tmIff e1 in
          let uu____4596 =
            let uu____4597 =
              let uu____4598 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4598 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4597 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4595 uu____4596 in
        FStar_Pprint.group uu____4594
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4604 =
          let uu____4605 = p_tmIff e1 in
          let uu____4606 =
            let uu____4607 =
              let uu____4608 =
                let uu____4609 = p_typ t in
                let uu____4610 =
                  let uu____4611 = str "by" in
                  let uu____4612 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4611 uu____4612 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4609 uu____4610 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4608 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4607 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4605 uu____4606 in
        FStar_Pprint.group uu____4604
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4613;_},e1::e2::e3::[])
        ->
        let uu____4619 =
          let uu____4620 =
            let uu____4621 =
              let uu____4622 = p_atomicTermNotQUident e1 in
              let uu____4623 =
                let uu____4624 =
                  let uu____4625 =
                    let uu____4626 = p_term e2 in
                    soft_parens_with_nesting uu____4626 in
                  let uu____4627 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4625 uu____4627 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4624 in
              FStar_Pprint.op_Hat_Hat uu____4622 uu____4623 in
            FStar_Pprint.group uu____4621 in
          let uu____4628 =
            let uu____4629 = p_noSeqTerm e3 in jump2 uu____4629 in
          FStar_Pprint.op_Hat_Hat uu____4620 uu____4628 in
        FStar_Pprint.group uu____4619
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4630;_},e1::e2::e3::[])
        ->
        let uu____4636 =
          let uu____4637 =
            let uu____4638 =
              let uu____4639 = p_atomicTermNotQUident e1 in
              let uu____4640 =
                let uu____4641 =
                  let uu____4642 =
                    let uu____4643 = p_term e2 in
                    soft_brackets_with_nesting uu____4643 in
                  let uu____4644 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4642 uu____4644 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4641 in
              FStar_Pprint.op_Hat_Hat uu____4639 uu____4640 in
            FStar_Pprint.group uu____4638 in
          let uu____4645 =
            let uu____4646 = p_noSeqTerm e3 in jump2 uu____4646 in
          FStar_Pprint.op_Hat_Hat uu____4637 uu____4645 in
        FStar_Pprint.group uu____4636
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4656 =
          let uu____4657 = str "requires" in
          let uu____4658 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4657 uu____4658 in
        FStar_Pprint.group uu____4656
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4668 =
          let uu____4669 = str "ensures" in
          let uu____4670 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4669 uu____4670 in
        FStar_Pprint.group uu____4668
    | FStar_Parser_AST.Attributes es ->
        let uu____4674 =
          let uu____4675 = str "attributes" in
          let uu____4676 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4675 uu____4676 in
        FStar_Pprint.group uu____4674
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4680 = is_unit e3 in
        if uu____4680
        then
          let uu____4681 =
            let uu____4682 =
              let uu____4683 = str "if" in
              let uu____4684 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4683 uu____4684 in
            let uu____4685 =
              let uu____4686 = str "then" in
              let uu____4687 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4686 uu____4687 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4682 uu____4685 in
          FStar_Pprint.group uu____4681
        else
          (let e2_doc =
             let uu____4690 =
               let uu____4691 = unparen e2 in uu____4691.FStar_Parser_AST.tm in
             match uu____4690 with
             | FStar_Parser_AST.If (uu____4692,uu____4693,e31) when
                 is_unit e31 ->
                 let uu____4695 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4695
             | uu____4696 -> p_noSeqTerm e2 in
           let uu____4697 =
             let uu____4698 =
               let uu____4699 = str "if" in
               let uu____4700 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4699 uu____4700 in
             let uu____4701 =
               let uu____4702 =
                 let uu____4703 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4703 e2_doc in
               let uu____4704 =
                 let uu____4705 = str "else" in
                 let uu____4706 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4705 uu____4706 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4702 uu____4704 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4698 uu____4701 in
           FStar_Pprint.group uu____4697)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4729 =
          let uu____4730 =
            let uu____4731 = str "try" in
            let uu____4732 = p_noSeqTerm e1 in prefix2 uu____4731 uu____4732 in
          let uu____4733 =
            let uu____4734 = str "with" in
            let uu____4735 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4734 uu____4735 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4730 uu____4733 in
        FStar_Pprint.group uu____4729
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4766 =
          let uu____4767 =
            let uu____4768 = str "match" in
            let uu____4769 = p_noSeqTerm e1 in
            let uu____4770 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4768 uu____4769 uu____4770 in
          let uu____4771 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4767 uu____4771 in
        FStar_Pprint.group uu____4766
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4782 =
          let uu____4783 =
            let uu____4784 = str "let open" in
            let uu____4785 = p_quident uid in
            let uu____4786 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4784 uu____4785 uu____4786 in
          let uu____4787 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4783 uu____4787 in
        FStar_Pprint.group uu____4782
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4804 = str "let" in
          let uu____4805 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4804 uu____4805 in
        let uu____4806 =
          let uu____4807 =
            let uu____4808 =
              let uu____4809 = str "and" in
              precede_break_separate_map let_doc uu____4809 p_letbinding lbs in
            let uu____4814 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4808 uu____4814 in
          FStar_Pprint.group uu____4807 in
        let uu____4815 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4806 uu____4815
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4818;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4821;
                                                         FStar_Parser_AST.level
                                                           = uu____4822;_})
        when matches_var maybe_x x ->
        let uu____4849 =
          let uu____4850 = str "function" in
          let uu____4851 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4850 uu____4851 in
        FStar_Pprint.group uu____4849
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4862 =
          let uu____4863 = p_lident id1 in
          let uu____4864 =
            let uu____4865 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4865 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4863 uu____4864 in
        FStar_Pprint.group uu____4862
    | uu____4866 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4869 =
      let uu____4870 = unparen e in uu____4870.FStar_Parser_AST.tm in
    match uu____4869 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4886 =
          let uu____4887 =
            let uu____4888 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4888 FStar_Pprint.space in
          let uu____4889 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4887 uu____4889 FStar_Pprint.dot in
        let uu____4890 =
          let uu____4891 = p_trigger trigger in
          let uu____4892 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4891 uu____4892 in
        prefix2 uu____4886 uu____4890
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4908 =
          let uu____4909 =
            let uu____4910 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4910 FStar_Pprint.space in
          let uu____4911 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4909 uu____4911 FStar_Pprint.dot in
        let uu____4912 =
          let uu____4913 = p_trigger trigger in
          let uu____4914 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4913 uu____4914 in
        prefix2 uu____4908 uu____4912
    | uu____4915 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4917 =
      let uu____4918 = unparen e in uu____4918.FStar_Parser_AST.tm in
    match uu____4917 with
    | FStar_Parser_AST.QForall uu____4919 -> str "forall"
    | FStar_Parser_AST.QExists uu____4932 -> str "exists"
    | uu____4945 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___100_4946  ->
    match uu___100_4946 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4958 =
          let uu____4959 =
            let uu____4960 = str "pattern" in
            let uu____4961 =
              let uu____4962 =
                let uu____4963 = p_disjunctivePats pats in jump2 uu____4963 in
              let uu____4964 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4962 uu____4964 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4960 uu____4961 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4959 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4958
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4970 = str "\\/" in
    FStar_Pprint.separate_map uu____4970 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4976 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4976
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4978 =
      let uu____4979 = unparen e in uu____4979.FStar_Parser_AST.tm in
    match uu____4978 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4986 =
          let uu____4987 = str "fun" in
          let uu____4988 =
            let uu____4989 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4989 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4987 uu____4988 in
        let uu____4990 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4986 uu____4990
    | uu____4991 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4994  ->
    match uu____4994 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____5013 =
            let uu____5014 = unparen e in uu____5014.FStar_Parser_AST.tm in
          match uu____5013 with
          | FStar_Parser_AST.Match uu____5017 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____5032 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____5048);
                 FStar_Parser_AST.prange = uu____5049;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____5051);
                                                               FStar_Parser_AST.range
                                                                 = uu____5052;
                                                               FStar_Parser_AST.level
                                                                 = uu____5053;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____5080 -> (fun x  -> x) in
        let uu____5082 =
          let uu____5083 =
            let uu____5084 =
              let uu____5085 =
                let uu____5086 =
                  let uu____5087 = p_disjunctivePattern pat in
                  let uu____5088 =
                    let uu____5089 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____5089 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____5087 uu____5088 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5086 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5085 in
            FStar_Pprint.group uu____5084 in
          let uu____5090 =
            let uu____5091 = p_term e in maybe_paren uu____5091 in
          op_Hat_Slash_Plus_Hat uu____5083 uu____5090 in
        FStar_Pprint.group uu____5082
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___101_5092  ->
    match uu___101_5092 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5096 = str "when" in
        let uu____5097 =
          let uu____5098 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____5098 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____5096 uu____5097
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5100 =
      let uu____5101 = unparen e in uu____5101.FStar_Parser_AST.tm in
    match uu____5100 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5102;_},e1::e2::[])
        ->
        let uu____5107 = str "<==>" in
        let uu____5108 = p_tmImplies e1 in
        let uu____5109 = p_tmIff e2 in
        infix0 uu____5107 uu____5108 uu____5109
    | uu____5110 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5112 =
      let uu____5113 = unparen e in uu____5113.FStar_Parser_AST.tm in
    match uu____5112 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5114;_},e1::e2::[])
        ->
        let uu____5119 = str "==>" in
        let uu____5120 = p_tmArrow p_tmFormula e1 in
        let uu____5121 = p_tmImplies e2 in
        infix0 uu____5119 uu____5120 uu____5121
    | uu____5122 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____5127 =
        let uu____5128 = unparen e in uu____5128.FStar_Parser_AST.tm in
      match uu____5127 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5135 =
            let uu____5136 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5141 = p_binder false b in
                   let uu____5142 =
                     let uu____5143 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5143 in
                   FStar_Pprint.op_Hat_Hat uu____5141 uu____5142) bs in
            let uu____5144 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____5136 uu____5144 in
          FStar_Pprint.group uu____5135
      | uu____5145 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5147 =
      let uu____5148 = unparen e in uu____5148.FStar_Parser_AST.tm in
    match uu____5147 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5149;_},e1::e2::[])
        ->
        let uu____5154 = str "\\/" in
        let uu____5155 = p_tmFormula e1 in
        let uu____5156 = p_tmConjunction e2 in
        infix0 uu____5154 uu____5155 uu____5156
    | uu____5157 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5159 =
      let uu____5160 = unparen e in uu____5160.FStar_Parser_AST.tm in
    match uu____5159 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5161;_},e1::e2::[])
        ->
        let uu____5166 = str "/\\" in
        let uu____5167 = p_tmConjunction e1 in
        let uu____5168 = p_tmTuple e2 in
        infix0 uu____5166 uu____5167 uu____5168
    | uu____5169 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5172 =
      let uu____5173 = unparen e in uu____5173.FStar_Parser_AST.tm in
    match uu____5172 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5188 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5188
          (fun uu____5196  ->
             match uu____5196 with | (e1,uu____5202) -> p_tmEq e1) args
    | uu____5203 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5208 =
             let uu____5209 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5209 in
           FStar_Pprint.group uu____5208)
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
      let uu____5254 =
        let uu____5255 = unparen e in uu____5255.FStar_Parser_AST.tm in
      match uu____5254 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5262 = levels op1 in
          (match uu____5262 with
           | (left1,mine,right1) ->
               let uu____5272 =
                 let uu____5273 = FStar_All.pipe_left str op1 in
                 let uu____5274 = p_tmEq' left1 e1 in
                 let uu____5275 = p_tmEq' right1 e2 in
                 infix0 uu____5273 uu____5274 uu____5275 in
               paren_if curr mine uu____5272)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5276;_},e1::e2::[])
          ->
          let uu____5281 =
            let uu____5282 = p_tmEq e1 in
            let uu____5283 =
              let uu____5284 =
                let uu____5285 =
                  let uu____5286 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5286 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5285 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5284 in
            FStar_Pprint.op_Hat_Hat uu____5282 uu____5283 in
          FStar_Pprint.group uu____5281
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5287;_},e1::[])
          ->
          let uu____5291 = levels "-" in
          (match uu____5291 with
           | (left1,mine,right1) ->
               let uu____5301 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5301)
      | uu____5302 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5357 =
        let uu____5358 = unparen e in uu____5358.FStar_Parser_AST.tm in
      match uu____5357 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5361)::(e2,uu____5363)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5383 = is_list e in Prims.op_Negation uu____5383)
          ->
          let op = "::" in
          let uu____5385 = levels op in
          (match uu____5385 with
           | (left1,mine,right1) ->
               let uu____5395 =
                 let uu____5396 = str op in
                 let uu____5397 = p_tmNoEq' left1 e1 in
                 let uu____5398 = p_tmNoEq' right1 e2 in
                 infix0 uu____5396 uu____5397 uu____5398 in
               paren_if curr mine uu____5395)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5406 = levels op in
          (match uu____5406 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5420 = p_binder false b in
                 let uu____5421 =
                   let uu____5422 =
                     let uu____5423 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5423 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5422 in
                 FStar_Pprint.op_Hat_Hat uu____5420 uu____5421 in
               let uu____5424 =
                 let uu____5425 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5426 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5425 uu____5426 in
               paren_if curr mine uu____5424)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5433 = levels op1 in
          (match uu____5433 with
           | (left1,mine,right1) ->
               let uu____5443 =
                 let uu____5444 = str op1 in
                 let uu____5445 = p_tmNoEq' left1 e1 in
                 let uu____5446 = p_tmNoEq' right1 e2 in
                 infix0 uu____5444 uu____5445 uu____5446 in
               paren_if curr mine uu____5443)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5449 =
            let uu____5450 = p_lidentOrUnderscore lid in
            let uu____5451 =
              let uu____5452 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5452 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5450 uu____5451 in
          FStar_Pprint.group uu____5449
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5473 =
            let uu____5474 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5475 =
              let uu____5476 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5476 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5474 uu____5475 in
          braces_with_nesting uu____5473
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5481;_},e1::[])
          ->
          let uu____5485 =
            let uu____5486 = str "~" in
            let uu____5487 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5486 uu____5487 in
          FStar_Pprint.group uu____5485
      | uu____5488 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5490 = p_appTerm e in
    let uu____5491 =
      let uu____5492 =
        let uu____5493 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5493 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5492 in
    FStar_Pprint.op_Hat_Hat uu____5490 uu____5491
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5498 =
            let uu____5499 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5499 t phi in
          soft_parens_with_nesting uu____5498
      | FStar_Parser_AST.TAnnotated uu____5500 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5505 ->
          let uu____5506 =
            let uu____5507 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5507 in
          failwith uu____5506
      | FStar_Parser_AST.TVariable uu____5508 ->
          let uu____5509 =
            let uu____5510 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5510 in
          failwith uu____5509
      | FStar_Parser_AST.NoName uu____5511 ->
          let uu____5512 =
            let uu____5513 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5513 in
          failwith uu____5512
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5514  ->
    match uu____5514 with
    | (lid,e) ->
        let uu____5521 =
          let uu____5522 = p_qlident lid in
          let uu____5523 =
            let uu____5524 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5524 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5522 uu____5523 in
        FStar_Pprint.group uu____5521
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5526 =
      let uu____5527 = unparen e in uu____5527.FStar_Parser_AST.tm in
    match uu____5526 with
    | FStar_Parser_AST.App uu____5528 when is_general_application e ->
        let uu____5535 = head_and_args e in
        (match uu____5535 with
         | (head1,args) ->
             let uu____5560 =
               let uu____5571 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5571
               then
                 let uu____5628 =
                   FStar_Util.take
                     (fun uu____5652  ->
                        match uu____5652 with
                        | (uu____5657,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5628 with
                 | (fs_typ_args,args1) ->
                     let uu____5695 =
                       let uu____5696 = p_indexingTerm head1 in
                       let uu____5697 =
                         let uu____5698 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5698 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5696 uu____5697 in
                     (uu____5695, args1)
               else
                 (let uu____5710 = p_indexingTerm head1 in (uu____5710, args)) in
             (match uu____5560 with
              | (head_doc,args1) ->
                  let uu____5731 =
                    let uu____5732 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5732 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5731))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5752 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5752)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5770 =
               let uu____5771 = p_quident lid in
               let uu____5772 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5771 uu____5772 in
             FStar_Pprint.group uu____5770
         | hd1::tl1 ->
             let uu____5789 =
               let uu____5790 =
                 let uu____5791 =
                   let uu____5792 = p_quident lid in
                   let uu____5793 = p_argTerm hd1 in
                   prefix2 uu____5792 uu____5793 in
                 FStar_Pprint.group uu____5791 in
               let uu____5794 =
                 let uu____5795 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5795 in
               FStar_Pprint.op_Hat_Hat uu____5790 uu____5794 in
             FStar_Pprint.group uu____5789)
    | uu____5800 -> p_indexingTerm e
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
         (let uu____5809 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5809 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5811 = str "#" in
        let uu____5812 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5811 uu____5812
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5814  ->
    match uu____5814 with | (e,uu____5820) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5825 =
        let uu____5826 = unparen e in uu____5826.FStar_Parser_AST.tm in
      match uu____5825 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5827;_},e1::e2::[])
          ->
          let uu____5832 =
            let uu____5833 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5834 =
              let uu____5835 =
                let uu____5836 = p_term e2 in
                soft_parens_with_nesting uu____5836 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5835 in
            FStar_Pprint.op_Hat_Hat uu____5833 uu____5834 in
          FStar_Pprint.group uu____5832
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5837;_},e1::e2::[])
          ->
          let uu____5842 =
            let uu____5843 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5844 =
              let uu____5845 =
                let uu____5846 = p_term e2 in
                soft_brackets_with_nesting uu____5846 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5845 in
            FStar_Pprint.op_Hat_Hat uu____5843 uu____5844 in
          FStar_Pprint.group uu____5842
      | uu____5847 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5850 =
      let uu____5851 = unparen e in uu____5851.FStar_Parser_AST.tm in
    match uu____5850 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5854 = p_quident lid in
        let uu____5855 =
          let uu____5856 =
            let uu____5857 = p_term e1 in soft_parens_with_nesting uu____5857 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5856 in
        FStar_Pprint.op_Hat_Hat uu____5854 uu____5855
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5863 = str (FStar_Ident.text_of_id op) in
        let uu____5864 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5863 uu____5864
    | uu____5865 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5867 =
      let uu____5868 = unparen e in uu____5868.FStar_Parser_AST.tm in
    match uu____5867 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5879 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5886 = str (FStar_Ident.text_of_id op) in
        let uu____5887 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5886 uu____5887
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5891 =
          let uu____5892 =
            let uu____5893 = str (FStar_Ident.text_of_id op) in
            let uu____5894 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5893 uu____5894 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5892 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5891
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5909 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5910 =
          let uu____5911 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5912 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5911 p_tmEq uu____5912 in
        let uu____5919 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5909 uu____5910 uu____5919
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5922 =
          let uu____5923 = p_atomicTermNotQUident e1 in
          let uu____5924 =
            let uu____5925 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5925 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5923 uu____5924 in
        FStar_Pprint.group uu____5922
    | uu____5926 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5928 =
      let uu____5929 = unparen e in uu____5929.FStar_Parser_AST.tm in
    match uu____5928 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5933 = p_quident constr_lid in
        let uu____5934 =
          let uu____5935 =
            let uu____5936 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5936 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5935 in
        FStar_Pprint.op_Hat_Hat uu____5933 uu____5934
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5938 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5938 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5940 = p_term e1 in soft_parens_with_nesting uu____5940
    | uu____5941 when is_array e ->
        let es = extract_from_list e in
        let uu____5945 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5946 =
          let uu____5947 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5947 p_noSeqTerm es in
        let uu____5948 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5945 uu____5946 uu____5948
    | uu____5949 when is_list e ->
        let uu____5950 =
          let uu____5951 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5952 = extract_from_list e in
          separate_map_or_flow uu____5951 p_noSeqTerm uu____5952 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5950 FStar_Pprint.rbracket
    | uu____5955 when is_lex_list e ->
        let uu____5956 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5957 =
          let uu____5958 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5959 = extract_from_list e in
          separate_map_or_flow uu____5958 p_noSeqTerm uu____5959 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5956 uu____5957 FStar_Pprint.rbracket
    | uu____5962 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5966 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5967 =
          let uu____5968 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5968 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5966 uu____5967 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5972 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5973 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5972 uu____5973
    | FStar_Parser_AST.Op (op,args) when
        let uu____5980 = handleable_op op args in
        Prims.op_Negation uu____5980 ->
        let uu____5981 =
          let uu____5982 =
            let uu____5983 =
              let uu____5984 =
                let uu____5985 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____5985
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____5984 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5983 in
          Prims.strcat "Operation " uu____5982 in
        failwith uu____5981
    | FStar_Parser_AST.Uvar uu____5986 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5987 = p_term e in soft_parens_with_nesting uu____5987
    | FStar_Parser_AST.Const uu____5988 ->
        let uu____5989 = p_term e in soft_parens_with_nesting uu____5989
    | FStar_Parser_AST.Op uu____5990 ->
        let uu____5997 = p_term e in soft_parens_with_nesting uu____5997
    | FStar_Parser_AST.Tvar uu____5998 ->
        let uu____5999 = p_term e in soft_parens_with_nesting uu____5999
    | FStar_Parser_AST.Var uu____6000 ->
        let uu____6001 = p_term e in soft_parens_with_nesting uu____6001
    | FStar_Parser_AST.Name uu____6002 ->
        let uu____6003 = p_term e in soft_parens_with_nesting uu____6003
    | FStar_Parser_AST.Construct uu____6004 ->
        let uu____6015 = p_term e in soft_parens_with_nesting uu____6015
    | FStar_Parser_AST.Abs uu____6016 ->
        let uu____6023 = p_term e in soft_parens_with_nesting uu____6023
    | FStar_Parser_AST.App uu____6024 ->
        let uu____6031 = p_term e in soft_parens_with_nesting uu____6031
    | FStar_Parser_AST.Let uu____6032 ->
        let uu____6045 = p_term e in soft_parens_with_nesting uu____6045
    | FStar_Parser_AST.LetOpen uu____6046 ->
        let uu____6051 = p_term e in soft_parens_with_nesting uu____6051
    | FStar_Parser_AST.Seq uu____6052 ->
        let uu____6057 = p_term e in soft_parens_with_nesting uu____6057
    | FStar_Parser_AST.Bind uu____6058 ->
        let uu____6065 = p_term e in soft_parens_with_nesting uu____6065
    | FStar_Parser_AST.If uu____6066 ->
        let uu____6073 = p_term e in soft_parens_with_nesting uu____6073
    | FStar_Parser_AST.Match uu____6074 ->
        let uu____6089 = p_term e in soft_parens_with_nesting uu____6089
    | FStar_Parser_AST.TryWith uu____6090 ->
        let uu____6105 = p_term e in soft_parens_with_nesting uu____6105
    | FStar_Parser_AST.Ascribed uu____6106 ->
        let uu____6115 = p_term e in soft_parens_with_nesting uu____6115
    | FStar_Parser_AST.Record uu____6116 ->
        let uu____6129 = p_term e in soft_parens_with_nesting uu____6129
    | FStar_Parser_AST.Project uu____6130 ->
        let uu____6135 = p_term e in soft_parens_with_nesting uu____6135
    | FStar_Parser_AST.Product uu____6136 ->
        let uu____6143 = p_term e in soft_parens_with_nesting uu____6143
    | FStar_Parser_AST.Sum uu____6144 ->
        let uu____6151 = p_term e in soft_parens_with_nesting uu____6151
    | FStar_Parser_AST.QForall uu____6152 ->
        let uu____6165 = p_term e in soft_parens_with_nesting uu____6165
    | FStar_Parser_AST.QExists uu____6166 ->
        let uu____6179 = p_term e in soft_parens_with_nesting uu____6179
    | FStar_Parser_AST.Refine uu____6180 ->
        let uu____6185 = p_term e in soft_parens_with_nesting uu____6185
    | FStar_Parser_AST.NamedTyp uu____6186 ->
        let uu____6191 = p_term e in soft_parens_with_nesting uu____6191
    | FStar_Parser_AST.Requires uu____6192 ->
        let uu____6199 = p_term e in soft_parens_with_nesting uu____6199
    | FStar_Parser_AST.Ensures uu____6200 ->
        let uu____6207 = p_term e in soft_parens_with_nesting uu____6207
    | FStar_Parser_AST.Assign uu____6208 ->
        let uu____6213 = p_term e in soft_parens_with_nesting uu____6213
    | FStar_Parser_AST.Attributes uu____6214 ->
        let uu____6217 = p_term e in soft_parens_with_nesting uu____6217
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___104_6218  ->
    match uu___104_6218 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6222 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6222
    | FStar_Const.Const_string (s,uu____6233) ->
        let uu____6234 = str s in FStar_Pprint.dquotes uu____6234
    | FStar_Const.Const_bytearray (bytes,uu____6236) ->
        let uu____6241 =
          let uu____6242 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6242 in
        let uu____6243 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6241 uu____6243
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___102_6261 =
          match uu___102_6261 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___103_6265 =
          match uu___103_6265 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6276  ->
               match uu____6276 with
               | (s,w) ->
                   let uu____6283 = signedness s in
                   let uu____6284 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6283 uu____6284)
            sign_width_opt in
        let uu____6285 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6285 ending
    | FStar_Const.Const_range r ->
        let uu____6287 = FStar_Range.string_of_range r in str uu____6287
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6289 = p_quident lid in
        let uu____6290 =
          let uu____6291 =
            let uu____6292 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6292 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6291 in
        FStar_Pprint.op_Hat_Hat uu____6289 uu____6290
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6294 = str "u#" in
    let uu____6295 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6294 uu____6295
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6297 =
      let uu____6298 = unparen u in uu____6298.FStar_Parser_AST.tm in
    match uu____6297 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6299;_},u1::u2::[])
        ->
        let uu____6304 =
          let uu____6305 = p_universeFrom u1 in
          let uu____6306 =
            let uu____6307 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6307 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6305 uu____6306 in
        FStar_Pprint.group uu____6304
    | FStar_Parser_AST.App uu____6308 ->
        let uu____6315 = head_and_args u in
        (match uu____6315 with
         | (head1,args) ->
             let uu____6340 =
               let uu____6341 = unparen head1 in
               uu____6341.FStar_Parser_AST.tm in
             (match uu____6340 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6343 =
                    let uu____6344 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6345 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6353  ->
                           match uu____6353 with
                           | (u1,uu____6359) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6344 uu____6345 in
                  FStar_Pprint.group uu____6343
              | uu____6360 ->
                  let uu____6361 =
                    let uu____6362 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6362 in
                  failwith uu____6361))
    | uu____6363 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6365 =
      let uu____6366 = unparen u in uu____6366.FStar_Parser_AST.tm in
    match uu____6365 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6389 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6389
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6390;_},uu____6391::uu____6392::[])
        ->
        let uu____6395 = p_universeFrom u in
        soft_parens_with_nesting uu____6395
    | FStar_Parser_AST.App uu____6396 ->
        let uu____6403 = p_universeFrom u in
        soft_parens_with_nesting uu____6403
    | uu____6404 ->
        let uu____6405 =
          let uu____6406 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6406 in
        failwith uu____6405
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
       | FStar_Parser_AST.Module (uu____6479,decls) ->
           let uu____6485 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6485
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6494,decls,uu____6496) ->
           let uu____6501 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6501
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6580  ->
         match uu____6580 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6622,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6628,decls,uu____6630) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6702 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6715;
                 FStar_Parser_AST.doc = uu____6716;
                 FStar_Parser_AST.quals = uu____6717;
                 FStar_Parser_AST.attrs = uu____6718;_}::uu____6719 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6725 =
                   let uu____6728 =
                     let uu____6731 = FStar_List.tl ds in d :: uu____6731 in
                   d0 :: uu____6728 in
                 (uu____6725, (d0.FStar_Parser_AST.drange))
             | uu____6736 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6702 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6821 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6821 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6998 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____6998, comments1))))))