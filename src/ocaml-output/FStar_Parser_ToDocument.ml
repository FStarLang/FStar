
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
    let uu____202 =
      let uu____203 = FStar_ST.op_Bang should_unparen in
      Prims.op_Negation uu____203 in
    if uu____202
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____254 -> t)
let str: Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s
let default_or_map:
  'Auu____263 'Auu____264 .
    'Auu____264 ->
      ('Auu____263 -> 'Auu____264) ->
        'Auu____263 FStar_Pervasives_Native.option -> 'Auu____264
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
  'Auu____318 .
    FStar_Pprint.document ->
      ('Auu____318 -> FStar_Pprint.document) ->
        'Auu____318 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____340 =
          let uu____341 =
            let uu____342 = FStar_Pprint.op_Hat_Hat sep break1 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____342 in
          FStar_Pprint.separate_map uu____341 f l in
        FStar_Pprint.group uu____340
let precede_break_separate_map:
  'Auu____348 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____348 -> FStar_Pprint.document) ->
          'Auu____348 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____374 =
            let uu____375 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space in
            let uu____376 =
              let uu____377 = FStar_List.hd l in
              FStar_All.pipe_right uu____377 f in
            FStar_Pprint.precede uu____375 uu____376 in
          let uu____378 =
            let uu____379 = FStar_List.tl l in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____385 =
                   let uu____386 =
                     let uu____387 = f x in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____387 in
                   FStar_Pprint.op_Hat_Hat sep uu____386 in
                 FStar_Pprint.op_Hat_Hat break1 uu____385) uu____379 in
          FStar_Pprint.op_Hat_Hat uu____374 uu____378
let concat_break_map:
  'Auu____391 .
    ('Auu____391 -> FStar_Pprint.document) ->
      'Auu____391 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____409 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____413 = f x in FStar_Pprint.op_Hat_Hat uu____413 break1)
          l in
      FStar_Pprint.group uu____409
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
    let uu____435 = str "begin" in
    let uu____436 = str "end" in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____435 contents uu____436
let separate_map_or_flow:
  'Auu____441 .
    FStar_Pprint.document ->
      ('Auu____441 -> FStar_Pprint.document) ->
        'Auu____441 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
let soft_surround_separate_map:
  'Auu____473 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____473 -> FStar_Pprint.document) ->
                  'Auu____473 Prims.list -> FStar_Pprint.document
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
                    (let uu____518 = FStar_Pprint.separate_map sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____518
                       closing)
let soft_surround_map_or_flow:
  'Auu____528 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____528 -> FStar_Pprint.document) ->
                  'Auu____528 Prims.list -> FStar_Pprint.document
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
                    (let uu____573 = separate_map_or_flow sep f xs in
                     FStar_Pprint.soft_surround n1 b opening uu____573
                       closing)
let doc_of_fsdoc:
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____586  ->
    match uu____586 with
    | (comment,keywords) ->
        let uu____611 =
          let uu____612 =
            let uu____615 = str comment in
            let uu____616 =
              let uu____619 =
                let uu____622 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____631  ->
                       match uu____631 with
                       | (k,v1) ->
                           let uu____638 =
                             let uu____641 = str k in
                             let uu____642 =
                               let uu____645 =
                                 let uu____648 = str v1 in [uu____648] in
                               FStar_Pprint.rarrow :: uu____645 in
                             uu____641 :: uu____642 in
                           FStar_Pprint.concat uu____638) keywords in
                [uu____622] in
              FStar_Pprint.space :: uu____619 in
            uu____615 :: uu____616 in
          FStar_Pprint.concat uu____612 in
        FStar_Pprint.group uu____611
let is_unit: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____652 =
      let uu____653 = unparen e in uu____653.FStar_Parser_AST.tm in
    match uu____652 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____654 -> false
let matches_var: FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____661 =
        let uu____662 = unparen t in uu____662.FStar_Parser_AST.tm in
      match uu____661 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____664 -> false
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
        let uu____681 =
          let uu____682 = unparen e in uu____682.FStar_Parser_AST.tm in
        match uu____681 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____695::(e2,uu____697)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____720 -> false in
      aux
let is_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid
let is_lex_list: FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
let rec extract_from_list:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____730 =
      let uu____731 = unparen e in uu____731.FStar_Parser_AST.tm in
    match uu____730 with
    | FStar_Parser_AST.Construct (uu____734,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____745,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____766 = extract_from_list e2 in e1 :: uu____766
    | uu____769 ->
        let uu____770 =
          let uu____771 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a list %s" uu____771 in
        failwith uu____770
let is_array: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____777 =
      let uu____778 = unparen e in uu____778.FStar_Parser_AST.tm in
    match uu____777 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____780;
           FStar_Parser_AST.level = uu____781;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____783 -> false
let rec is_ref_set: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____787 =
      let uu____788 = unparen e in uu____788.FStar_Parser_AST.tm in
    match uu____787 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____791;
           FStar_Parser_AST.level = uu____792;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____794;
                                                        FStar_Parser_AST.level
                                                          = uu____795;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____797;
                                                   FStar_Parser_AST.level =
                                                     uu____798;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____800;
                FStar_Parser_AST.level = uu____801;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____803;
           FStar_Parser_AST.level = uu____804;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____806 -> false
let rec extract_from_ref_set:
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____812 =
      let uu____813 = unparen e in uu____813.FStar_Parser_AST.tm in
    match uu____812 with
    | FStar_Parser_AST.Var uu____816 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____817;
           FStar_Parser_AST.range = uu____818;
           FStar_Parser_AST.level = uu____819;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____820;
                                                        FStar_Parser_AST.range
                                                          = uu____821;
                                                        FStar_Parser_AST.level
                                                          = uu____822;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____824;
                                                   FStar_Parser_AST.level =
                                                     uu____825;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____826;
                FStar_Parser_AST.range = uu____827;
                FStar_Parser_AST.level = uu____828;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____830;
           FStar_Parser_AST.level = uu____831;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____833 = extract_from_ref_set e1 in
        let uu____836 = extract_from_ref_set e2 in
        FStar_List.append uu____833 uu____836
    | uu____839 ->
        let uu____840 =
          let uu____841 = FStar_Parser_AST.term_to_string e in
          FStar_Util.format1 "Not a ref set %s" uu____841 in
        failwith uu____840
let is_general_application: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____847 = (is_array e) || (is_ref_set e) in
    Prims.op_Negation uu____847
let is_general_construction: FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____851 = (is_list e) || (is_lex_list e) in
    Prims.op_Negation uu____851
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
      let uu____901 =
        let uu____902 = unparen e1 in uu____902.FStar_Parser_AST.tm in
      match uu____901 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____920 -> (e1, acc) in
    aux e []
type associativity =
  | Left
  | Right
  | NonAssoc[@@deriving show]
let uu___is_Left: associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____934 -> false
let uu___is_Right: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____938 -> false
let uu___is_NonAssoc: associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____942 -> false
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string:
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___48_960  ->
    match uu___48_960 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
let matches_token:
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___49_977  ->
      match uu___49_977 with
      | FStar_Util.Inl c ->
          let uu____986 = FStar_String.get s (Prims.parse_int "0") in
          uu____986 = c
      | FStar_Util.Inr s' -> s = s'
let matches_level:
  'Auu____994 .
    Prims.string ->
      ('Auu____994,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1013  ->
      match uu____1013 with
      | (assoc_levels,tokens) ->
          let uu____1041 = FStar_List.tryFind (matches_token s) tokens in
          uu____1041 <> FStar_Pervasives_Native.None
let opinfix4:
  'Auu____1067 .
    Prims.unit ->
      (associativity,('Auu____1067,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1078  -> (Right, [FStar_Util.Inr "**"])
let opinfix3:
  'Auu____1094 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1094) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1106  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
let opinfix2:
  'Auu____1141 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1141) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1153  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])
let minus_lvl:
  'Auu____1181 .
    Prims.unit ->
      (associativity,('Auu____1181,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1192  -> (Left, [FStar_Util.Inr "-"])
let opinfix1:
  'Auu____1208 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1208) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1220  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])
let pipe_right:
  'Auu____1248 .
    Prims.unit ->
      (associativity,('Auu____1248,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1259  -> (Left, [FStar_Util.Inr "|>"])
let opinfix0d:
  'Auu____1275 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1275) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1287  -> (Left, [FStar_Util.Inl 36])
let opinfix0c:
  'Auu____1308 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1308) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1320  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
let equal:
  'Auu____1355 .
    Prims.unit ->
      (associativity,('Auu____1355,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1366  -> (Left, [FStar_Util.Inr "="])
let opinfix0b:
  'Auu____1382 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1382) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1394  -> (Left, [FStar_Util.Inl 38])
let opinfix0a:
  'Auu____1415 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1415) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1427  -> (Left, [FStar_Util.Inl 124])
let colon_equals:
  'Auu____1448 .
    Prims.unit ->
      (associativity,('Auu____1448,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1459  -> (NonAssoc, [FStar_Util.Inr ":="])
let amp:
  'Auu____1475 .
    Prims.unit ->
      (associativity,('Auu____1475,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1486  -> (Right, [FStar_Util.Inr "&"])
let colon_colon:
  'Auu____1502 .
    Prims.unit ->
      (associativity,('Auu____1502,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1513  -> (Right, [FStar_Util.Inr "::"])
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
  let levels_from_associativity l uu___50_1720 =
    match uu___50_1720 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l) in
  FStar_List.mapi
    (fun i  ->
       fun uu____1760  ->
         match uu____1760 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
let assign_levels:
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1840 = FStar_List.tryFind (matches_level s) level_table in
      match uu____1840 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1890) ->
          assoc_levels
      | uu____1934 -> failwith (Prims.strcat "Unrecognized operator " s)
let max: Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2
let max_level:
  'Auu____1969 .
    ('Auu____1969,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2029 =
        FStar_List.tryFind
          (fun uu____2069  ->
             match uu____2069 with
             | (uu____2087,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table in
      match uu____2029 with
      | FStar_Pervasives_Native.Some ((uu____2129,l1,uu____2131),uu____2132)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2187 =
            let uu____2188 =
              let uu____2189 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level) in
              FStar_String.concat "," uu____2189 in
            FStar_Util.format1 "Undefined associativity level %s" uu____2188 in
          failwith uu____2187 in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
let levels:
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec
let operatorInfix0ad12:
  'Auu____2223 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2223) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2237  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
let is_operatorInfix0ad12: FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2318 =
      let uu____2332 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2332 (operatorInfix0ad12 ()) in
    uu____2318 <> FStar_Pervasives_Native.None
let is_operatorInfix34: FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()] in
  fun op  ->
    let uu____2445 =
      let uu____2459 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op) in
      FStar_List.tryFind uu____2459 opinfix34 in
    uu____2445 <> FStar_Pervasives_Native.None
let handleable_args_length: FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op in
    let uu____2525 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"]) in
    if uu____2525
    then Prims.parse_int "1"
    else
      (let uu____2527 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"]) in
       if uu____2527
       then Prims.parse_int "2"
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then Prims.parse_int "3"
         else Prims.parse_int "0")
let handleable_op:
  'Auu____2533 . FStar_Ident.ident -> 'Auu____2533 Prims.list -> Prims.bool =
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
      | uu____2546 -> false
let comment_stack:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref []
let with_comment:
  'Auu____2580 .
    ('Auu____2580 -> FStar_Pprint.document) ->
      'Auu____2580 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2612 = FStar_ST.op_Bang comment_stack in
          match uu____2612 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2700 = FStar_Range.range_before_pos crange print_pos in
              if uu____2700
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2766 =
                    let uu____2767 =
                      let uu____2768 = str comment in
                      FStar_Pprint.op_Hat_Hat uu____2768
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat acc uu____2767 in
                  comments_before_pos uu____2766 print_pos lookahead_pos))
              else
                (let uu____2770 =
                   FStar_Range.range_before_pos crange lookahead_pos in
                 (acc, uu____2770)) in
        let uu____2771 =
          let uu____2776 =
            let uu____2777 = FStar_Range.start_of_range tmrange in
            FStar_Range.end_of_line uu____2777 in
          let uu____2778 = FStar_Range.end_of_range tmrange in
          comments_before_pos FStar_Pprint.empty uu____2776 uu____2778 in
        match uu____2771 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange in
                let uu____2784 = comments_before_pos comments pos pos in
                FStar_Pervasives_Native.fst uu____2784
              else comments in
            let uu____2790 = FStar_Pprint.op_Hat_Hat comments1 printed_e in
            FStar_Pprint.group uu____2790
let rec place_comments_until_pos:
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2803 = FStar_ST.op_Bang comment_stack in
          match uu____2803 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2945 =
                    let uu____2946 =
                      let uu____2947 = FStar_Range.start_of_range crange in
                      FStar_Range.line_of_pos uu____2947 in
                    uu____2946 - lbegin in
                  max k uu____2945 in
                let doc2 =
                  let uu____2949 =
                    let uu____2950 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline in
                    let uu____2951 = str comment in
                    FStar_Pprint.op_Hat_Hat uu____2950 uu____2951 in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2949 in
                let uu____2952 =
                  let uu____2953 = FStar_Range.end_of_range crange in
                  FStar_Range.line_of_pos uu____2953 in
                place_comments_until_pos (Prims.parse_int "1") uu____2952
                  pos_end doc2))
          | uu____2954 ->
              let lnum =
                let uu____2962 =
                  let uu____2963 = FStar_Range.line_of_pos pos_end in
                  uu____2963 - lbegin in
                max (Prims.parse_int "1") uu____2962 in
              let uu____2964 = FStar_Pprint.repeat lnum FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat doc1 uu____2964
let separate_map_with_comments:
  'Auu____2971 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2971 -> FStar_Pprint.document) ->
          'Auu____2971 Prims.list ->
            ('Auu____2971 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3019 x =
              match uu____3019 with
              | (last_line,doc1) ->
                  let r = extract_range x in
                  let doc2 =
                    let uu____3033 = FStar_Range.start_of_range r in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3033 doc1 in
                  let uu____3034 =
                    let uu____3035 = FStar_Range.end_of_range r in
                    FStar_Range.line_of_pos uu____3035 in
                  let uu____3036 =
                    let uu____3037 =
                      let uu____3038 = f x in
                      FStar_Pprint.op_Hat_Hat sep uu____3038 in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3037 in
                  (uu____3034, uu____3036) in
            let uu____3039 =
              let uu____3046 = FStar_List.hd xs in
              let uu____3047 = FStar_List.tl xs in (uu____3046, uu____3047) in
            match uu____3039 with
            | (x,xs1) ->
                let init1 =
                  let uu____3063 =
                    let uu____3064 =
                      let uu____3065 = extract_range x in
                      FStar_Range.end_of_range uu____3065 in
                    FStar_Range.line_of_pos uu____3064 in
                  let uu____3066 =
                    let uu____3067 = f x in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3067 in
                  (uu____3063, uu____3066) in
                let uu____3068 = FStar_List.fold_left fold_fun init1 xs1 in
                FStar_Pervasives_Native.snd uu____3068
let rec p_decl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3363 =
      let uu____3364 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc in
      let uu____3365 =
        let uu____3366 = p_attributes d.FStar_Parser_AST.attrs in
        let uu____3367 =
          let uu____3368 = p_qualifiers d.FStar_Parser_AST.quals in
          let uu____3369 =
            let uu____3370 = p_rawDecl d in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3370 in
          FStar_Pprint.op_Hat_Hat uu____3368 uu____3369 in
        FStar_Pprint.op_Hat_Hat uu____3366 uu____3367 in
      FStar_Pprint.op_Hat_Hat uu____3364 uu____3365 in
    FStar_Pprint.group uu____3363
and p_attributes: FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3373 =
      let uu____3374 = str "@" in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3374 in
    let uu____3375 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3373 FStar_Pprint.space uu____3375
      p_atomicTerm attrs
and p_fsdoc: FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3376  ->
    match uu____3376 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3410 =
                match uu____3410 with
                | (kwd,arg) ->
                    let uu____3417 = str "@" in
                    let uu____3418 =
                      let uu____3419 = str kwd in
                      let uu____3420 =
                        let uu____3421 = str arg in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3421 in
                      FStar_Pprint.op_Hat_Hat uu____3419 uu____3420 in
                    FStar_Pprint.op_Hat_Hat uu____3417 uu____3418 in
              let uu____3422 =
                let uu____3423 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1 in
                FStar_Pprint.op_Hat_Hat uu____3423 FStar_Pprint.hardline in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3422 in
        let uu____3428 =
          let uu____3429 =
            let uu____3430 =
              let uu____3431 =
                let uu____3432 = str doc1 in
                let uu____3433 =
                  let uu____3434 =
                    let uu____3435 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3435 in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3434 in
                FStar_Pprint.op_Hat_Hat uu____3432 uu____3433 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3431 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3430 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3429 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3428
and p_justSig: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3439 =
          let uu____3440 = str "val" in
          let uu____3441 =
            let uu____3442 =
              let uu____3443 = p_lident lid in
              let uu____3444 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3443 uu____3444 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3442 in
          FStar_Pprint.op_Hat_Hat uu____3440 uu____3441 in
        let uu____3445 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3439 uu____3445
    | FStar_Parser_AST.TopLevelLet (uu____3446,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3471 =
               let uu____3472 = str "let" in
               let uu____3473 = p_letlhs lb in
               FStar_Pprint.op_Hat_Slash_Hat uu____3472 uu____3473 in
             FStar_Pprint.group uu____3471) lbs
    | uu____3474 -> FStar_Pprint.empty
and p_rawDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3477 =
          let uu____3478 = str "open" in
          let uu____3479 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3478 uu____3479 in
        FStar_Pprint.group uu____3477
    | FStar_Parser_AST.Include uid ->
        let uu____3481 =
          let uu____3482 = str "include" in
          let uu____3483 = p_quident uid in
          FStar_Pprint.op_Hat_Slash_Hat uu____3482 uu____3483 in
        FStar_Pprint.group uu____3481
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3486 =
          let uu____3487 = str "module" in
          let uu____3488 =
            let uu____3489 =
              let uu____3490 = p_uident uid1 in
              let uu____3491 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____3490 uu____3491 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3489 in
          FStar_Pprint.op_Hat_Hat uu____3487 uu____3488 in
        let uu____3492 = p_quident uid2 in
        op_Hat_Slash_Plus_Hat uu____3486 uu____3492
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3494 =
          let uu____3495 = str "module" in
          let uu____3496 =
            let uu____3497 = p_quident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3497 in
          FStar_Pprint.op_Hat_Hat uu____3495 uu____3496 in
        FStar_Pprint.group uu____3494
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3530 = str "effect" in
          let uu____3531 =
            let uu____3532 = p_uident uid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3532 in
          FStar_Pprint.op_Hat_Hat uu____3530 uu____3531 in
        let uu____3533 =
          let uu____3534 = p_typars tpars in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3534 FStar_Pprint.equals in
        let uu____3535 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3533 uu____3535
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3553 = str "type" in
        let uu____3554 = str "and" in
        precede_break_separate_map uu____3553 uu____3554 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3576 = str "let" in
          let uu____3577 =
            let uu____3578 = p_letqualifier q in
            FStar_Pprint.op_Hat_Hat uu____3578 FStar_Pprint.space in
          FStar_Pprint.op_Hat_Hat uu____3576 uu____3577 in
        let uu____3579 =
          let uu____3580 = str "and" in
          FStar_Pprint.op_Hat_Hat uu____3580 FStar_Pprint.space in
        separate_map_with_comments let_doc uu____3579 p_letbinding lbs
          (fun uu____3588  ->
             match uu____3588 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3597 =
          let uu____3598 = str "val" in
          let uu____3599 =
            let uu____3600 =
              let uu____3601 = p_lident lid in
              let uu____3602 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
              FStar_Pprint.op_Hat_Hat uu____3601 uu____3602 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3600 in
          FStar_Pprint.op_Hat_Hat uu____3598 uu____3599 in
        let uu____3603 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3597 uu____3603
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3607 =
            let uu____3608 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0") in
            FStar_All.pipe_right uu____3608 FStar_Util.is_upper in
          if uu____3607
          then FStar_Pprint.empty
          else
            (let uu____3610 = str "val" in
             FStar_Pprint.op_Hat_Hat uu____3610 FStar_Pprint.space) in
        let uu____3611 =
          let uu____3612 =
            let uu____3613 = p_ident id1 in
            let uu____3614 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon in
            FStar_Pprint.op_Hat_Hat uu____3613 uu____3614 in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3612 in
        let uu____3615 = p_typ t in
        op_Hat_Slash_Plus_Hat uu____3611 uu____3615
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3622 = str "exception" in
        let uu____3623 =
          let uu____3624 =
            let uu____3625 = p_uident uid in
            let uu____3626 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3631 = str "of" in
                   let uu____3632 = p_typ t in
                   op_Hat_Slash_Plus_Hat uu____3631 uu____3632) t_opt in
            FStar_Pprint.op_Hat_Hat uu____3625 uu____3626 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3624 in
        FStar_Pprint.op_Hat_Hat uu____3622 uu____3623
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3634 = str "new_effect" in
        let uu____3635 =
          let uu____3636 = p_newEffect ne in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3636 in
        FStar_Pprint.op_Hat_Hat uu____3634 uu____3635
    | FStar_Parser_AST.SubEffect se ->
        let uu____3638 = str "sub_effect" in
        let uu____3639 =
          let uu____3640 = p_subEffect se in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3640 in
        FStar_Pprint.op_Hat_Hat uu____3638 uu____3639
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3643 = p_fsdoc doc1 in
        FStar_Pprint.op_Hat_Hat uu____3643 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3644 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3645) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
and p_pragma: FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___51_3662  ->
    match uu___51_3662 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3664 = str "#set-options" in
        let uu____3665 =
          let uu____3666 =
            let uu____3667 = str s in FStar_Pprint.dquotes uu____3667 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3666 in
        FStar_Pprint.op_Hat_Hat uu____3664 uu____3665
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3671 = str "#reset-options" in
        let uu____3672 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3676 =
                 let uu____3677 = str s in FStar_Pprint.dquotes uu____3677 in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3676) s_opt in
        FStar_Pprint.op_Hat_Hat uu____3671 uu____3672
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
  fun uu____3730  ->
    match uu____3730 with
    | (typedecl,fsdoc_opt) ->
        let uu____3743 = FStar_Pprint.optional p_fsdoc fsdoc_opt in
        let uu____3744 = p_typeDecl typedecl in
        FStar_Pprint.op_Hat_Hat uu____3743 uu____3744
and p_typeDecl: FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___52_3745  ->
    match uu___52_3745 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3760 = FStar_Pprint.empty in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3776 =
          let uu____3777 = p_typ t in prefix2 FStar_Pprint.equals uu____3777 in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3821 =
          match uu____3821 with
          | (lid1,t,doc_opt) ->
              let uu____3837 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3837 in
        let p_fields uu____3851 =
          let uu____3852 =
            let uu____3853 =
              let uu____3854 =
                let uu____3855 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
                FStar_Pprint.separate_map uu____3855 p_recordFieldAndComments
                  record_field_decls in
              braces_with_nesting uu____3854 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3853 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3852 in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3919 =
          match uu____3919 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3945 =
                  let uu____3946 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range) in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3946 in
                FStar_Range.extend_to_end_of_line uu____3945 in
              let p_constructorBranch decl =
                let uu____3979 =
                  let uu____3980 =
                    let uu____3981 = p_constructorDecl decl in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3981 in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3980 in
                FStar_Pprint.group uu____3979 in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range in
        let datacon_doc uu____4001 =
          let uu____4002 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls in
          FStar_Pprint.group uu____4002 in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4017  ->
             let uu____4018 = datacon_doc () in
             prefix2 FStar_Pprint.equals uu____4018)
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
            let uu____4033 = p_ident lid in
            let uu____4034 =
              let uu____4035 = cont () in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4035 in
            FStar_Pprint.op_Hat_Hat uu____4033 uu____4034
          else
            (let binders_doc =
               let uu____4038 = p_typars bs in
               let uu____4039 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4043 =
                        let uu____4044 =
                          let uu____4045 = p_typ t in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4045 in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4044 in
                      FStar_Pprint.op_Hat_Hat break1 uu____4043) typ_opt in
               FStar_Pprint.op_Hat_Hat uu____4038 uu____4039 in
             let uu____4046 = p_ident lid in
             let uu____4047 = cont () in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4046 binders_doc uu____4047)
and p_recordFieldDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4048  ->
    match uu____4048 with
    | (lid,t,doc_opt) ->
        let uu____4064 =
          let uu____4065 = FStar_Pprint.optional p_fsdoc doc_opt in
          let uu____4066 =
            let uu____4067 = p_lident lid in
            let uu____4068 =
              let uu____4069 = p_typ t in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4069 in
            FStar_Pprint.op_Hat_Hat uu____4067 uu____4068 in
          FStar_Pprint.op_Hat_Hat uu____4065 uu____4066 in
        FStar_Pprint.group uu____4064
and p_constructorDecl:
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____4070  ->
    match uu____4070 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon in
        let uid_doc = p_uident uid in
        let uu____4098 = FStar_Pprint.optional p_fsdoc doc_opt in
        let uu____4099 =
          let uu____4100 = FStar_Pprint.break_ (Prims.parse_int "0") in
          let uu____4101 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4106 =
                   let uu____4107 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4107 in
                 let uu____4108 = p_typ t in
                 op_Hat_Slash_Plus_Hat uu____4106 uu____4108) t_opt in
          FStar_Pprint.op_Hat_Hat uu____4100 uu____4101 in
        FStar_Pprint.op_Hat_Hat uu____4098 uu____4099
and p_letlhs:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4109  ->
    match uu____4109 with
    | (pat,uu____4115) ->
        let uu____4116 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4127 =
                let uu____4128 =
                  let uu____4129 =
                    let uu____4130 =
                      let uu____4131 = p_tmArrow p_tmNoEq t in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4131 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4130 in
                  FStar_Pprint.group uu____4129 in
                FStar_Pprint.op_Hat_Hat break1 uu____4128 in
              (pat1, uu____4127)
          | uu____4132 -> (pat, FStar_Pprint.empty) in
        (match uu____4116 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4136);
                     FStar_Parser_AST.prange = uu____4137;_},pats)
                  ->
                  let uu____4147 =
                    let uu____4148 = p_lident x in
                    let uu____4149 =
                      let uu____4150 =
                        separate_map_or_flow break1 p_atomicPattern pats in
                      FStar_Pprint.op_Hat_Hat uu____4150 ascr_doc in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4148 uu____4149 in
                  FStar_Pprint.group uu____4147
              | uu____4151 ->
                  let uu____4152 =
                    let uu____4153 = p_tuplePattern pat1 in
                    FStar_Pprint.op_Hat_Hat uu____4153 ascr_doc in
                  FStar_Pprint.group uu____4152))
and p_letbinding:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4154  ->
    match uu____4154 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e) in
        let uu____4162 =
          let uu____4163 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals in
          FStar_Pprint.group uu____4163 in
        let uu____4164 = p_term e in prefix2 uu____4162 uu____4164
and p_newEffect: FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___53_4165  ->
    match uu___53_4165 with
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
        let uu____4190 = p_uident uid in
        let uu____4191 = p_binders true bs in
        let uu____4192 =
          let uu____4193 = p_simpleTerm t in
          prefix2 FStar_Pprint.equals uu____4193 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4190 uu____4191 uu____4192
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
          let uu____4202 =
            let uu____4203 =
              let uu____4204 =
                let uu____4205 = p_uident uid in
                let uu____4206 = p_binders true bs in
                let uu____4207 =
                  let uu____4208 = p_typ t in
                  prefix2 FStar_Pprint.colon uu____4208 in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4205 uu____4206 uu____4207 in
              FStar_Pprint.group uu____4204 in
            let uu____4209 =
              let uu____4210 = str "with" in
              let uu____4211 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls in
              prefix2 uu____4210 uu____4211 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4203 uu____4209 in
          braces_with_nesting uu____4202
and p_effectDecl: FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4241 =
          let uu____4242 = p_lident lid in
          let uu____4243 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals in
          FStar_Pprint.op_Hat_Hat uu____4242 uu____4243 in
        let uu____4244 = p_simpleTerm e in prefix2 uu____4241 uu____4244
    | uu____4245 ->
        let uu____4246 =
          let uu____4247 = FStar_Parser_AST.decl_to_string d in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4247 in
        failwith uu____4246
and p_subEffect: FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)] in
      let p_lift uu____4302 =
        match uu____4302 with
        | (kwd,t) ->
            let uu____4309 =
              let uu____4310 = str kwd in
              let uu____4311 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals in
              FStar_Pprint.op_Hat_Hat uu____4310 uu____4311 in
            let uu____4312 = p_simpleTerm t in prefix2 uu____4309 uu____4312 in
      separate_break_map FStar_Pprint.semi p_lift lifts in
    let uu____4317 =
      let uu____4318 =
        let uu____4319 = p_quident lift.FStar_Parser_AST.msource in
        let uu____4320 =
          let uu____4321 = str "~>" in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4321 in
        FStar_Pprint.op_Hat_Hat uu____4319 uu____4320 in
      let uu____4322 = p_quident lift.FStar_Parser_AST.mdest in
      prefix2 uu____4318 uu____4322 in
    let uu____4323 =
      let uu____4324 = braces_with_nesting lift_op_doc in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4324 in
    FStar_Pprint.op_Hat_Hat uu____4317 uu____4323
and p_qualifier: FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___54_4325  ->
    match uu___54_4325 with
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
    let uu____4327 = FStar_Pprint.separate_map break1 p_qualifier qs in
    FStar_Pprint.group uu____4327
and p_letqualifier: FStar_Parser_AST.let_qualifier -> FStar_Pprint.document =
  fun uu___55_4328  ->
    match uu___55_4328 with
    | FStar_Parser_AST.Rec  ->
        let uu____4329 = str "rec" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4329
    | FStar_Parser_AST.Mutable  ->
        let uu____4330 = str "mutable" in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4330
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty
and p_aqual: FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___56_4331  ->
    match uu___56_4331 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
and p_disjunctivePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4336 =
          let uu____4337 =
            let uu____4338 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space in
            FStar_Pprint.op_Hat_Hat break1 uu____4338 in
          FStar_Pprint.separate_map uu____4337 p_tuplePattern pats in
        FStar_Pprint.group uu____4336
    | uu____4339 -> p_tuplePattern p
and p_tuplePattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4346 =
          let uu____4347 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          FStar_Pprint.separate_map uu____4347 p_constructorPattern pats in
        FStar_Pprint.group uu____4346
    | uu____4348 -> p_constructorPattern p
and p_constructorPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4351;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4356 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon in
        let uu____4357 = p_constructorPattern hd1 in
        let uu____4358 = p_constructorPattern tl1 in
        infix0 uu____4356 uu____4357 uu____4358
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4360;_},pats)
        ->
        let uu____4366 = p_quident uid in
        let uu____4367 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats in
        prefix2 uu____4366 uu____4367
    | uu____4368 -> p_atomicPattern p
and p_atomicPattern: FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4372 =
          let uu____4377 =
            let uu____4378 = unparen t in uu____4378.FStar_Parser_AST.tm in
          ((pat.FStar_Parser_AST.pat), uu____4377) in
        (match uu____4372 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4383;
               FStar_Parser_AST.blevel = uu____4384;
               FStar_Parser_AST.aqual = uu____4385;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4391 =
               let uu____4392 = p_ident lid in
               p_refinement aqual uu____4392 t1 phi in
             soft_parens_with_nesting uu____4391
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4394;
               FStar_Parser_AST.blevel = uu____4395;
               FStar_Parser_AST.aqual = uu____4396;_},phi))
             ->
             let uu____4398 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi in
             soft_parens_with_nesting uu____4398
         | uu____4399 ->
             let uu____4404 =
               let uu____4405 = p_tuplePattern pat in
               let uu____4406 =
                 let uu____4407 = FStar_Pprint.break_ (Prims.parse_int "0") in
                 let uu____4408 =
                   let uu____4409 = p_typ t in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4409 in
                 FStar_Pprint.op_Hat_Hat uu____4407 uu____4408 in
               FStar_Pprint.op_Hat_Hat uu____4405 uu____4406 in
             soft_parens_with_nesting uu____4404)
    | FStar_Parser_AST.PatList pats ->
        let uu____4413 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4413 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4428 =
          match uu____4428 with
          | (lid,pat) ->
              let uu____4435 = p_qlident lid in
              let uu____4436 = p_tuplePattern pat in
              infix2 FStar_Pprint.equals uu____4435 uu____4436 in
        let uu____4437 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats in
        soft_braces_with_nesting uu____4437
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4447 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____4448 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats in
        let uu____4449 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4447 uu____4448 uu____4449
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4460 =
          let uu____4461 =
            let uu____4462 = str (FStar_Ident.text_of_id op) in
            let uu____4463 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____4462 uu____4463 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4461 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4460
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4471 = FStar_Pprint.optional p_aqual aqual in
        let uu____4472 = p_lident lid in
        FStar_Pprint.op_Hat_Hat uu____4471 uu____4472
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4474 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4477;
           FStar_Parser_AST.prange = uu____4478;_},uu____4479)
        ->
        let uu____4484 = p_tuplePattern p in
        soft_parens_with_nesting uu____4484
    | FStar_Parser_AST.PatTuple (uu____4485,false ) ->
        let uu____4490 = p_tuplePattern p in
        soft_parens_with_nesting uu____4490
    | uu____4491 ->
        let uu____4492 =
          let uu____4493 = FStar_Parser_AST.pat_to_string p in
          FStar_Util.format1 "Invalid pattern %s" uu____4493 in
        failwith uu____4492
and p_binder: Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4497 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
          let uu____4498 = p_lident lid in
          FStar_Pprint.op_Hat_Hat uu____4497 uu____4498
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4503 =
              let uu____4504 = unparen t in uu____4504.FStar_Parser_AST.tm in
            match uu____4503 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4507;
                   FStar_Parser_AST.blevel = uu____4508;
                   FStar_Parser_AST.aqual = uu____4509;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4511 = p_ident lid in
                p_refinement b.FStar_Parser_AST.aqual uu____4511 t1 phi
            | uu____4512 ->
                let uu____4513 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual in
                let uu____4514 =
                  let uu____4515 = p_lident lid in
                  let uu____4516 =
                    let uu____4517 =
                      let uu____4518 =
                        FStar_Pprint.break_ (Prims.parse_int "0") in
                      let uu____4519 = p_tmFormula t in
                      FStar_Pprint.op_Hat_Hat uu____4518 uu____4519 in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4517 in
                  FStar_Pprint.op_Hat_Hat uu____4515 uu____4516 in
                FStar_Pprint.op_Hat_Hat uu____4513 uu____4514 in
          if is_atomic
          then
            let uu____4520 =
              let uu____4521 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4521 in
            FStar_Pprint.group uu____4520
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4523 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4529 =
            let uu____4530 = unparen t in uu____4530.FStar_Parser_AST.tm in
          (match uu____4529 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4532;
                  FStar_Parser_AST.blevel = uu____4533;
                  FStar_Parser_AST.aqual = uu____4534;_},phi)
               ->
               if is_atomic
               then
                 let uu____4536 =
                   let uu____4537 =
                     let uu____4538 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi in
                     FStar_Pprint.op_Hat_Hat uu____4538 FStar_Pprint.rparen in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4537 in
                 FStar_Pprint.group uu____4536
               else
                 (let uu____4540 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi in
                  FStar_Pprint.group uu____4540)
           | uu____4541 -> if is_atomic then p_atomicTerm t else p_appTerm t)
and p_refinement:
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4549 = FStar_Pprint.optional p_aqual aqual_opt in
          let uu____4550 =
            let uu____4551 =
              let uu____4552 =
                let uu____4553 = p_appTerm t in
                let uu____4554 =
                  let uu____4555 = p_noSeqTerm phi in
                  soft_braces_with_nesting uu____4555 in
                FStar_Pprint.op_Hat_Hat uu____4553 uu____4554 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4552 in
            FStar_Pprint.op_Hat_Hat binder uu____4551 in
          FStar_Pprint.op_Hat_Hat uu____4549 uu____4550
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
    let uu____4569 =
      let uu____4570 = unparen e in uu____4570.FStar_Parser_AST.tm in
    match uu____4569 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4573 =
          let uu____4574 =
            let uu____4575 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____4575 FStar_Pprint.semi in
          FStar_Pprint.group uu____4574 in
        let uu____4576 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4573 uu____4576
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4580 =
          let uu____4581 =
            let uu____4582 =
              let uu____4583 = p_lident x in
              let uu____4584 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow in
              FStar_Pprint.op_Hat_Hat uu____4583 uu____4584 in
            let uu____4585 =
              let uu____4586 = p_noSeqTerm e1 in
              let uu____4587 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi in
              FStar_Pprint.op_Hat_Hat uu____4586 uu____4587 in
            op_Hat_Slash_Plus_Hat uu____4582 uu____4585 in
          FStar_Pprint.group uu____4581 in
        let uu____4588 = p_term e2 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4580 uu____4588
    | uu____4589 ->
        let uu____4590 = p_noSeqTerm e in FStar_Pprint.group uu____4590
and p_noSeqTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range
and p_noSeqTerm': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4593 =
      let uu____4594 = unparen e in uu____4594.FStar_Parser_AST.tm in
    match uu____4593 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4599 =
          let uu____4600 = p_tmIff e1 in
          let uu____4601 =
            let uu____4602 =
              let uu____4603 = p_typ t in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4603 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4602 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4600 uu____4601 in
        FStar_Pprint.group uu____4599
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4609 =
          let uu____4610 = p_tmIff e1 in
          let uu____4611 =
            let uu____4612 =
              let uu____4613 =
                let uu____4614 = p_typ t in
                let uu____4615 =
                  let uu____4616 = str "by" in
                  let uu____4617 = p_typ tac in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4616 uu____4617 in
                FStar_Pprint.op_Hat_Slash_Hat uu____4614 uu____4615 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4613 in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4612 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4610 uu____4611 in
        FStar_Pprint.group uu____4609
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4618;_},e1::e2::e3::[])
        ->
        let uu____4624 =
          let uu____4625 =
            let uu____4626 =
              let uu____4627 = p_atomicTermNotQUident e1 in
              let uu____4628 =
                let uu____4629 =
                  let uu____4630 =
                    let uu____4631 = p_term e2 in
                    soft_parens_with_nesting uu____4631 in
                  let uu____4632 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4630 uu____4632 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4629 in
              FStar_Pprint.op_Hat_Hat uu____4627 uu____4628 in
            FStar_Pprint.group uu____4626 in
          let uu____4633 =
            let uu____4634 = p_noSeqTerm e3 in jump2 uu____4634 in
          FStar_Pprint.op_Hat_Hat uu____4625 uu____4633 in
        FStar_Pprint.group uu____4624
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4635;_},e1::e2::e3::[])
        ->
        let uu____4641 =
          let uu____4642 =
            let uu____4643 =
              let uu____4644 = p_atomicTermNotQUident e1 in
              let uu____4645 =
                let uu____4646 =
                  let uu____4647 =
                    let uu____4648 = p_term e2 in
                    soft_brackets_with_nesting uu____4648 in
                  let uu____4649 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow in
                  FStar_Pprint.op_Hat_Hat uu____4647 uu____4649 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4646 in
              FStar_Pprint.op_Hat_Hat uu____4644 uu____4645 in
            FStar_Pprint.group uu____4643 in
          let uu____4650 =
            let uu____4651 = p_noSeqTerm e3 in jump2 uu____4651 in
          FStar_Pprint.op_Hat_Hat uu____4642 uu____4650 in
        FStar_Pprint.group uu____4641
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4661 =
          let uu____4662 = str "requires" in
          let uu____4663 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4662 uu____4663 in
        FStar_Pprint.group uu____4661
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4673 =
          let uu____4674 = str "ensures" in
          let uu____4675 = p_typ e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4674 uu____4675 in
        FStar_Pprint.group uu____4673
    | FStar_Parser_AST.Attributes es ->
        let uu____4679 =
          let uu____4680 = str "attributes" in
          let uu____4681 = FStar_Pprint.separate_map break1 p_atomicTerm es in
          FStar_Pprint.op_Hat_Slash_Hat uu____4680 uu____4681 in
        FStar_Pprint.group uu____4679
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4685 = is_unit e3 in
        if uu____4685
        then
          let uu____4686 =
            let uu____4687 =
              let uu____4688 = str "if" in
              let uu____4689 = p_noSeqTerm e1 in
              op_Hat_Slash_Plus_Hat uu____4688 uu____4689 in
            let uu____4690 =
              let uu____4691 = str "then" in
              let uu____4692 = p_noSeqTerm e2 in
              op_Hat_Slash_Plus_Hat uu____4691 uu____4692 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4687 uu____4690 in
          FStar_Pprint.group uu____4686
        else
          (let e2_doc =
             let uu____4695 =
               let uu____4696 = unparen e2 in uu____4696.FStar_Parser_AST.tm in
             match uu____4695 with
             | FStar_Parser_AST.If (uu____4697,uu____4698,e31) when
                 is_unit e31 ->
                 let uu____4700 = p_noSeqTerm e2 in
                 soft_parens_with_nesting uu____4700
             | uu____4701 -> p_noSeqTerm e2 in
           let uu____4702 =
             let uu____4703 =
               let uu____4704 = str "if" in
               let uu____4705 = p_noSeqTerm e1 in
               op_Hat_Slash_Plus_Hat uu____4704 uu____4705 in
             let uu____4706 =
               let uu____4707 =
                 let uu____4708 = str "then" in
                 op_Hat_Slash_Plus_Hat uu____4708 e2_doc in
               let uu____4709 =
                 let uu____4710 = str "else" in
                 let uu____4711 = p_noSeqTerm e3 in
                 op_Hat_Slash_Plus_Hat uu____4710 uu____4711 in
               FStar_Pprint.op_Hat_Slash_Hat uu____4707 uu____4709 in
             FStar_Pprint.op_Hat_Slash_Hat uu____4703 uu____4706 in
           FStar_Pprint.group uu____4702)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4734 =
          let uu____4735 =
            let uu____4736 = str "try" in
            let uu____4737 = p_noSeqTerm e1 in prefix2 uu____4736 uu____4737 in
          let uu____4738 =
            let uu____4739 = str "with" in
            let uu____4740 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches in
            FStar_Pprint.op_Hat_Slash_Hat uu____4739 uu____4740 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4735 uu____4738 in
        FStar_Pprint.group uu____4734
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4771 =
          let uu____4772 =
            let uu____4773 = str "match" in
            let uu____4774 = p_noSeqTerm e1 in
            let uu____4775 = str "with" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4773 uu____4774 uu____4775 in
          let uu____4776 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4772 uu____4776 in
        FStar_Pprint.group uu____4771
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4787 =
          let uu____4788 =
            let uu____4789 = str "let open" in
            let uu____4790 = p_quident uid in
            let uu____4791 = str "in" in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4789 uu____4790 uu____4791 in
          let uu____4792 = p_term e1 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4788 uu____4792 in
        FStar_Pprint.group uu____4787
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4809 = str "let" in
          let uu____4810 = p_letqualifier q in
          FStar_Pprint.op_Hat_Hat uu____4809 uu____4810 in
        let uu____4811 =
          let uu____4812 =
            let uu____4813 =
              let uu____4814 = str "and" in
              precede_break_separate_map let_doc uu____4814 p_letbinding lbs in
            let uu____4819 = str "in" in
            FStar_Pprint.op_Hat_Slash_Hat uu____4813 uu____4819 in
          FStar_Pprint.group uu____4812 in
        let uu____4820 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____4811 uu____4820
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4823;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4826;
                                                         FStar_Parser_AST.level
                                                           = uu____4827;_})
        when matches_var maybe_x x ->
        let uu____4854 =
          let uu____4855 = str "function" in
          let uu____4856 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches in
          FStar_Pprint.op_Hat_Slash_Hat uu____4855 uu____4856 in
        FStar_Pprint.group uu____4854
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4867 =
          let uu____4868 = p_lident id1 in
          let uu____4869 =
            let uu____4870 = p_noSeqTerm e1 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4870 in
          FStar_Pprint.op_Hat_Slash_Hat uu____4868 uu____4869 in
        FStar_Pprint.group uu____4867
    | uu____4871 -> p_typ e
and p_typ: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range
and p_typ': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4874 =
      let uu____4875 = unparen e in uu____4875.FStar_Parser_AST.tm in
    match uu____4874 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4891 =
          let uu____4892 =
            let uu____4893 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4893 FStar_Pprint.space in
          let uu____4894 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4892 uu____4894 FStar_Pprint.dot in
        let uu____4895 =
          let uu____4896 = p_trigger trigger in
          let uu____4897 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4896 uu____4897 in
        prefix2 uu____4891 uu____4895
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4913 =
          let uu____4914 =
            let uu____4915 = p_quantifier e in
            FStar_Pprint.op_Hat_Hat uu____4915 FStar_Pprint.space in
          let uu____4916 = p_binders true bs in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4914 uu____4916 FStar_Pprint.dot in
        let uu____4917 =
          let uu____4918 = p_trigger trigger in
          let uu____4919 = p_noSeqTerm e1 in
          FStar_Pprint.op_Hat_Hat uu____4918 uu____4919 in
        prefix2 uu____4913 uu____4917
    | uu____4920 -> p_simpleTerm e
and p_quantifier: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4922 =
      let uu____4923 = unparen e in uu____4923.FStar_Parser_AST.tm in
    match uu____4922 with
    | FStar_Parser_AST.QForall uu____4924 -> str "forall"
    | FStar_Parser_AST.QExists uu____4937 -> str "exists"
    | uu____4950 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"
and p_trigger:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___57_4951  ->
    match uu___57_4951 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4963 =
          let uu____4964 =
            let uu____4965 = str "pattern" in
            let uu____4966 =
              let uu____4967 =
                let uu____4968 = p_disjunctivePats pats in jump2 uu____4968 in
              let uu____4969 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4967 uu____4969 in
            FStar_Pprint.op_Hat_Slash_Hat uu____4965 uu____4966 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4964 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4963
and p_disjunctivePats:
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4975 = str "\\/" in
    FStar_Pprint.separate_map uu____4975 p_conjunctivePats pats
and p_conjunctivePats:
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4981 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats in
    FStar_Pprint.group uu____4981
and p_simpleTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4983 =
      let uu____4984 = unparen e in uu____4984.FStar_Parser_AST.tm in
    match uu____4983 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4991 =
          let uu____4992 = str "fun" in
          let uu____4993 =
            let uu____4994 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats in
            FStar_Pprint.op_Hat_Slash_Hat uu____4994 FStar_Pprint.rarrow in
          op_Hat_Slash_Plus_Hat uu____4992 uu____4993 in
        let uu____4995 = p_term e1 in
        op_Hat_Slash_Plus_Hat uu____4991 uu____4995
    | uu____4996 -> p_tmIff e
and p_maybeFocusArrow: Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow
and p_patternBranch:
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4999  ->
    match uu____4999 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____5018 =
            let uu____5019 = unparen e in uu____5019.FStar_Parser_AST.tm in
          match uu____5018 with
          | FStar_Parser_AST.Match uu____5022 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____5037 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____5053);
                 FStar_Parser_AST.prange = uu____5054;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____5056);
                                                               FStar_Parser_AST.range
                                                                 = uu____5057;
                                                               FStar_Parser_AST.level
                                                                 = uu____5058;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____5085 -> (fun x  -> x) in
        let uu____5087 =
          let uu____5088 =
            let uu____5089 =
              let uu____5090 =
                let uu____5091 =
                  let uu____5092 = p_disjunctivePattern pat in
                  let uu____5093 =
                    let uu____5094 = p_maybeWhen when_opt in
                    FStar_Pprint.op_Hat_Hat uu____5094 FStar_Pprint.rarrow in
                  op_Hat_Slash_Plus_Hat uu____5092 uu____5093 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5091 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5090 in
            FStar_Pprint.group uu____5089 in
          let uu____5095 =
            let uu____5096 = p_term e in maybe_paren uu____5096 in
          op_Hat_Slash_Plus_Hat uu____5088 uu____5095 in
        FStar_Pprint.group uu____5087
and p_maybeWhen:
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___58_5097  ->
    match uu___58_5097 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5101 = str "when" in
        let uu____5102 =
          let uu____5103 = p_tmFormula e in
          FStar_Pprint.op_Hat_Hat uu____5103 FStar_Pprint.space in
        op_Hat_Slash_Plus_Hat uu____5101 uu____5102
and p_tmIff: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5105 =
      let uu____5106 = unparen e in uu____5106.FStar_Parser_AST.tm in
    match uu____5105 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5107;_},e1::e2::[])
        ->
        let uu____5112 = str "<==>" in
        let uu____5113 = p_tmImplies e1 in
        let uu____5114 = p_tmIff e2 in
        infix0 uu____5112 uu____5113 uu____5114
    | uu____5115 -> p_tmImplies e
and p_tmImplies: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5117 =
      let uu____5118 = unparen e in uu____5118.FStar_Parser_AST.tm in
    match uu____5117 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5119;_},e1::e2::[])
        ->
        let uu____5124 = str "==>" in
        let uu____5125 = p_tmArrow p_tmFormula e1 in
        let uu____5126 = p_tmImplies e2 in
        infix0 uu____5124 uu____5125 uu____5126
    | uu____5127 -> p_tmArrow p_tmFormula e
and p_tmArrow:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____5132 =
        let uu____5133 = unparen e in uu____5133.FStar_Parser_AST.tm in
      match uu____5132 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5140 =
            let uu____5141 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5146 = p_binder false b in
                   let uu____5147 =
                     let uu____5148 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1 in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5148 in
                   FStar_Pprint.op_Hat_Hat uu____5146 uu____5147) bs in
            let uu____5149 = p_tmArrow p_Tm tgt in
            FStar_Pprint.op_Hat_Hat uu____5141 uu____5149 in
          FStar_Pprint.group uu____5140
      | uu____5150 -> p_Tm e
and p_tmFormula: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5152 =
      let uu____5153 = unparen e in uu____5153.FStar_Parser_AST.tm in
    match uu____5152 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5154;_},e1::e2::[])
        ->
        let uu____5159 = str "\\/" in
        let uu____5160 = p_tmFormula e1 in
        let uu____5161 = p_tmConjunction e2 in
        infix0 uu____5159 uu____5160 uu____5161
    | uu____5162 -> p_tmConjunction e
and p_tmConjunction: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5164 =
      let uu____5165 = unparen e in uu____5165.FStar_Parser_AST.tm in
    match uu____5164 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5166;_},e1::e2::[])
        ->
        let uu____5171 = str "/\\" in
        let uu____5172 = p_tmConjunction e1 in
        let uu____5173 = p_tmTuple e2 in
        infix0 uu____5171 uu____5172 uu____5173
    | uu____5174 -> p_tmTuple e
and p_tmTuple: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range
and p_tmTuple': FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5177 =
      let uu____5178 = unparen e in uu____5178.FStar_Parser_AST.tm in
    match uu____5177 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5193 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
        FStar_Pprint.separate_map uu____5193
          (fun uu____5201  ->
             match uu____5201 with | (e1,uu____5207) -> p_tmEq e1) args
    | uu____5208 -> p_tmEq e
and paren_if:
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5213 =
             let uu____5214 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5214 in
           FStar_Pprint.group uu____5213)
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
      let uu____5265 =
        let uu____5266 = unparen e in uu____5266.FStar_Parser_AST.tm in
      match uu____5265 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5273 = levels op1 in
          (match uu____5273 with
           | (left1,mine,right1) ->
               let uu____5283 =
                 let uu____5284 = FStar_All.pipe_left str op1 in
                 let uu____5285 = p_tmEq' left1 e1 in
                 let uu____5286 = p_tmEq' right1 e2 in
                 infix0 uu____5284 uu____5285 uu____5286 in
               paren_if curr mine uu____5283)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5287;_},e1::e2::[])
          ->
          let uu____5292 =
            let uu____5293 = p_tmEq e1 in
            let uu____5294 =
              let uu____5295 =
                let uu____5296 =
                  let uu____5297 = p_tmEq e2 in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5297 in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5296 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5295 in
            FStar_Pprint.op_Hat_Hat uu____5293 uu____5294 in
          FStar_Pprint.group uu____5292
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5298;_},e1::[])
          ->
          let uu____5302 = levels "-" in
          (match uu____5302 with
           | (left1,mine,right1) ->
               let uu____5312 = p_tmEq' mine e1 in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5312)
      | uu____5313 -> p_tmNoEq e
and p_tmNoEq: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()] in
    p_tmNoEq' n1 e
and p_tmNoEq': Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5376 =
        let uu____5377 = unparen e in uu____5377.FStar_Parser_AST.tm in
      match uu____5376 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5380)::(e2,uu____5382)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5402 = is_list e in Prims.op_Negation uu____5402)
          ->
          let op = "::" in
          let uu____5404 = levels op in
          (match uu____5404 with
           | (left1,mine,right1) ->
               let uu____5414 =
                 let uu____5415 = str op in
                 let uu____5416 = p_tmNoEq' left1 e1 in
                 let uu____5417 = p_tmNoEq' right1 e2 in
                 infix0 uu____5415 uu____5416 uu____5417 in
               paren_if curr mine uu____5414)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&" in
          let uu____5425 = levels op in
          (match uu____5425 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5439 = p_binder false b in
                 let uu____5440 =
                   let uu____5441 =
                     let uu____5442 = str op in
                     FStar_Pprint.op_Hat_Hat uu____5442 break1 in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5441 in
                 FStar_Pprint.op_Hat_Hat uu____5439 uu____5440 in
               let uu____5443 =
                 let uu____5444 = FStar_Pprint.concat_map p_dsumfst binders in
                 let uu____5445 = p_tmNoEq' right1 res in
                 FStar_Pprint.op_Hat_Hat uu____5444 uu____5445 in
               paren_if curr mine uu____5443)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op in
          let uu____5452 = levels op1 in
          (match uu____5452 with
           | (left1,mine,right1) ->
               let uu____5462 =
                 let uu____5463 = str op1 in
                 let uu____5464 = p_tmNoEq' left1 e1 in
                 let uu____5465 = p_tmNoEq' right1 e2 in
                 infix0 uu____5463 uu____5464 uu____5465 in
               paren_if curr mine uu____5462)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5468 =
            let uu____5469 = p_lidentOrUnderscore lid in
            let uu____5470 =
              let uu____5471 = p_appTerm e1 in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5471 in
            FStar_Pprint.op_Hat_Slash_Hat uu____5469 uu____5470 in
          FStar_Pprint.group uu____5468
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5492 =
            let uu____5493 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt in
            let uu____5494 =
              let uu____5495 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
              FStar_Pprint.separate_map uu____5495 p_simpleDef record_fields in
            FStar_Pprint.op_Hat_Hat uu____5493 uu____5494 in
          braces_with_nesting uu____5492
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5500;_},e1::[])
          ->
          let uu____5504 =
            let uu____5505 = str "~" in
            let uu____5506 = p_atomicTerm e1 in
            FStar_Pprint.op_Hat_Hat uu____5505 uu____5506 in
          FStar_Pprint.group uu____5504
      | uu____5507 -> p_appTerm e
and p_with_clause: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5509 = p_appTerm e in
    let uu____5510 =
      let uu____5511 =
        let uu____5512 = str "with" in
        FStar_Pprint.op_Hat_Hat uu____5512 break1 in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5511 in
    FStar_Pprint.op_Hat_Hat uu____5509 uu____5510
and p_refinedBinder:
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5517 =
            let uu____5518 = p_lident lid in
            p_refinement b.FStar_Parser_AST.aqual uu____5518 t phi in
          soft_parens_with_nesting uu____5517
      | FStar_Parser_AST.TAnnotated uu____5519 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5524 ->
          let uu____5525 =
            let uu____5526 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5526 in
          failwith uu____5525
      | FStar_Parser_AST.TVariable uu____5527 ->
          let uu____5528 =
            let uu____5529 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5529 in
          failwith uu____5528
      | FStar_Parser_AST.NoName uu____5530 ->
          let uu____5531 =
            let uu____5532 = FStar_Parser_AST.binder_to_string b in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5532 in
          failwith uu____5531
and p_simpleDef:
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5533  ->
    match uu____5533 with
    | (lid,e) ->
        let uu____5540 =
          let uu____5541 = p_qlident lid in
          let uu____5542 =
            let uu____5543 = p_tmIff e in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5543 in
          FStar_Pprint.op_Hat_Slash_Hat uu____5541 uu____5542 in
        FStar_Pprint.group uu____5540
and p_appTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5545 =
      let uu____5546 = unparen e in uu____5546.FStar_Parser_AST.tm in
    match uu____5545 with
    | FStar_Parser_AST.App uu____5547 when is_general_application e ->
        let uu____5554 = head_and_args e in
        (match uu____5554 with
         | (head1,args) ->
             let uu____5579 =
               let uu____5590 = FStar_ST.op_Bang should_print_fs_typ_app in
               if uu____5590
               then
                 let uu____5649 =
                   FStar_Util.take
                     (fun uu____5673  ->
                        match uu____5673 with
                        | (uu____5678,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args in
                 match uu____5649 with
                 | (fs_typ_args,args1) ->
                     let uu____5716 =
                       let uu____5717 = p_indexingTerm head1 in
                       let uu____5718 =
                         let uu____5719 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5719 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args in
                       FStar_Pprint.op_Hat_Hat uu____5717 uu____5718 in
                     (uu____5716, args1)
               else
                 (let uu____5731 = p_indexingTerm head1 in (uu____5731, args)) in
             (match uu____5579 with
              | (head_doc,args1) ->
                  let uu____5752 =
                    let uu____5753 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5753 break1
                      FStar_Pprint.empty p_argTerm args1 in
                  FStar_Pprint.group uu____5752))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5773 = is_dtuple_constructor lid in
           Prims.op_Negation uu____5773)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5791 =
               let uu____5792 = p_quident lid in
               let uu____5793 = p_argTerm arg in
               FStar_Pprint.op_Hat_Slash_Hat uu____5792 uu____5793 in
             FStar_Pprint.group uu____5791
         | hd1::tl1 ->
             let uu____5810 =
               let uu____5811 =
                 let uu____5812 =
                   let uu____5813 = p_quident lid in
                   let uu____5814 = p_argTerm hd1 in
                   prefix2 uu____5813 uu____5814 in
                 FStar_Pprint.group uu____5812 in
               let uu____5815 =
                 let uu____5816 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1 in
                 jump2 uu____5816 in
               FStar_Pprint.op_Hat_Hat uu____5811 uu____5815 in
             FStar_Pprint.group uu____5810)
    | uu____5821 -> p_indexingTerm e
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
         (let uu____5830 = p_indexingTerm e in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5830 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5832 = str "#" in
        let uu____5833 = p_indexingTerm e in
        FStar_Pprint.op_Hat_Hat uu____5832 uu____5833
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e
and p_fsTypArg:
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5835  ->
    match uu____5835 with | (e,uu____5841) -> p_indexingTerm e
and p_indexingTerm_aux:
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5846 =
        let uu____5847 = unparen e in uu____5847.FStar_Parser_AST.tm in
      match uu____5846 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5848;_},e1::e2::[])
          ->
          let uu____5853 =
            let uu____5854 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5855 =
              let uu____5856 =
                let uu____5857 = p_term e2 in
                soft_parens_with_nesting uu____5857 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5856 in
            FStar_Pprint.op_Hat_Hat uu____5854 uu____5855 in
          FStar_Pprint.group uu____5853
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5858;_},e1::e2::[])
          ->
          let uu____5863 =
            let uu____5864 = p_indexingTerm_aux p_atomicTermNotQUident e1 in
            let uu____5865 =
              let uu____5866 =
                let uu____5867 = p_term e2 in
                soft_brackets_with_nesting uu____5867 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5866 in
            FStar_Pprint.op_Hat_Hat uu____5864 uu____5865 in
          FStar_Pprint.group uu____5863
      | uu____5868 -> exit1 e
and p_indexingTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e
and p_atomicTerm: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5871 =
      let uu____5872 = unparen e in uu____5872.FStar_Parser_AST.tm in
    match uu____5871 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5875 = p_quident lid in
        let uu____5876 =
          let uu____5877 =
            let uu____5878 = p_term e1 in soft_parens_with_nesting uu____5878 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5877 in
        FStar_Pprint.op_Hat_Hat uu____5875 uu____5876
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5884 = str (FStar_Ident.text_of_id op) in
        let uu____5885 = p_atomicTerm e1 in
        FStar_Pprint.op_Hat_Hat uu____5884 uu____5885
    | uu____5886 -> p_atomicTermNotQUident e
and p_atomicTermNotQUident: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5888 =
      let uu____5889 = unparen e in uu____5889.FStar_Parser_AST.tm in
    match uu____5888 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5895 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5902 = str (FStar_Ident.text_of_id op) in
        let uu____5903 = p_atomicTermNotQUident e1 in
        FStar_Pprint.op_Hat_Hat uu____5902 uu____5903
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5907 =
          let uu____5908 =
            let uu____5909 = str (FStar_Ident.text_of_id op) in
            let uu____5910 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen in
            FStar_Pprint.op_Hat_Hat uu____5909 uu____5910 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5908 in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5907
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5925 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar in
        let uu____5926 =
          let uu____5927 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          let uu____5928 = FStar_List.map FStar_Pervasives_Native.fst args in
          FStar_Pprint.separate_map uu____5927 p_tmEq uu____5928 in
        let uu____5935 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5925 uu____5926 uu____5935
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5938 =
          let uu____5939 = p_atomicTermNotQUident e1 in
          let uu____5940 =
            let uu____5941 = p_qlident lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5941 in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5939 uu____5940 in
        FStar_Pprint.group uu____5938
    | uu____5942 -> p_projectionLHS e
and p_projectionLHS: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5944 =
      let uu____5945 = unparen e in uu____5945.FStar_Parser_AST.tm in
    match uu____5944 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5949 = p_quident constr_lid in
        let uu____5950 =
          let uu____5951 =
            let uu____5952 = p_lident field_lid in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5952 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5951 in
        FStar_Pprint.op_Hat_Hat uu____5949 uu____5950
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5954 = p_quident constr_lid in
        FStar_Pprint.op_Hat_Hat uu____5954 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5956 = p_term e1 in soft_parens_with_nesting uu____5956
    | uu____5957 when is_array e ->
        let es = extract_from_list e in
        let uu____5961 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar in
        let uu____5962 =
          let uu____5963 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          separate_map_or_flow uu____5963 p_noSeqTerm es in
        let uu____5964 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5961 uu____5962 uu____5964
    | uu____5965 when is_list e ->
        let uu____5966 =
          let uu____5967 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5968 = extract_from_list e in
          separate_map_or_flow uu____5967 p_noSeqTerm uu____5968 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5966 FStar_Pprint.rbracket
    | uu____5971 when is_lex_list e ->
        let uu____5972 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket in
        let uu____5973 =
          let uu____5974 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1 in
          let uu____5975 = extract_from_list e in
          separate_map_or_flow uu____5974 p_noSeqTerm uu____5975 in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5972 uu____5973 FStar_Pprint.rbracket
    | uu____5978 when is_ref_set e ->
        let es = extract_from_ref_set e in
        let uu____5982 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace in
        let uu____5983 =
          let uu____5984 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1 in
          separate_map_or_flow uu____5984 p_appTerm es in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5982 uu____5983 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5988 = str (Prims.strcat "(*" (Prims.strcat s "*)")) in
        let uu____5989 = p_term e1 in
        FStar_Pprint.op_Hat_Slash_Hat uu____5988 uu____5989
    | FStar_Parser_AST.Op (op,args) when
        let uu____5996 = handleable_op op args in
        Prims.op_Negation uu____5996 ->
        let uu____5997 =
          let uu____5998 =
            let uu____5999 =
              let uu____6000 =
                let uu____6001 =
                  FStar_Util.string_of_int (FStar_List.length args) in
                Prims.strcat uu____6001
                  " arguments couldn't be handled by the pretty printer" in
              Prims.strcat " with " uu____6000 in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5999 in
          Prims.strcat "Operation " uu____5998 in
        failwith uu____5997
    | FStar_Parser_AST.Uvar uu____6002 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6003 = p_term e in soft_parens_with_nesting uu____6003
    | FStar_Parser_AST.Const uu____6004 ->
        let uu____6005 = p_term e in soft_parens_with_nesting uu____6005
    | FStar_Parser_AST.Op uu____6006 ->
        let uu____6013 = p_term e in soft_parens_with_nesting uu____6013
    | FStar_Parser_AST.Tvar uu____6014 ->
        let uu____6015 = p_term e in soft_parens_with_nesting uu____6015
    | FStar_Parser_AST.Var uu____6016 ->
        let uu____6017 = p_term e in soft_parens_with_nesting uu____6017
    | FStar_Parser_AST.Name uu____6018 ->
        let uu____6019 = p_term e in soft_parens_with_nesting uu____6019
    | FStar_Parser_AST.Construct uu____6020 ->
        let uu____6031 = p_term e in soft_parens_with_nesting uu____6031
    | FStar_Parser_AST.Abs uu____6032 ->
        let uu____6039 = p_term e in soft_parens_with_nesting uu____6039
    | FStar_Parser_AST.App uu____6040 ->
        let uu____6047 = p_term e in soft_parens_with_nesting uu____6047
    | FStar_Parser_AST.Let uu____6048 ->
        let uu____6061 = p_term e in soft_parens_with_nesting uu____6061
    | FStar_Parser_AST.LetOpen uu____6062 ->
        let uu____6067 = p_term e in soft_parens_with_nesting uu____6067
    | FStar_Parser_AST.Seq uu____6068 ->
        let uu____6073 = p_term e in soft_parens_with_nesting uu____6073
    | FStar_Parser_AST.Bind uu____6074 ->
        let uu____6081 = p_term e in soft_parens_with_nesting uu____6081
    | FStar_Parser_AST.If uu____6082 ->
        let uu____6089 = p_term e in soft_parens_with_nesting uu____6089
    | FStar_Parser_AST.Match uu____6090 ->
        let uu____6105 = p_term e in soft_parens_with_nesting uu____6105
    | FStar_Parser_AST.TryWith uu____6106 ->
        let uu____6121 = p_term e in soft_parens_with_nesting uu____6121
    | FStar_Parser_AST.Ascribed uu____6122 ->
        let uu____6131 = p_term e in soft_parens_with_nesting uu____6131
    | FStar_Parser_AST.Record uu____6132 ->
        let uu____6145 = p_term e in soft_parens_with_nesting uu____6145
    | FStar_Parser_AST.Project uu____6146 ->
        let uu____6151 = p_term e in soft_parens_with_nesting uu____6151
    | FStar_Parser_AST.Product uu____6152 ->
        let uu____6159 = p_term e in soft_parens_with_nesting uu____6159
    | FStar_Parser_AST.Sum uu____6160 ->
        let uu____6167 = p_term e in soft_parens_with_nesting uu____6167
    | FStar_Parser_AST.QForall uu____6168 ->
        let uu____6181 = p_term e in soft_parens_with_nesting uu____6181
    | FStar_Parser_AST.QExists uu____6182 ->
        let uu____6195 = p_term e in soft_parens_with_nesting uu____6195
    | FStar_Parser_AST.Refine uu____6196 ->
        let uu____6201 = p_term e in soft_parens_with_nesting uu____6201
    | FStar_Parser_AST.NamedTyp uu____6202 ->
        let uu____6207 = p_term e in soft_parens_with_nesting uu____6207
    | FStar_Parser_AST.Requires uu____6208 ->
        let uu____6215 = p_term e in soft_parens_with_nesting uu____6215
    | FStar_Parser_AST.Ensures uu____6216 ->
        let uu____6223 = p_term e in soft_parens_with_nesting uu____6223
    | FStar_Parser_AST.Assign uu____6224 ->
        let uu____6229 = p_term e in soft_parens_with_nesting uu____6229
    | FStar_Parser_AST.Attributes uu____6230 ->
        let uu____6233 = p_term e in soft_parens_with_nesting uu____6233
and p_constant: FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___61_6234  ->
    match uu___61_6234 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6238 = FStar_Pprint.doc_of_char x in
        FStar_Pprint.squotes uu____6238
    | FStar_Const.Const_string (s,uu____6240) ->
        let uu____6241 = str s in FStar_Pprint.dquotes uu____6241
    | FStar_Const.Const_bytearray (bytes,uu____6243) ->
        let uu____6248 =
          let uu____6249 = str (FStar_Util.string_of_bytes bytes) in
          FStar_Pprint.dquotes uu____6249 in
        let uu____6250 = str "B" in
        FStar_Pprint.op_Hat_Hat uu____6248 uu____6250
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___59_6268 =
          match uu___59_6268 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty in
        let width uu___60_6272 =
          match uu___60_6272 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L" in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6283  ->
               match uu____6283 with
               | (s,w) ->
                   let uu____6290 = signedness s in
                   let uu____6291 = width w in
                   FStar_Pprint.op_Hat_Hat uu____6290 uu____6291)
            sign_width_opt in
        let uu____6292 = str repr in
        FStar_Pprint.op_Hat_Hat uu____6292 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6294 = FStar_Range.string_of_range r in str uu____6294
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6296 = p_quident lid in
        let uu____6297 =
          let uu____6298 =
            let uu____6299 = str "reflect" in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6299 in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6298 in
        FStar_Pprint.op_Hat_Hat uu____6296 uu____6297
and p_universe: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6301 = str "u#" in
    let uu____6302 = p_atomicUniverse u in
    FStar_Pprint.op_Hat_Hat uu____6301 uu____6302
and p_universeFrom: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6304 =
      let uu____6305 = unparen u in uu____6305.FStar_Parser_AST.tm in
    match uu____6304 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6306;_},u1::u2::[])
        ->
        let uu____6311 =
          let uu____6312 = p_universeFrom u1 in
          let uu____6313 =
            let uu____6314 = p_universeFrom u2 in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6314 in
          FStar_Pprint.op_Hat_Slash_Hat uu____6312 uu____6313 in
        FStar_Pprint.group uu____6311
    | FStar_Parser_AST.App uu____6315 ->
        let uu____6322 = head_and_args u in
        (match uu____6322 with
         | (head1,args) ->
             let uu____6347 =
               let uu____6348 = unparen head1 in
               uu____6348.FStar_Parser_AST.tm in
             (match uu____6347 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6350 =
                    let uu____6351 = p_qlident FStar_Parser_Const.max_lid in
                    let uu____6352 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6360  ->
                           match uu____6360 with
                           | (u1,uu____6366) -> p_atomicUniverse u1) args in
                    op_Hat_Slash_Plus_Hat uu____6351 uu____6352 in
                  FStar_Pprint.group uu____6350
              | uu____6367 ->
                  let uu____6368 =
                    let uu____6369 = FStar_Parser_AST.term_to_string u in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6369 in
                  failwith uu____6368))
    | uu____6370 -> p_atomicUniverse u
and p_atomicUniverse: FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6372 =
      let uu____6373 = unparen u in uu____6373.FStar_Parser_AST.tm in
    match uu____6372 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6396 = p_universeFrom u1 in
        soft_parens_with_nesting uu____6396
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6397;_},uu____6398::uu____6399::[])
        ->
        let uu____6402 = p_universeFrom u in
        soft_parens_with_nesting uu____6402
    | FStar_Parser_AST.App uu____6403 ->
        let uu____6410 = p_universeFrom u in
        soft_parens_with_nesting uu____6410
    | uu____6411 ->
        let uu____6412 =
          let uu____6413 = FStar_Parser_AST.term_to_string u in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6413 in
        failwith uu____6412
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
       | FStar_Parser_AST.Module (uu____6482,decls) ->
           let uu____6488 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6488
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6497,decls,uu____6499) ->
           let uu____6504 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document) in
           FStar_All.pipe_right uu____6504
             (FStar_Pprint.separate FStar_Pprint.hardline) in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
let comments_to_document:
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6584  ->
         match uu____6584 with | (comment,range) -> str comment) comments
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
        | FStar_Parser_AST.Module (uu____6624,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6630,decls,uu____6632) -> decls in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6706 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6719;
                 FStar_Parser_AST.doc = uu____6720;
                 FStar_Parser_AST.quals = uu____6721;
                 FStar_Parser_AST.attrs = uu____6722;_}::uu____6723 ->
                 let d0 = FStar_List.hd ds in
                 let uu____6729 =
                   let uu____6732 =
                     let uu____6735 = FStar_List.tl ds in d :: uu____6735 in
                   d0 :: uu____6732 in
                 (uu____6729, (d0.FStar_Parser_AST.drange))
             | uu____6740 -> ((d :: ds), (d.FStar_Parser_AST.drange)) in
           (match uu____6706 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6827 = FStar_Range.start_of_range first_range in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6827 FStar_Pprint.empty in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range in
                  let comments1 = FStar_ST.op_Bang comment_stack in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7010 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1 in
                   (uu____7010, comments1))))))