open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.bool)
  =
  fun args  ->
    FStar_Util.for_all
      (fun uu___110_83  ->
         match uu___110_83 with
         | (uu____89,FStar_Parser_AST.Nothing ) -> true
         | uu____91 -> false) args
  
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____125 'Auu____126 .
    Prims.bool -> ('Auu____125 -> 'Auu____126) -> 'Auu____125 -> 'Auu____126
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let (str : Prims.string -> FStar_Pprint.document) =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____236 'Auu____237 .
    'Auu____236 ->
      ('Auu____237 -> 'Auu____236) ->
        'Auu____237 FStar_Pervasives_Native.option -> 'Auu____236
  =
  fun n1  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n1
        | FStar_Pervasives_Native.Some x' -> f x'
  
let (prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let (break1 : FStar_Pprint.document) =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map :
  'Auu____350 .
    FStar_Pprint.document ->
      ('Auu____350 -> FStar_Pprint.document) ->
        'Auu____350 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____375 =
          let uu____376 =
            let uu____377 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____377  in
          FStar_Pprint.separate_map uu____376 f l  in
        FStar_Pprint.group uu____375
  
let precede_break_separate_map :
  'Auu____389 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____389 -> FStar_Pprint.document) ->
          'Auu____389 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____419 =
            let uu____420 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____421 =
              let uu____422 = FStar_List.hd l  in
              FStar_All.pipe_right uu____422 f  in
            FStar_Pprint.precede uu____420 uu____421  in
          let uu____423 =
            let uu____424 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____430 =
                   let uu____431 =
                     let uu____432 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____432  in
                   FStar_Pprint.op_Hat_Hat sep uu____431  in
                 FStar_Pprint.op_Hat_Hat break1 uu____430) uu____424
             in
          FStar_Pprint.op_Hat_Hat uu____419 uu____423
  
let concat_break_map :
  'Auu____440 .
    ('Auu____440 -> FStar_Pprint.document) ->
      'Auu____440 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____460 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____464 = f x  in FStar_Pprint.op_Hat_Hat uu____464 break1)
          l
         in
      FStar_Pprint.group uu____460
  
let (parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    let uu____527 = str "begin"  in
    let uu____529 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____527 contents uu____529
  
let separate_map_last :
  'Auu____542 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____542 -> FStar_Pprint.document) ->
        'Auu____542 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.separate sep es1
  
let separate_break_map_last :
  'Auu____600 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____600 -> FStar_Pprint.document) ->
        'Auu____600 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____632 =
          let uu____633 =
            let uu____634 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____634  in
          separate_map_last uu____633 f l  in
        FStar_Pprint.group uu____632
  
let separate_map_or_flow :
  'Auu____644 .
    FStar_Pprint.document ->
      ('Auu____644 -> FStar_Pprint.document) ->
        'Auu____644 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____682 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____682 -> FStar_Pprint.document) ->
        'Auu____682 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun es  ->
        let l = FStar_List.length es  in
        let es1 =
          FStar_List.mapi
            (fun i  -> fun e  -> f (i <> (l - (Prims.parse_int "1"))) e) es
           in
        FStar_Pprint.flow sep es1
  
let separate_map_or_flow_last :
  'Auu____740 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____740 -> FStar_Pprint.document) ->
        'Auu____740 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep  -> fun l  -> separate_map_or_flow sep FStar_Pervasives.id l 
let (surround_maybe_empty :
  Prims.int ->
    Prims.int ->
      FStar_Pprint.document ->
        FStar_Pprint.document ->
          FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun n1  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____822 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____822
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____844 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____844 -> FStar_Pprint.document) ->
                  'Auu____844 Prims.list -> FStar_Pprint.document
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
                    (let uu____903 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____903
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____923 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____923 -> FStar_Pprint.document) ->
                  'Auu____923 Prims.list -> FStar_Pprint.document
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
                    (let uu____982 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____982
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____1001  ->
    match uu____1001 with
    | (comment,keywords) ->
        let uu____1035 =
          let uu____1036 =
            let uu____1039 = str comment  in
            let uu____1040 =
              let uu____1043 =
                let uu____1046 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1057  ->
                       match uu____1057 with
                       | (k,v1) ->
                           let uu____1070 =
                             let uu____1073 = str k  in
                             let uu____1074 =
                               let uu____1077 =
                                 let uu____1080 = str v1  in [uu____1080]  in
                               FStar_Pprint.rarrow :: uu____1077  in
                             uu____1073 :: uu____1074  in
                           FStar_Pprint.concat uu____1070) keywords
                   in
                [uu____1046]  in
              FStar_Pprint.space :: uu____1043  in
            uu____1039 :: uu____1040  in
          FStar_Pprint.concat uu____1036  in
        FStar_Pprint.group uu____1035
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1090 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1106 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1106
      | uu____1109 -> false
  
let (is_tuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_tuple_data_lid' 
let (is_dtuple_constructor : FStar_Ident.lident -> Prims.bool) =
  FStar_Parser_Const.is_dtuple_data_lid' 
let (is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool)
  =
  fun cons_lid1  ->
    fun nil_lid1  ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____1160::(e2,uu____1162)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1185 -> false  in
      aux
  
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (uu____1209,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1220,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1241 = extract_from_list e2  in e1 :: uu____1241
    | uu____1244 ->
        let uu____1245 =
          let uu____1247 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1247  in
        failwith uu____1245
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1261;
           FStar_Parser_AST.level = uu____1262;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1264 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1276;
           FStar_Parser_AST.level = uu____1277;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1279;
                                                         FStar_Parser_AST.level
                                                           = uu____1280;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1282;
                                                    FStar_Parser_AST.level =
                                                      uu____1283;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1285;
                FStar_Parser_AST.level = uu____1286;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1288;
           FStar_Parser_AST.level = uu____1289;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1291 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1303 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1304;
           FStar_Parser_AST.range = uu____1305;
           FStar_Parser_AST.level = uu____1306;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1307;
                                                         FStar_Parser_AST.range
                                                           = uu____1308;
                                                         FStar_Parser_AST.level
                                                           = uu____1309;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1311;
                                                    FStar_Parser_AST.level =
                                                      uu____1312;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1313;
                FStar_Parser_AST.range = uu____1314;
                FStar_Parser_AST.level = uu____1315;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1317;
           FStar_Parser_AST.level = uu____1318;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1320 = extract_from_ref_set e1  in
        let uu____1323 = extract_from_ref_set e2  in
        FStar_List.append uu____1320 uu____1323
    | uu____1326 ->
        let uu____1327 =
          let uu____1329 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1329  in
        failwith uu____1327
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1341 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1341
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1350 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1350
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1361 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1361 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1371 = FStar_Ident.text_of_id op  in uu____1371 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1441 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1461 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1472 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1483 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___111_1509  ->
    match uu___111_1509 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___112_1544  ->
      match uu___112_1544 with
      | FStar_Util.Inl c ->
          let uu____1557 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1557 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1573 .
    Prims.string ->
      ('Auu____1573,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1597  ->
      match uu____1597 with
      | (assoc_levels,tokens) ->
          let uu____1629 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1629 <> FStar_Pervasives_Native.None
  
let (opinfix4 : associativity_level) = (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 : associativity_level) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 : associativity_level) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl : associativity_level) = (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 : associativity_level) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right : associativity_level) = (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d : associativity_level) = (Left, [FStar_Util.Inl 36]) 
let (opinfix0c : associativity_level) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : associativity_level) = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b : associativity_level) = (Left, [FStar_Util.Inl 38]) 
let (opinfix0a : associativity_level) = (Left, [FStar_Util.Inl 124]) 
let (colon_equals : associativity_level) = (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : associativity_level) = (Right, [FStar_Util.Inr "&"]) 
let (colon_colon : associativity_level) = (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec : associativity_level Prims.list) =
  [opinfix4;
  opinfix3;
  opinfix2;
  opinfix1;
  pipe_right;
  opinfix0d;
  opinfix0c;
  opinfix0b;
  opinfix0a;
  colon_equals;
  amp;
  colon_colon] 
let (level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,token
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___113_1801 =
    match uu___113_1801 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1851  ->
         match uu____1851 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1926 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1926 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1978) ->
          assoc_levels
      | uu____2016 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____2049 .
    ('Auu____2049,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2098 =
        FStar_List.tryFind
          (fun uu____2134  ->
             match uu____2134 with
             | (uu____2151,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2098 with
      | FStar_Pervasives_Native.Some ((uu____2180,l1,uu____2182),uu____2183)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2233 =
            let uu____2235 =
              let uu____2237 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2237  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2235
             in
          failwith uu____2233
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2272 = assign_levels level_associativity_spec op  in
    match uu____2272 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2331 =
      let uu____2334 =
        let uu____2340 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2340  in
      FStar_List.tryFind uu____2334 operatorInfix0ad12  in
    uu____2331 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2407 =
      let uu____2422 =
        let uu____2440 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2440  in
      FStar_List.tryFind uu____2422 opinfix34  in
    uu____2407 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2506 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2506
    then (Prims.parse_int "1")
    else
      (let uu____2519 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2519
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2565 . FStar_Ident.ident -> 'Auu____2565 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2583 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2583 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2592 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2592
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2614 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2614 [".()<-"; ".[]<-"]
      | uu____2622 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool ;
  has_fsdoc: Prims.bool ;
  is_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> has_fsdoc
  
let (__proj__Mkdecl_meta__item__is_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r; has_qs; has_attrs; has_fsdoc; is_fsdoc;_} -> is_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false;
    is_fsdoc = false
  } 
let with_comment :
  'Auu____2787 'Auu____2788 .
    ('Auu____2787 -> FStar_Pprint.document) ->
      'Auu____2787 ->
        FStar_Range.range -> 'Auu____2788 -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____2835 = FStar_ST.op_Bang comment_stack  in
            match uu____2835 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment =
                  if FStar_Util.starts_with c "//"
                  then
                    let uu____2908 = str c  in
                    FStar_Pprint.op_Hat_Hat uu____2908 FStar_Pprint.hardline
                  else
                    (let uu____2911 = str c  in
                     FStar_Pprint.op_Hat_Hat uu____2911 FStar_Pprint.hardline)
                   in
                let uu____2912 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____2912
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____2954 = FStar_Pprint.op_Hat_Hat acc comment  in
                    comments_before_pos uu____2954 print_pos lookahead_pos))
                else
                  (let uu____2957 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____2957))
             in
          let uu____2960 =
            let uu____2966 =
              let uu____2967 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____2967  in
            let uu____2968 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____2966 uu____2968  in
          match uu____2960 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____2977 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____2977
                else comments  in
              if comments1 = FStar_Pprint.empty
              then printed_e
              else
                (let uu____2989 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                    in
                 FStar_Pprint.group uu____2989)
  
let with_comment_sep :
  'Auu____3005 'Auu____3006 'Auu____3007 .
    ('Auu____3005 -> 'Auu____3006) ->
      'Auu____3005 ->
        FStar_Range.range ->
          'Auu____3007 ->
            (FStar_Pprint.document,'Auu____3006)
              FStar_Pervasives_Native.tuple2
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____3058 = FStar_ST.op_Bang comment_stack  in
            match uu____3058 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment = str c  in
                let uu____3129 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____3129
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____3171 =
                      if acc = FStar_Pprint.empty
                      then comment
                      else
                        (let uu____3175 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             comment
                            in
                         FStar_Pprint.op_Hat_Hat acc uu____3175)
                       in
                    comments_before_pos uu____3171 print_pos lookahead_pos))
                else
                  (let uu____3178 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____3178))
             in
          let uu____3181 =
            let uu____3187 =
              let uu____3188 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____3188  in
            let uu____3189 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____3187 uu____3189  in
          match uu____3181 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____3202 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____3202
                else comments  in
              (comments1, printed_e)
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos  ->
        fun meta_decl  ->
          fun doc1  ->
            fun r  ->
              fun init1  ->
                let uu____3255 = FStar_ST.op_Bang comment_stack  in
                match uu____3255 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3349 =
                          let uu____3351 =
                            let uu____3353 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3353  in
                          uu____3351 - lbegin  in
                        max k uu____3349  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3358 =
                          let uu____3359 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3360 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3359 uu____3360  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3358  in
                      let uu____3361 =
                        let uu____3363 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3363  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3361 pos meta_decl doc2 true init1))
                | uu____3366 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3379 = FStar_Range.line_of_pos pos  in
                         uu____3379 - lbegin  in
                       let lnum1 = min (Prims.parse_int "3") lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - (Prims.parse_int "1")
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.parse_int "2")
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.parse_int "2") lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then (Prims.parse_int "1")
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.parse_int "2") else lnum6  in
                       let uu____3421 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3421)
  
let separate_map_with_comments :
  'Auu____3435 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3435 -> FStar_Pprint.document) ->
          'Auu____3435 Prims.list ->
            ('Auu____3435 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3494 x =
              match uu____3494 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3513 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3513 meta_decl doc1 false false
                     in
                  let uu____3517 =
                    let uu____3519 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3519  in
                  let uu____3520 =
                    let uu____3521 =
                      let uu____3522 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3522  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3521  in
                  (uu____3517, uu____3520)
               in
            let uu____3524 =
              let uu____3531 = FStar_List.hd xs  in
              let uu____3532 = FStar_List.tl xs  in (uu____3531, uu____3532)
               in
            match uu____3524 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3550 =
                    let uu____3552 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3552  in
                  let uu____3553 =
                    let uu____3554 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3554  in
                  (uu____3550, uu____3553)  in
                let uu____3556 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3556
  
let separate_map_with_comments_kw :
  'Auu____3583 'Auu____3584 .
    'Auu____3583 ->
      'Auu____3583 ->
        ('Auu____3583 -> 'Auu____3584 -> FStar_Pprint.document) ->
          'Auu____3584 Prims.list ->
            ('Auu____3584 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3648 x =
              match uu____3648 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3667 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3667 meta_decl doc1 false false
                     in
                  let uu____3671 =
                    let uu____3673 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3673  in
                  let uu____3674 =
                    let uu____3675 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3675  in
                  (uu____3671, uu____3674)
               in
            let uu____3677 =
              let uu____3684 = FStar_List.hd xs  in
              let uu____3685 = FStar_List.tl xs  in (uu____3684, uu____3685)
               in
            match uu____3677 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3703 =
                    let uu____3705 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3705  in
                  let uu____3706 = f prefix1 x  in (uu____3703, uu____3706)
                   in
                let uu____3708 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3708
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4528)) ->
          let uu____4531 =
            let uu____4533 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4533 FStar_Util.is_upper  in
          if uu____4531
          then
            let uu____4539 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4539 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4542 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4549 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____4552 =
      let uu____4553 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4554 =
        let uu____4555 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4555  in
      FStar_Pprint.op_Hat_Hat uu____4553 uu____4554  in
    FStar_Pprint.op_Hat_Hat uu____4549 uu____4552

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4557 ->
        let uu____4558 =
          let uu____4559 = str "@ "  in
          let uu____4561 =
            let uu____4562 =
              let uu____4563 =
                let uu____4564 =
                  let uu____4565 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4565  in
                FStar_Pprint.op_Hat_Hat uu____4564 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4563  in
            FStar_Pprint.op_Hat_Hat uu____4562 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4559 uu____4561  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4558

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4568  ->
    match uu____4568 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4616 =
                match uu____4616 with
                | (kwd,arg) ->
                    let uu____4629 = str "@"  in
                    let uu____4631 =
                      let uu____4632 = str kwd  in
                      let uu____4633 =
                        let uu____4634 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4634
                         in
                      FStar_Pprint.op_Hat_Hat uu____4632 uu____4633  in
                    FStar_Pprint.op_Hat_Hat uu____4629 uu____4631
                 in
              let uu____4635 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____4635 FStar_Pprint.hardline
           in
        let uu____4642 =
          let uu____4643 =
            let uu____4644 =
              let uu____4645 = str doc1  in
              let uu____4646 =
                let uu____4647 =
                  let uu____4648 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4648  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4647  in
              FStar_Pprint.op_Hat_Hat uu____4645 uu____4646  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4644  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4643  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4642

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4652 =
          let uu____4653 = str "val"  in
          let uu____4655 =
            let uu____4656 =
              let uu____4657 = p_lident lid  in
              let uu____4658 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4657 uu____4658  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4656  in
          FStar_Pprint.op_Hat_Hat uu____4653 uu____4655  in
        let uu____4659 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4652 uu____4659
    | FStar_Parser_AST.TopLevelLet (uu____4662,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4687 =
               let uu____4688 = str "let"  in p_letlhs uu____4688 lb  in
             FStar_Pprint.group uu____4687) lbs
    | uu____4690 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_4705 =
          match uu___114_4705 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4713 = f x  in
              let uu____4714 =
                let uu____4715 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4715  in
              FStar_Pprint.op_Hat_Hat uu____4713 uu____4714
           in
        let uu____4716 = str "["  in
        let uu____4718 =
          let uu____4719 = p_list' l  in
          let uu____4720 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4719 uu____4720  in
        FStar_Pprint.op_Hat_Hat uu____4716 uu____4718

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4724 =
          let uu____4725 = str "open"  in
          let uu____4727 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4725 uu____4727  in
        FStar_Pprint.group uu____4724
    | FStar_Parser_AST.Include uid ->
        let uu____4729 =
          let uu____4730 = str "include"  in
          let uu____4732 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4730 uu____4732  in
        FStar_Pprint.group uu____4729
    | FStar_Parser_AST.Friend uid ->
        let uu____4734 =
          let uu____4735 = str "friend"  in
          let uu____4737 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4735 uu____4737  in
        FStar_Pprint.group uu____4734
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4740 =
          let uu____4741 = str "module"  in
          let uu____4743 =
            let uu____4744 =
              let uu____4745 = p_uident uid1  in
              let uu____4746 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4745 uu____4746  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4744  in
          FStar_Pprint.op_Hat_Hat uu____4741 uu____4743  in
        let uu____4747 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4740 uu____4747
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4749 =
          let uu____4750 = str "module"  in
          let uu____4752 =
            let uu____4753 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4753  in
          FStar_Pprint.op_Hat_Hat uu____4750 uu____4752  in
        FStar_Pprint.group uu____4749
    | FStar_Parser_AST.Tycon
        (true
         ,uu____4754,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____4791 = str "effect"  in
          let uu____4793 =
            let uu____4794 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4794  in
          FStar_Pprint.op_Hat_Hat uu____4791 uu____4793  in
        let uu____4795 =
          let uu____4796 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4796 FStar_Pprint.equals
           in
        let uu____4799 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4795 uu____4799
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____4830 =
          let uu____4831 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____4831  in
        let uu____4844 =
          let uu____4845 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4883 =
                    let uu____4884 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4884 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4883)) uu____4845
           in
        FStar_Pprint.op_Hat_Hat uu____4830 uu____4844
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4901 = str "let"  in
          let uu____4903 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4901 uu____4903  in
        let uu____4904 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4904 p_letbinding lbs
          (fun uu____4914  ->
             match uu____4914 with
             | (p,t) ->
                 let uu____4921 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____4921;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4927 = str "val"  in
        let uu____4929 =
          let uu____4930 =
            let uu____4931 = p_lident lid  in
            let uu____4932 =
              let uu____4933 =
                let uu____4934 =
                  let uu____4935 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4935  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4934  in
              FStar_Pprint.group uu____4933  in
            FStar_Pprint.op_Hat_Hat uu____4931 uu____4932  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4930  in
        FStar_Pprint.op_Hat_Hat uu____4927 uu____4929
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4941 =
            let uu____4943 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4943 FStar_Util.is_upper  in
          if uu____4941
          then FStar_Pprint.empty
          else
            (let uu____4951 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4951 FStar_Pprint.space)
           in
        let uu____4953 =
          let uu____4954 = p_ident id1  in
          let uu____4955 =
            let uu____4956 =
              let uu____4957 =
                let uu____4958 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4958  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4957  in
            FStar_Pprint.group uu____4956  in
          FStar_Pprint.op_Hat_Hat uu____4954 uu____4955  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4953
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4967 = str "exception"  in
        let uu____4969 =
          let uu____4970 =
            let uu____4971 = p_uident uid  in
            let uu____4972 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4976 =
                     let uu____4977 = str "of"  in
                     let uu____4979 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4977 uu____4979  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4976) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4971 uu____4972  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4970  in
        FStar_Pprint.op_Hat_Hat uu____4967 uu____4969
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4983 = str "new_effect"  in
        let uu____4985 =
          let uu____4986 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4986  in
        FStar_Pprint.op_Hat_Hat uu____4983 uu____4985
    | FStar_Parser_AST.SubEffect se ->
        let uu____4988 = str "sub_effect"  in
        let uu____4990 =
          let uu____4991 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4991  in
        FStar_Pprint.op_Hat_Hat uu____4988 uu____4990
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____4994 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4996,uu____4997) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5025 = str "%splice"  in
        let uu____5027 =
          let uu____5028 =
            let uu____5029 = str ";"  in p_list p_uident uu____5029 ids  in
          let uu____5031 =
            let uu____5032 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5032  in
          FStar_Pprint.op_Hat_Hat uu____5028 uu____5031  in
        FStar_Pprint.op_Hat_Hat uu____5025 uu____5027

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_5035  ->
    match uu___115_5035 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5038 = str "#set-options"  in
        let uu____5040 =
          let uu____5041 =
            let uu____5042 = str s  in FStar_Pprint.dquotes uu____5042  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5041  in
        FStar_Pprint.op_Hat_Hat uu____5038 uu____5040
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5047 = str "#reset-options"  in
        let uu____5049 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5055 =
                 let uu____5056 = str s  in FStar_Pprint.dquotes uu____5056
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5055) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5047 uu____5049
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5061 = str "#push-options"  in
        let uu____5063 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5069 =
                 let uu____5070 = str s  in FStar_Pprint.dquotes uu____5070
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5069) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5061 uu____5063
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5101  ->
      match uu____5101 with
      | (typedecl,fsdoc_opt) ->
          let uu____5114 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5114 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5139 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5139
               else
                 (let uu____5142 =
                    let uu____5143 =
                      let uu____5144 =
                        let uu____5145 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5145 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5144  in
                    let uu____5146 =
                      let uu____5147 =
                        let uu____5148 =
                          let uu____5149 =
                            let uu____5150 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5150  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5149
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5148
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5147  in
                    FStar_Pprint.ifflat uu____5143 uu____5146  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5142))

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,FStar_Pprint.document,FStar_Pprint.document,
        FStar_Pprint.document -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple4)
  =
  fun pre  ->
    fun uu___116_5153  ->
      match uu___116_5153 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5182 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5182, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5199 = p_typ_sep false false t  in
          (match uu____5199 with
           | (comm,doc1) ->
               let uu____5219 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5219, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5275 =
            match uu____5275 with
            | (lid1,t,doc_opt) ->
                let uu____5292 =
                  let uu____5297 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5297 "!1"
                   in
                (match uu____5292 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5317 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5317  in
          let uu____5326 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5326, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5393 =
            match uu____5393 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5422 =
                    let uu____5423 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5423  in
                  FStar_Range.extend_to_end_of_line uu____5422  in
                let uu____5428 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range "!2"
                   in
                (match uu____5428 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5469 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5469, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____5474  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____5474 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____5509 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____5509  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____5511 =
                        let uu____5514 =
                          let uu____5517 = p_fsdoc fsdoc  in
                          let uu____5518 =
                            let uu____5521 = cont lid_doc  in [uu____5521]
                             in
                          uu____5517 :: uu____5518  in
                        kw :: uu____5514  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____5511
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____5528 =
                        let uu____5529 =
                          let uu____5530 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5530 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5529
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5528
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5550 =
                          let uu____5551 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5551  in
                        prefix2 uu____5550 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5553  ->
      match uu____5553 with
      | (lid,t,doc_opt) ->
          let uu____5570 =
            let uu____5571 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5572 =
              let uu____5573 = p_lident lid  in
              let uu____5574 =
                let uu____5575 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5575  in
              FStar_Pprint.op_Hat_Hat uu____5573 uu____5574  in
            FStar_Pprint.op_Hat_Hat uu____5571 uu____5572  in
          FStar_Pprint.group uu____5570

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____5577  ->
    match uu____5577 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5611 =
            let uu____5612 =
              let uu____5613 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5613  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5612  in
          FStar_Pprint.group uu____5611  in
        let uu____5614 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5615 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5619 =
                 let uu____5620 =
                   let uu____5621 =
                     let uu____5622 =
                       let uu____5623 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5623
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5622  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5621  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5620  in
               FStar_Pprint.group uu____5619) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5614 uu____5615

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5627  ->
      match uu____5627 with
      | (pat,uu____5633) ->
          let uu____5634 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5653 =
                  let uu____5654 =
                    let uu____5655 =
                      let uu____5656 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5655  in
                  FStar_Pprint.group uu____5654  in
                (pat1, uu____5653)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5668 =
                  let uu____5669 =
                    let uu____5670 =
                      let uu____5671 =
                        let uu____5672 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5672
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5671
                       in
                    FStar_Pprint.group uu____5670  in
                  let uu____5673 =
                    let uu____5674 =
                      let uu____5675 = str "by"  in
                      let uu____5677 =
                        let uu____5678 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5678
                         in
                      FStar_Pprint.op_Hat_Hat uu____5675 uu____5677  in
                    FStar_Pprint.group uu____5674  in
                  FStar_Pprint.op_Hat_Hat uu____5669 uu____5673  in
                (pat1, uu____5668)
            | uu____5679 -> (pat, FStar_Pprint.empty)  in
          (match uu____5634 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5683);
                       FStar_Parser_AST.prange = uu____5684;_},pats)
                    ->
                    let uu____5694 =
                      let uu____5695 =
                        let uu____5696 =
                          let uu____5697 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5697  in
                        FStar_Pprint.group uu____5696  in
                      let uu____5698 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5695 uu____5698  in
                    prefix2_nonempty uu____5694 ascr_doc
                | uu____5699 ->
                    let uu____5700 =
                      let uu____5701 =
                        let uu____5702 =
                          let uu____5703 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5703  in
                        FStar_Pprint.group uu____5702  in
                      FStar_Pprint.op_Hat_Hat uu____5701 ascr_doc  in
                    FStar_Pprint.group uu____5700))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5705  ->
      match uu____5705 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let uu____5713 = p_term_sep false false e  in
          (match uu____5713 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5723 =
                 let uu____5724 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5724  in
               let uu____5725 =
                 let uu____5726 =
                   let uu____5727 =
                     let uu____5728 =
                       let uu____5729 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5729
                        in
                     FStar_Pprint.group uu____5728  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5727  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5726  in
               FStar_Pprint.ifflat uu____5723 uu____5725)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_5730  ->
    match uu___117_5730 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and (p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____5755 = p_uident uid  in
        let uu____5756 = p_binders true bs  in
        let uu____5758 =
          let uu____5759 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5759  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5755 uu____5756 uu____5758

and (p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document)
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let binders = p_binders true bs  in
          let uu____5774 =
            let uu____5775 =
              let uu____5776 =
                let uu____5777 = p_uident uid  in
                let uu____5778 = p_binders true bs  in
                let uu____5780 =
                  let uu____5781 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5781  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5777 uu____5778 uu____5780
                 in
              FStar_Pprint.group uu____5776  in
            let uu____5786 =
              let uu____5787 = str "with"  in
              let uu____5789 =
                let uu____5790 =
                  let uu____5791 =
                    let uu____5792 =
                      let uu____5793 =
                        let uu____5794 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5794
                         in
                      separate_map_last uu____5793 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5792  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5791  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5790  in
              FStar_Pprint.op_Hat_Hat uu____5787 uu____5789  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5775 uu____5786  in
          braces_with_nesting uu____5774

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____5798,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____5831 =
            let uu____5832 = p_lident lid  in
            let uu____5833 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5832 uu____5833  in
          let uu____5834 = p_simpleTerm ps false e  in
          prefix2 uu____5831 uu____5834
      | uu____5836 ->
          let uu____5837 =
            let uu____5839 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5839
             in
          failwith uu____5837

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5922 =
        match uu____5922 with
        | (kwd,t) ->
            let uu____5933 =
              let uu____5934 = str kwd  in
              let uu____5935 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5934 uu____5935  in
            let uu____5936 = p_simpleTerm ps false t  in
            prefix2 uu____5933 uu____5936
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5943 =
      let uu____5944 =
        let uu____5945 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5946 =
          let uu____5947 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5947  in
        FStar_Pprint.op_Hat_Hat uu____5945 uu____5946  in
      let uu____5949 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5944 uu____5949  in
    let uu____5950 =
      let uu____5951 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5951  in
    FStar_Pprint.op_Hat_Hat uu____5943 uu____5950

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_5952  ->
    match uu___118_5952 with
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

and (p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document) =
  fun qs  ->
    match qs with
    | [] -> FStar_Pprint.empty
    | q::[] ->
        let uu____5972 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____5972 FStar_Pprint.hardline
    | uu____5973 ->
        let uu____5974 =
          let uu____5975 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5975  in
        FStar_Pprint.op_Hat_Hat uu____5974 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_5978  ->
    match uu___119_5978 with
    | FStar_Parser_AST.Rec  ->
        let uu____5979 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5979
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_5981  ->
    match uu___120_5981 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____5985,e) ->
             let uu____5991 = str "#["  in
             let uu____5993 =
               let uu____5994 = p_term false false e  in
               let uu____5997 =
                 let uu____5998 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____5998 break1  in
               FStar_Pprint.op_Hat_Hat uu____5994 uu____5997  in
             FStar_Pprint.op_Hat_Hat uu____5991 uu____5993
         | uu____6000 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6006 =
          let uu____6007 =
            let uu____6008 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6008  in
          FStar_Pprint.separate_map uu____6007 p_tuplePattern pats  in
        FStar_Pprint.group uu____6006
    | uu____6009 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6018 =
          let uu____6019 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6019 p_constructorPattern pats  in
        FStar_Pprint.group uu____6018
    | uu____6020 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6023;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6028 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6029 = p_constructorPattern hd1  in
        let uu____6030 = p_constructorPattern tl1  in
        infix0 uu____6028 uu____6029 uu____6030
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6032;_},pats)
        ->
        let uu____6038 = p_quident uid  in
        let uu____6039 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6038 uu____6039
    | uu____6040 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6056;
               FStar_Parser_AST.blevel = uu____6057;
               FStar_Parser_AST.aqual = uu____6058;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6067 =
               let uu____6068 = p_ident lid  in
               p_refinement aqual uu____6068 t1 phi  in
             soft_parens_with_nesting uu____6067
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6071;
               FStar_Parser_AST.blevel = uu____6072;
               FStar_Parser_AST.aqual = uu____6073;_},phi))
             ->
             let uu____6079 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6079
         | uu____6080 ->
             let uu____6085 =
               let uu____6086 = p_tuplePattern pat  in
               let uu____6087 =
                 let uu____6088 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6088
                  in
               FStar_Pprint.op_Hat_Hat uu____6086 uu____6087  in
             soft_parens_with_nesting uu____6085)
    | FStar_Parser_AST.PatList pats ->
        let uu____6092 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6092 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6111 =
          match uu____6111 with
          | (lid,pat) ->
              let uu____6118 = p_qlident lid  in
              let uu____6119 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6118 uu____6119
           in
        let uu____6120 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6120
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6132 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6133 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6134 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6132 uu____6133 uu____6134
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6145 =
          let uu____6146 =
            let uu____6147 =
              let uu____6148 = FStar_Ident.text_of_id op  in str uu____6148
               in
            let uu____6150 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6147 uu____6150  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6146  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6145
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6154 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6154 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6162 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6163 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6162 uu____6163
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6165 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6169;
           FStar_Parser_AST.prange = uu____6170;_},uu____6171)
        ->
        let uu____6176 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6176
    | FStar_Parser_AST.PatTuple (uu____6177,false ) ->
        let uu____6184 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6184
    | uu____6185 ->
        let uu____6186 =
          let uu____6188 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6188  in
        failwith uu____6186

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6193;_},uu____6194)
        -> true
    | uu____6201 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6207) -> true
    | uu____6209 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6217 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____6218 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____6217 uu____6218
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6225;
                   FStar_Parser_AST.blevel = uu____6226;
                   FStar_Parser_AST.aqual = uu____6227;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6232 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____6232 t1 phi
            | uu____6233 ->
                let t' =
                  let uu____6235 = is_typ_tuple t  in
                  if uu____6235
                  then
                    let uu____6238 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6238
                  else p_tmFormula t  in
                let uu____6241 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____6242 =
                  let uu____6243 = p_lident lid  in
                  let uu____6244 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____6243 uu____6244  in
                FStar_Pprint.op_Hat_Hat uu____6241 uu____6242
             in
          let uu____6245 =
            is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)  in
          if uu____6245
          then
            let uu____6248 =
              let uu____6249 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6249  in
            FStar_Pprint.group uu____6248
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____6252 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6260;
                  FStar_Parser_AST.blevel = uu____6261;
                  FStar_Parser_AST.aqual = uu____6262;_},phi)
               ->
               if is_atomic
               then
                 let uu____6267 =
                   let uu____6268 =
                     let uu____6269 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____6269 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6268  in
                 FStar_Pprint.group uu____6267
               else
                 (let uu____6272 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____6272)
           | uu____6273 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____6286 -> false
            | FStar_Parser_AST.App uu____6298 -> false
            | FStar_Parser_AST.Op uu____6306 -> false
            | uu____6314 -> true  in
          let uu____6316 = p_noSeqTerm false false phi  in
          match uu____6316 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6329 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6329)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____6338 =
                let uu____6339 = FStar_Pprint.optional p_aqual aqual_opt  in
                let uu____6340 =
                  FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
                FStar_Pprint.op_Hat_Hat uu____6339 uu____6340  in
              let uu____6341 =
                let uu____6342 = p_appTerm t  in
                let uu____6343 =
                  let uu____6344 =
                    let uu____6345 =
                      let uu____6346 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6347 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6346 uu____6347  in
                    FStar_Pprint.group uu____6345  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____6344
                   in
                FStar_Pprint.op_Hat_Hat uu____6342 uu____6343  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6338 uu____6341

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6361 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6361

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6365 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6368 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6368)
       in
    if uu____6365
    then FStar_Pprint.underscore
    else (let uu____6373 = FStar_Ident.text_of_id lid  in str uu____6373)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6376 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6379 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6379)
       in
    if uu____6376
    then FStar_Pprint.underscore
    else (let uu____6384 = FStar_Ident.text_of_lid lid  in str uu____6384)

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document)
  = fun b  -> if b then soft_parens_with_nesting else (fun x  -> x)

and (inline_comment_or_above :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun comm  ->
    fun doc1  ->
      fun sep  ->
        if comm = FStar_Pprint.empty
        then
          let uu____6405 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____6405
        else
          (let uu____6408 =
             let uu____6409 =
               let uu____6410 =
                 let uu____6411 =
                   let uu____6412 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6412  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____6411  in
               FStar_Pprint.group uu____6410  in
             let uu____6413 =
               let uu____6414 =
                 let uu____6415 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6415  in
               FStar_Pprint.op_Hat_Hat comm uu____6414  in
             FStar_Pprint.ifflat uu____6409 uu____6413  in
           FStar_All.pipe_left FStar_Pprint.group uu____6408)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6423 = p_noSeqTerm true false e1  in
            (match uu____6423 with
             | (comm,t1) ->
                 let uu____6432 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6433 =
                   let uu____6434 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6434
                    in
                 FStar_Pprint.op_Hat_Hat uu____6432 uu____6433)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6438 =
              let uu____6439 =
                let uu____6440 =
                  let uu____6441 = p_lident x  in
                  let uu____6442 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6441 uu____6442  in
                let uu____6443 =
                  let uu____6444 = p_noSeqTermAndComment true false e1  in
                  let uu____6447 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6444 uu____6447  in
                op_Hat_Slash_Plus_Hat uu____6440 uu____6443  in
              FStar_Pprint.group uu____6439  in
            let uu____6448 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6438 uu____6448
        | uu____6449 ->
            let uu____6450 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6450

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6462 = p_noSeqTerm true false e1  in
            (match uu____6462 with
             | (comm,t1) ->
                 let uu____6475 =
                   let uu____6476 =
                     let uu____6477 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6477  in
                   let uu____6478 =
                     let uu____6479 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6479
                      in
                   FStar_Pprint.op_Hat_Hat uu____6476 uu____6478  in
                 (comm, uu____6475))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6483 =
              let uu____6484 =
                let uu____6485 =
                  let uu____6486 =
                    let uu____6487 = p_lident x  in
                    let uu____6488 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6487 uu____6488  in
                  let uu____6489 =
                    let uu____6490 = p_noSeqTermAndComment true false e1  in
                    let uu____6493 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6490 uu____6493  in
                  op_Hat_Slash_Plus_Hat uu____6486 uu____6489  in
                FStar_Pprint.group uu____6485  in
              let uu____6494 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6484 uu____6494  in
            (FStar_Pprint.empty, uu____6483)
        | uu____6495 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range "!3"

and (p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range "!3"

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____6519 =
              let uu____6520 = p_tmIff e1  in
              let uu____6521 =
                let uu____6522 =
                  let uu____6523 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6523
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6522  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6520 uu____6521  in
            FStar_Pprint.group uu____6519
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6529 =
              let uu____6530 = p_tmIff e1  in
              let uu____6531 =
                let uu____6532 =
                  let uu____6533 =
                    let uu____6534 = p_typ false false t  in
                    let uu____6537 =
                      let uu____6538 = str "by"  in
                      let uu____6540 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6538 uu____6540  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6534 uu____6537  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6533
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6532  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6530 uu____6531  in
            FStar_Pprint.group uu____6529
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____6541;_},e1::e2::e3::[])
            ->
            let uu____6548 =
              let uu____6549 =
                let uu____6550 =
                  let uu____6551 = p_atomicTermNotQUident e1  in
                  let uu____6552 =
                    let uu____6553 =
                      let uu____6554 =
                        let uu____6555 = p_term false false e2  in
                        soft_parens_with_nesting uu____6555  in
                      let uu____6558 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6554 uu____6558  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6553  in
                  FStar_Pprint.op_Hat_Hat uu____6551 uu____6552  in
                FStar_Pprint.group uu____6550  in
              let uu____6559 =
                let uu____6560 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6560  in
              FStar_Pprint.op_Hat_Hat uu____6549 uu____6559  in
            FStar_Pprint.group uu____6548
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____6561;_},e1::e2::e3::[])
            ->
            let uu____6568 =
              let uu____6569 =
                let uu____6570 =
                  let uu____6571 = p_atomicTermNotQUident e1  in
                  let uu____6572 =
                    let uu____6573 =
                      let uu____6574 =
                        let uu____6575 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6575  in
                      let uu____6578 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6574 uu____6578  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6573  in
                  FStar_Pprint.op_Hat_Hat uu____6571 uu____6572  in
                FStar_Pprint.group uu____6570  in
              let uu____6579 =
                let uu____6580 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6580  in
              FStar_Pprint.op_Hat_Hat uu____6569 uu____6579  in
            FStar_Pprint.group uu____6568
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6590 =
              let uu____6591 = str "requires"  in
              let uu____6593 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6591 uu____6593  in
            FStar_Pprint.group uu____6590
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6603 =
              let uu____6604 = str "ensures"  in
              let uu____6606 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6604 uu____6606  in
            FStar_Pprint.group uu____6603
        | FStar_Parser_AST.Attributes es ->
            let uu____6610 =
              let uu____6611 = str "attributes"  in
              let uu____6613 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6611 uu____6613  in
            FStar_Pprint.group uu____6610
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____6618 =
                let uu____6619 =
                  let uu____6620 = str "if"  in
                  let uu____6622 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____6620 uu____6622  in
                let uu____6625 =
                  let uu____6626 = str "then"  in
                  let uu____6628 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____6626 uu____6628  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6619 uu____6625  in
              FStar_Pprint.group uu____6618
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____6632,uu____6633,e31) when
                     is_unit e31 ->
                     let uu____6635 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____6635
                 | uu____6638 -> p_noSeqTermAndComment false false e2  in
               let uu____6641 =
                 let uu____6642 =
                   let uu____6643 = str "if"  in
                   let uu____6645 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____6643 uu____6645  in
                 let uu____6648 =
                   let uu____6649 =
                     let uu____6650 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____6650 e2_doc  in
                   let uu____6652 =
                     let uu____6653 = str "else"  in
                     let uu____6655 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____6653 uu____6655  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____6649 uu____6652  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____6642 uu____6648  in
               FStar_Pprint.group uu____6641)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____6678 =
              let uu____6679 =
                let uu____6680 =
                  let uu____6681 = str "try"  in
                  let uu____6683 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____6681 uu____6683  in
                let uu____6686 =
                  let uu____6687 = str "with"  in
                  let uu____6689 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6687 uu____6689  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6680 uu____6686  in
              FStar_Pprint.group uu____6679  in
            let uu____6698 = paren_if (ps || pb)  in uu____6698 uu____6678
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____6725 =
              let uu____6726 =
                let uu____6727 =
                  let uu____6728 = str "match"  in
                  let uu____6730 = p_noSeqTermAndComment false false e1  in
                  let uu____6733 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6728 uu____6730 uu____6733
                   in
                let uu____6737 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6727 uu____6737  in
              FStar_Pprint.group uu____6726  in
            let uu____6746 = paren_if (ps || pb)  in uu____6746 uu____6725
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____6753 =
              let uu____6754 =
                let uu____6755 =
                  let uu____6756 = str "let open"  in
                  let uu____6758 = p_quident uid  in
                  let uu____6759 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6756 uu____6758 uu____6759
                   in
                let uu____6763 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6755 uu____6763  in
              FStar_Pprint.group uu____6754  in
            let uu____6765 = paren_if ps  in uu____6765 uu____6753
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____6830 is_last =
              match uu____6830 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____6864 =
                          let uu____6865 = str "let"  in
                          let uu____6867 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6865 uu____6867
                           in
                        FStar_Pprint.group uu____6864
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____6870 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let uu____6875 = p_term_sep false false e2  in
                  (match uu____6875 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____6885 =
                         if is_last
                         then
                           let uu____6887 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____6888 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____6887 doc_expr1
                             uu____6888
                         else
                           (let uu____6894 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____6894)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____6885)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6945 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6945
                     else
                       (let uu____6956 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6956)) lbs
               in
            let lbs_doc =
              let uu____6966 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6966  in
            let uu____6967 =
              let uu____6968 =
                let uu____6969 =
                  let uu____6970 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6970
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6969  in
              FStar_Pprint.group uu____6968  in
            let uu____6972 = paren_if ps  in uu____6972 uu____6967
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6979;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6982;
                                                             FStar_Parser_AST.level
                                                               = uu____6983;_})
            when matches_var maybe_x x ->
            let uu____7010 =
              let uu____7011 =
                let uu____7012 = str "function"  in
                let uu____7014 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7012 uu____7014  in
              FStar_Pprint.group uu____7011  in
            let uu____7023 = paren_if (ps || pb)  in uu____7023 uu____7010
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7029 =
              let uu____7030 = str "quote"  in
              let uu____7032 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7030 uu____7032  in
            FStar_Pprint.group uu____7029
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7034 =
              let uu____7035 = str "`"  in
              let uu____7037 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7035 uu____7037  in
            FStar_Pprint.group uu____7034
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7039 =
              let uu____7040 = str "`%"  in
              let uu____7042 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7040 uu____7042  in
            FStar_Pprint.group uu____7039
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7044;
              FStar_Parser_AST.level = uu____7045;_}
            ->
            let uu____7046 =
              let uu____7047 = str "`@"  in
              let uu____7049 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7047 uu____7049  in
            FStar_Pprint.group uu____7046
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7051 =
              let uu____7052 = str "`#"  in
              let uu____7054 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7052 uu____7054  in
            FStar_Pprint.group uu____7051
        | uu____7055 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_7056  ->
    match uu___121_7056 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7068 =
          let uu____7069 = str "[@"  in
          let uu____7071 =
            let uu____7072 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7073 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7072 uu____7073  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7069 uu____7071  in
        FStar_Pprint.group uu____7068

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range "!4"

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range "!4"

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7114 =
                   let uu____7115 =
                     let uu____7116 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7116 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____7115 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____7114 term_doc
             | pats ->
                 let uu____7124 =
                   let uu____7125 =
                     let uu____7126 =
                       let uu____7127 =
                         let uu____7128 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7128
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____7127 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7131 = p_trigger trigger  in
                     prefix2 uu____7126 uu____7131  in
                   FStar_Pprint.group uu____7125  in
                 prefix2 uu____7124 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7152 =
                   let uu____7153 =
                     let uu____7154 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7154 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____7153 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____7152 term_doc
             | pats ->
                 let uu____7162 =
                   let uu____7163 =
                     let uu____7164 =
                       let uu____7165 =
                         let uu____7166 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7166
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____7165 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7169 = p_trigger trigger  in
                     prefix2 uu____7164 uu____7169  in
                   FStar_Pprint.group uu____7163  in
                 prefix2 uu____7162 term_doc)
        | uu____7170 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____7172 -> str "forall"
    | FStar_Parser_AST.QExists uu____7186 -> str "exists"
    | uu____7200 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_7202  ->
    match uu___122_7202 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____7214 =
          let uu____7215 =
            let uu____7216 =
              let uu____7217 = str "pattern"  in
              let uu____7219 =
                let uu____7220 =
                  let uu____7221 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____7221
                   in
                FStar_Pprint.op_Hat_Hat uu____7220 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7217 uu____7219  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7216  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7215  in
        FStar_Pprint.group uu____7214

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____7229 = str "\\/"  in
    FStar_Pprint.separate_map uu____7229 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____7236 =
      let uu____7237 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____7237 p_appTerm pats  in
    FStar_Pprint.group uu____7236

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____7249 = p_term_sep false pb e1  in
            (match uu____7249 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____7258 = str "fun"  in
                   let uu____7260 =
                     let uu____7261 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____7261
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____7258 uu____7260  in
                 let uu____7262 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____7264 =
                       let uu____7265 =
                         let uu____7266 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____7266  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____7265
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____7264
                   else
                     (let uu____7269 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____7269)
                    in
                 let uu____7270 = paren_if ps  in uu____7270 uu____7262)
        | uu____7275 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____7283  ->
      match uu____7283 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____7307 =
                    let uu____7308 =
                      let uu____7309 =
                        let uu____7310 = p_tuplePattern p  in
                        let uu____7311 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____7310 uu____7311  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7309
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7308  in
                  FStar_Pprint.group uu____7307
              | FStar_Pervasives_Native.Some f ->
                  let uu____7313 =
                    let uu____7314 =
                      let uu____7315 =
                        let uu____7316 =
                          let uu____7317 =
                            let uu____7318 = p_tuplePattern p  in
                            let uu____7319 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____7318
                              uu____7319
                             in
                          FStar_Pprint.group uu____7317  in
                        let uu____7321 =
                          let uu____7322 =
                            let uu____7325 = p_tmFormula f  in
                            [uu____7325; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____7322  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____7316 uu____7321
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7315
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7314  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____7313
               in
            let uu____7327 = p_term_sep false pb e  in
            match uu____7327 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____7337 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____7337
                   else
                     (let uu____7340 =
                        let uu____7341 =
                          let uu____7342 =
                            let uu____7343 =
                              let uu____7344 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____7344  in
                            op_Hat_Slash_Plus_Hat branch uu____7343  in
                          FStar_Pprint.group uu____7342  in
                        let uu____7345 =
                          let uu____7346 =
                            let uu____7347 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____7347  in
                          FStar_Pprint.op_Hat_Hat branch uu____7346  in
                        FStar_Pprint.ifflat uu____7341 uu____7345  in
                      FStar_Pprint.group uu____7340))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____7351 =
                       let uu____7352 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____7352  in
                     op_Hat_Slash_Plus_Hat branch uu____7351)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____7363 =
                      let uu____7364 =
                        let uu____7365 =
                          let uu____7366 =
                            let uu____7367 =
                              let uu____7368 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____7368  in
                            FStar_Pprint.separate_map uu____7367
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7366
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7365
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7364  in
                    FStar_Pprint.group uu____7363
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____7370 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____7372;_},e1::e2::[])
        ->
        let uu____7378 = str "<==>"  in
        let uu____7380 = p_tmImplies e1  in
        let uu____7381 = p_tmIff e2  in
        infix0 uu____7378 uu____7380 uu____7381
    | uu____7382 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____7384;_},e1::e2::[])
        ->
        let uu____7390 = str "==>"  in
        let uu____7392 = p_tmArrow p_tmFormula e1  in
        let uu____7393 = p_tmImplies e2  in
        infix0 uu____7390 uu____7392 uu____7393
    | uu____7394 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____7402 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____7402 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_5 when _0_5 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____7427 ->
               let uu____7428 =
                 let uu____7429 =
                   let uu____7430 =
                     let uu____7431 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7431
                      in
                   FStar_Pprint.separate uu____7430 terms  in
                 let uu____7432 =
                   let uu____7433 =
                     let uu____7434 =
                       let uu____7435 =
                         let uu____7436 =
                           let uu____7437 =
                             let uu____7438 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____7438
                              in
                           FStar_Pprint.separate uu____7437 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____7436 last_op  in
                       let uu____7439 =
                         let uu____7440 =
                           let uu____7441 =
                             let uu____7442 =
                               let uu____7443 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____7443
                                in
                             FStar_Pprint.separate uu____7442 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____7441 last_op  in
                         jump2 uu____7440  in
                       FStar_Pprint.ifflat uu____7435 uu____7439  in
                     FStar_Pprint.group uu____7434  in
                   let uu____7444 = FStar_List.hd last1  in
                   prefix2 uu____7433 uu____7444  in
                 FStar_Pprint.ifflat uu____7429 uu____7432  in
               FStar_Pprint.group uu____7428)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____7457 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____7463 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____7457 uu____7463
      | uu____7466 -> let uu____7467 = p_Tm e  in [uu____7467]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____7470 =
        let uu____7471 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____7471 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7470  in
    let disj =
      let uu____7474 =
        let uu____7475 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____7475 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7474  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____7495;_},e1::e2::[])
        ->
        let uu____7501 = p_tmDisjunction e1  in
        let uu____7506 = let uu____7511 = p_tmConjunction e2  in [uu____7511]
           in
        FStar_List.append uu____7501 uu____7506
    | uu____7520 -> let uu____7521 = p_tmConjunction e  in [uu____7521]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____7531;_},e1::e2::[])
        ->
        let uu____7537 = p_tmConjunction e1  in
        let uu____7540 = let uu____7543 = p_tmTuple e2  in [uu____7543]  in
        FStar_List.append uu____7537 uu____7540
    | uu____7544 -> let uu____7545 = p_tmTuple e  in [uu____7545]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range "!5"

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____7564 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____7564
          (fun uu____7572  ->
             match uu____7572 with | (e1,uu____7578) -> p_tmEq e1) args
    | uu____7579 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____7588 =
             let uu____7589 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7589  in
           FStar_Pprint.group uu____7588)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
         in
      p_tmEqWith' p_X n1 e

and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               (let uu____7608 = FStar_Ident.text_of_id op  in
                uu____7608 = "="))
              ||
              (let uu____7613 = FStar_Ident.text_of_id op  in
               uu____7613 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____7619 = levels op1  in
            (match uu____7619 with
             | (left1,mine,right1) ->
                 let uu____7638 =
                   let uu____7639 = FStar_All.pipe_left str op1  in
                   let uu____7641 = p_tmEqWith' p_X left1 e1  in
                   let uu____7642 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____7639 uu____7641 uu____7642  in
                 paren_if_gt curr mine uu____7638)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____7643;_},e1::e2::[])
            ->
            let uu____7649 =
              let uu____7650 = p_tmEqWith p_X e1  in
              let uu____7651 =
                let uu____7652 =
                  let uu____7653 =
                    let uu____7654 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____7654  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7653  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7652  in
              FStar_Pprint.op_Hat_Hat uu____7650 uu____7651  in
            FStar_Pprint.group uu____7649
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____7655;_},e1::[])
            ->
            let uu____7660 = levels "-"  in
            (match uu____7660 with
             | (left1,mine,right1) ->
                 let uu____7680 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____7680)
        | uu____7681 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' false p_X n1 e

and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple  ->
    fun p_X  ->
      fun curr  ->
        fun e  ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid,(e1,uu____7729)::(e2,uu____7731)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____7751 = is_list e  in Prims.op_Negation uu____7751)
              ->
              let op = "::"  in
              let uu____7756 = levels op  in
              (match uu____7756 with
               | (left1,mine,right1) ->
                   let uu____7775 =
                     let uu____7776 = str op  in
                     let uu____7777 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7779 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7776 uu____7777 uu____7779  in
                   paren_if_gt curr mine uu____7775)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____7798 = levels op  in
              (match uu____7798 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____7832 = p_binder false b  in
                         let uu____7834 =
                           let uu____7835 =
                             let uu____7836 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7836 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7835
                            in
                         FStar_Pprint.op_Hat_Hat uu____7832 uu____7834
                     | FStar_Util.Inr t ->
                         let uu____7838 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____7840 =
                           let uu____7841 =
                             let uu____7842 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7842 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7841
                            in
                         FStar_Pprint.op_Hat_Hat uu____7838 uu____7840
                      in
                   let uu____7843 =
                     let uu____7844 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____7849 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____7844 uu____7849  in
                   paren_if_gt curr mine uu____7843)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____7851;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____7881 = levels op  in
              (match uu____7881 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____7901 = str op  in
                     let uu____7902 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____7904 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____7901 uu____7902 uu____7904
                   else
                     (let uu____7908 =
                        let uu____7909 = str op  in
                        let uu____7910 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____7912 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____7909 uu____7910 uu____7912  in
                      paren_if_gt curr mine uu____7908))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____7921 = levels op1  in
              (match uu____7921 with
               | (left1,mine,right1) ->
                   let uu____7940 =
                     let uu____7941 = str op1  in
                     let uu____7942 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7944 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7941 uu____7942 uu____7944  in
                   paren_if_gt curr mine uu____7940)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____7964 =
                let uu____7965 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____7966 =
                  let uu____7967 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____7967 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____7965 uu____7966  in
              braces_with_nesting uu____7964
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____7972;_},e1::[])
              ->
              let uu____7977 =
                let uu____7978 = str "~"  in
                let uu____7980 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____7978 uu____7980  in
              FStar_Pprint.group uu____7977
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____7982;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____7991 = levels op  in
                   (match uu____7991 with
                    | (left1,mine,right1) ->
                        let uu____8010 =
                          let uu____8011 = str op  in
                          let uu____8012 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____8014 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____8011 uu____8012 uu____8014  in
                        paren_if_gt curr mine uu____8010)
               | uu____8016 -> p_X e)
          | uu____8017 -> p_X e

and (p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_appTerm e

and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmEqWith p_tmRefinement e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_tmNoEqWith p_tmRefinement e

and (p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid,e1) ->
        let uu____8024 =
          let uu____8025 = p_lident lid  in
          let uu____8026 =
            let uu____8027 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____8027  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8025 uu____8026  in
        FStar_Pprint.group uu____8024
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____8030 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____8032 = p_appTerm e  in
    let uu____8033 =
      let uu____8034 =
        let uu____8035 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____8035 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8034  in
    FStar_Pprint.op_Hat_Hat uu____8032 uu____8033

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____8041 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____8041 t phi
      | FStar_Parser_AST.TAnnotated uu____8042 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____8048 ->
          let uu____8049 =
            let uu____8051 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8051
             in
          failwith uu____8049
      | FStar_Parser_AST.TVariable uu____8054 ->
          let uu____8055 =
            let uu____8057 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8057
             in
          failwith uu____8055
      | FStar_Parser_AST.NoName uu____8060 ->
          let uu____8061 =
            let uu____8063 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____8063
             in
          failwith uu____8061

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____8067  ->
      match uu____8067 with
      | (lid,e) ->
          let uu____8075 =
            let uu____8076 = p_qlident lid  in
            let uu____8077 =
              let uu____8078 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____8078
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____8076 uu____8077  in
          FStar_Pprint.group uu____8075

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____8081 when is_general_application e ->
        let uu____8088 = head_and_args e  in
        (match uu____8088 with
         | (head1,args) ->
             let uu____8113 =
               let uu____8124 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____8124
               then
                 let uu____8158 =
                   FStar_Util.take
                     (fun uu____8182  ->
                        match uu____8182 with
                        | (uu____8188,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____8158 with
                 | (fs_typ_args,args1) ->
                     let uu____8226 =
                       let uu____8227 = p_indexingTerm head1  in
                       let uu____8228 =
                         let uu____8229 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____8229 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____8227 uu____8228  in
                     (uu____8226, args1)
               else
                 (let uu____8244 = p_indexingTerm head1  in
                  (uu____8244, args))
                in
             (match uu____8113 with
              | (head_doc,args1) ->
                  let uu____8265 =
                    let uu____8266 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____8266 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____8265))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____8288 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____8288)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____8307 =
               let uu____8308 = p_quident lid  in
               let uu____8309 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____8308 uu____8309  in
             FStar_Pprint.group uu____8307
         | hd1::tl1 ->
             let uu____8326 =
               let uu____8327 =
                 let uu____8328 =
                   let uu____8329 = p_quident lid  in
                   let uu____8330 = p_argTerm hd1  in
                   prefix2 uu____8329 uu____8330  in
                 FStar_Pprint.group uu____8328  in
               let uu____8331 =
                 let uu____8332 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____8332  in
               FStar_Pprint.op_Hat_Hat uu____8327 uu____8331  in
             FStar_Pprint.group uu____8326)
    | uu____8337 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____8348 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____8348 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____8352 = str "#"  in
        let uu____8354 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____8352 uu____8354
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____8357 = str "#["  in
        let uu____8359 =
          let uu____8360 = p_indexingTerm t  in
          let uu____8361 =
            let uu____8362 = str "]"  in
            let uu____8364 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____8362 uu____8364  in
          FStar_Pprint.op_Hat_Hat uu____8360 uu____8361  in
        FStar_Pprint.op_Hat_Hat uu____8357 uu____8359
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____8366  ->
    match uu____8366 with | (e,uu____8372) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____8377;_},e1::e2::[])
          ->
          let uu____8383 =
            let uu____8384 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____8385 =
              let uu____8386 =
                let uu____8387 = p_term false false e2  in
                soft_parens_with_nesting uu____8387  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8386  in
            FStar_Pprint.op_Hat_Hat uu____8384 uu____8385  in
          FStar_Pprint.group uu____8383
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____8390;_},e1::e2::[])
          ->
          let uu____8396 =
            let uu____8397 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____8398 =
              let uu____8399 =
                let uu____8400 = p_term false false e2  in
                soft_brackets_with_nesting uu____8400  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8399  in
            FStar_Pprint.op_Hat_Hat uu____8397 uu____8398  in
          FStar_Pprint.group uu____8396
      | uu____8403 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____8408 = p_quident lid  in
        let uu____8409 =
          let uu____8410 =
            let uu____8411 = p_term false false e1  in
            soft_parens_with_nesting uu____8411  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8410  in
        FStar_Pprint.op_Hat_Hat uu____8408 uu____8409
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____8419 =
          let uu____8420 = FStar_Ident.text_of_id op  in str uu____8420  in
        let uu____8422 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____8419 uu____8422
    | uu____8423 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid ->
        str "assume"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____8436 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____8445 =
          let uu____8446 = FStar_Ident.text_of_id op  in str uu____8446  in
        let uu____8448 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____8445 uu____8448
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____8452 =
          let uu____8453 =
            let uu____8454 =
              let uu____8455 = FStar_Ident.text_of_id op  in str uu____8455
               in
            let uu____8457 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____8454 uu____8457  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8453  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____8452
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____8472 = all_explicit args  in
        if uu____8472
        then
          let uu____8475 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____8476 =
            let uu____8477 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____8478 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____8477 p_tmEq uu____8478  in
          let uu____8485 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____8475 uu____8476 uu____8485
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____8507 =
                 let uu____8508 = p_quident lid  in
                 let uu____8509 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____8508 uu____8509  in
               FStar_Pprint.group uu____8507
           | hd1::tl1 ->
               let uu____8526 =
                 let uu____8527 =
                   let uu____8528 =
                     let uu____8529 = p_quident lid  in
                     let uu____8530 = p_argTerm hd1  in
                     prefix2 uu____8529 uu____8530  in
                   FStar_Pprint.group uu____8528  in
                 let uu____8531 =
                   let uu____8532 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____8532  in
                 FStar_Pprint.op_Hat_Hat uu____8527 uu____8531  in
               FStar_Pprint.group uu____8526)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____8539 =
          let uu____8540 = p_atomicTermNotQUident e1  in
          let uu____8541 =
            let uu____8542 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8542  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____8540 uu____8541
           in
        FStar_Pprint.group uu____8539
    | uu____8545 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____8550 = p_quident constr_lid  in
        let uu____8551 =
          let uu____8552 =
            let uu____8553 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8553  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____8552  in
        FStar_Pprint.op_Hat_Hat uu____8550 uu____8551
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____8555 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____8555 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____8557 = p_term_sep false false e1  in
        (match uu____8557 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____8570 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____8570))
    | uu____8571 when is_array e ->
        let es = extract_from_list e  in
        let uu____8575 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____8576 =
          let uu____8577 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____8577
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____8582 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____8575 uu____8576 uu____8582
    | uu____8585 when is_list e ->
        let uu____8586 =
          let uu____8587 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____8588 = extract_from_list e  in
          separate_map_or_flow_last uu____8587
            (fun ps  -> p_noSeqTermAndComment ps false) uu____8588
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____8586 FStar_Pprint.rbracket
    | uu____8597 when is_lex_list e ->
        let uu____8598 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____8599 =
          let uu____8600 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____8601 = extract_from_list e  in
          separate_map_or_flow_last uu____8600
            (fun ps  -> p_noSeqTermAndComment ps false) uu____8601
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____8598 uu____8599 FStar_Pprint.rbracket
    | uu____8610 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____8614 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____8615 =
          let uu____8616 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____8616 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____8614 uu____8615 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____8626 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____8629 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____8626 uu____8629
    | FStar_Parser_AST.Op (op,args) when
        let uu____8638 = handleable_op op args  in
        Prims.op_Negation uu____8638 ->
        let uu____8640 =
          let uu____8642 =
            let uu____8644 = FStar_Ident.text_of_id op  in
            let uu____8646 =
              let uu____8648 =
                let uu____8650 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____8650
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____8648  in
            Prims.strcat uu____8644 uu____8646  in
          Prims.strcat "Operation " uu____8642  in
        failwith uu____8640
    | FStar_Parser_AST.Uvar id1 ->
        let uu____8656 = str "u#"  in
        let uu____8658 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____8656 uu____8658
    | FStar_Parser_AST.Wild  ->
        let uu____8659 = p_term false false e  in
        soft_parens_with_nesting uu____8659
    | FStar_Parser_AST.Const uu____8662 ->
        let uu____8663 = p_term false false e  in
        soft_parens_with_nesting uu____8663
    | FStar_Parser_AST.Op uu____8666 ->
        let uu____8673 = p_term false false e  in
        soft_parens_with_nesting uu____8673
    | FStar_Parser_AST.Tvar uu____8676 ->
        let uu____8677 = p_term false false e  in
        soft_parens_with_nesting uu____8677
    | FStar_Parser_AST.Var uu____8680 ->
        let uu____8681 = p_term false false e  in
        soft_parens_with_nesting uu____8681
    | FStar_Parser_AST.Name uu____8684 ->
        let uu____8685 = p_term false false e  in
        soft_parens_with_nesting uu____8685
    | FStar_Parser_AST.Construct uu____8688 ->
        let uu____8699 = p_term false false e  in
        soft_parens_with_nesting uu____8699
    | FStar_Parser_AST.Abs uu____8702 ->
        let uu____8709 = p_term false false e  in
        soft_parens_with_nesting uu____8709
    | FStar_Parser_AST.App uu____8712 ->
        let uu____8719 = p_term false false e  in
        soft_parens_with_nesting uu____8719
    | FStar_Parser_AST.Let uu____8722 ->
        let uu____8743 = p_term false false e  in
        soft_parens_with_nesting uu____8743
    | FStar_Parser_AST.LetOpen uu____8746 ->
        let uu____8751 = p_term false false e  in
        soft_parens_with_nesting uu____8751
    | FStar_Parser_AST.Seq uu____8754 ->
        let uu____8759 = p_term false false e  in
        soft_parens_with_nesting uu____8759
    | FStar_Parser_AST.Bind uu____8762 ->
        let uu____8769 = p_term false false e  in
        soft_parens_with_nesting uu____8769
    | FStar_Parser_AST.If uu____8772 ->
        let uu____8779 = p_term false false e  in
        soft_parens_with_nesting uu____8779
    | FStar_Parser_AST.Match uu____8782 ->
        let uu____8797 = p_term false false e  in
        soft_parens_with_nesting uu____8797
    | FStar_Parser_AST.TryWith uu____8800 ->
        let uu____8815 = p_term false false e  in
        soft_parens_with_nesting uu____8815
    | FStar_Parser_AST.Ascribed uu____8818 ->
        let uu____8827 = p_term false false e  in
        soft_parens_with_nesting uu____8827
    | FStar_Parser_AST.Record uu____8830 ->
        let uu____8843 = p_term false false e  in
        soft_parens_with_nesting uu____8843
    | FStar_Parser_AST.Project uu____8846 ->
        let uu____8851 = p_term false false e  in
        soft_parens_with_nesting uu____8851
    | FStar_Parser_AST.Product uu____8854 ->
        let uu____8861 = p_term false false e  in
        soft_parens_with_nesting uu____8861
    | FStar_Parser_AST.Sum uu____8864 ->
        let uu____8875 = p_term false false e  in
        soft_parens_with_nesting uu____8875
    | FStar_Parser_AST.QForall uu____8878 ->
        let uu____8891 = p_term false false e  in
        soft_parens_with_nesting uu____8891
    | FStar_Parser_AST.QExists uu____8894 ->
        let uu____8907 = p_term false false e  in
        soft_parens_with_nesting uu____8907
    | FStar_Parser_AST.Refine uu____8910 ->
        let uu____8915 = p_term false false e  in
        soft_parens_with_nesting uu____8915
    | FStar_Parser_AST.NamedTyp uu____8918 ->
        let uu____8923 = p_term false false e  in
        soft_parens_with_nesting uu____8923
    | FStar_Parser_AST.Requires uu____8926 ->
        let uu____8934 = p_term false false e  in
        soft_parens_with_nesting uu____8934
    | FStar_Parser_AST.Ensures uu____8937 ->
        let uu____8945 = p_term false false e  in
        soft_parens_with_nesting uu____8945
    | FStar_Parser_AST.Attributes uu____8948 ->
        let uu____8951 = p_term false false e  in
        soft_parens_with_nesting uu____8951
    | FStar_Parser_AST.Quote uu____8954 ->
        let uu____8959 = p_term false false e  in
        soft_parens_with_nesting uu____8959
    | FStar_Parser_AST.VQuote uu____8962 ->
        let uu____8963 = p_term false false e  in
        soft_parens_with_nesting uu____8963
    | FStar_Parser_AST.Antiquote uu____8966 ->
        let uu____8967 = p_term false false e  in
        soft_parens_with_nesting uu____8967

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_8970  ->
    match uu___125_8970 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____8979) ->
        let uu____8982 = str s  in FStar_Pprint.dquotes uu____8982
    | FStar_Const.Const_bytearray (bytes,uu____8984) ->
        let uu____8989 =
          let uu____8990 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____8990  in
        let uu____8991 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____8989 uu____8991
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_9014 =
          match uu___123_9014 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_9021 =
          match uu___124_9021 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____9036  ->
               match uu____9036 with
               | (s,w) ->
                   let uu____9043 = signedness s  in
                   let uu____9044 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____9043 uu____9044)
            sign_width_opt
           in
        let uu____9045 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____9045 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____9049 = FStar_Range.string_of_range r  in str uu____9049
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____9053 = p_quident lid  in
        let uu____9054 =
          let uu____9055 =
            let uu____9056 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9056  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____9055  in
        FStar_Pprint.op_Hat_Hat uu____9053 uu____9054

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____9059 = str "u#"  in
    let uu____9061 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____9059 uu____9061

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____9063;_},u1::u2::[])
        ->
        let uu____9069 =
          let uu____9070 = p_universeFrom u1  in
          let uu____9071 =
            let uu____9072 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____9072  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9070 uu____9071  in
        FStar_Pprint.group uu____9069
    | FStar_Parser_AST.App uu____9073 ->
        let uu____9080 = head_and_args u  in
        (match uu____9080 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____9106 =
                    let uu____9107 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____9108 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____9116  ->
                           match uu____9116 with
                           | (u1,uu____9122) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____9107 uu____9108  in
                  FStar_Pprint.group uu____9106
              | uu____9123 ->
                  let uu____9124 =
                    let uu____9126 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____9126
                     in
                  failwith uu____9124))
    | uu____9129 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____9155 = FStar_Ident.text_of_id id1  in str uu____9155
    | FStar_Parser_AST.Paren u1 ->
        let uu____9158 = p_universeFrom u1  in
        soft_parens_with_nesting uu____9158
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____9159;_},uu____9160::uu____9161::[])
        ->
        let uu____9165 = p_universeFrom u  in
        soft_parens_with_nesting uu____9165
    | FStar_Parser_AST.App uu____9166 ->
        let uu____9173 = p_universeFrom u  in
        soft_parens_with_nesting uu____9173
    | uu____9174 ->
        let uu____9175 =
          let uu____9177 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____9177
           in
        failwith uu____9175

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    FStar_ST.op_Colon_Equals unfold_tuples false; p_term false false e
  
let (signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document)
  = fun e  -> p_justSig e 
let (decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun e  -> p_decl e 
let (pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  -> p_disjunctivePattern p 
let (binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun b  -> p_binder true b 
let (modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document) =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____9266,decls) ->
           let uu____9272 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____9272
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____9281,decls,uu____9283) ->
           let uu____9290 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____9290
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____9350  ->
         match uu____9350 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____9372)) -> false
      | ([],uu____9376) -> false
      | uu____9380 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____9390 -> true
         | uu____9392 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____9435,decls) -> decls
        | FStar_Parser_AST.Interface (uu____9441,decls,uu____9443) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____9495 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____9508;
                 FStar_Parser_AST.doc = uu____9509;
                 FStar_Parser_AST.quals = uu____9510;
                 FStar_Parser_AST.attrs = uu____9511;_}::uu____9512 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____9518 =
                   let uu____9521 =
                     let uu____9524 = FStar_List.tl ds  in d :: uu____9524
                      in
                   d0 :: uu____9521  in
                 (uu____9518, (d0.FStar_Parser_AST.drange))
             | uu____9529 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____9495 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____9586 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____9586 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____9695 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____9695, comments1))))))
  