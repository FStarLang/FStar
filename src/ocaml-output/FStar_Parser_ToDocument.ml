open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___110_43  ->
         match uu___110_43 with
         | (uu____49,FStar_Parser_AST.Nothing ) -> true
         | uu____51 -> false) args
  
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____85 'Auu____86 .
    Prims.bool -> ('Auu____85 -> 'Auu____86) -> 'Auu____85 -> 'Auu____86
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
  'Auu____196 'Auu____197 .
    'Auu____196 ->
      ('Auu____197 -> 'Auu____196) ->
        'Auu____197 FStar_Pervasives_Native.option -> 'Auu____196
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
  'Auu____310 .
    FStar_Pprint.document ->
      ('Auu____310 -> FStar_Pprint.document) ->
        'Auu____310 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____335 =
          let uu____336 =
            let uu____337 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____337  in
          FStar_Pprint.separate_map uu____336 f l  in
        FStar_Pprint.group uu____335
  
let precede_break_separate_map :
  'Auu____349 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____349 -> FStar_Pprint.document) ->
          'Auu____349 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____379 =
            let uu____380 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____381 =
              let uu____382 = FStar_List.hd l  in
              FStar_All.pipe_right uu____382 f  in
            FStar_Pprint.precede uu____380 uu____381  in
          let uu____383 =
            let uu____384 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____390 =
                   let uu____391 =
                     let uu____392 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____392  in
                   FStar_Pprint.op_Hat_Hat sep uu____391  in
                 FStar_Pprint.op_Hat_Hat break1 uu____390) uu____384
             in
          FStar_Pprint.op_Hat_Hat uu____379 uu____383
  
let concat_break_map :
  'Auu____400 .
    ('Auu____400 -> FStar_Pprint.document) ->
      'Auu____400 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____420 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____424 = f x  in FStar_Pprint.op_Hat_Hat uu____424 break1)
          l
         in
      FStar_Pprint.group uu____420
  
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
    let uu____487 = str "begin"  in
    let uu____489 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____487 contents uu____489
  
let separate_map_last :
  'Auu____502 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____502 -> FStar_Pprint.document) ->
        'Auu____502 Prims.list -> FStar_Pprint.document
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
  'Auu____560 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____560 -> FStar_Pprint.document) ->
        'Auu____560 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____592 =
          let uu____593 =
            let uu____594 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____594  in
          separate_map_last uu____593 f l  in
        FStar_Pprint.group uu____592
  
let separate_map_or_flow :
  'Auu____604 .
    FStar_Pprint.document ->
      ('Auu____604 -> FStar_Pprint.document) ->
        'Auu____604 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____642 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____642 -> FStar_Pprint.document) ->
        'Auu____642 Prims.list -> FStar_Pprint.document
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
  'Auu____700 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____700 -> FStar_Pprint.document) ->
        'Auu____700 Prims.list -> FStar_Pprint.document
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
              let uu____782 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____782
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____804 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____804 -> FStar_Pprint.document) ->
                  'Auu____804 Prims.list -> FStar_Pprint.document
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
                    (let uu____863 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____863
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____883 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____883 -> FStar_Pprint.document) ->
                  'Auu____883 Prims.list -> FStar_Pprint.document
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
                    (let uu____942 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____942
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____961  ->
    match uu____961 with
    | (comment,keywords) ->
        let uu____995 =
          let uu____996 =
            let uu____999 = str comment  in
            let uu____1000 =
              let uu____1003 =
                let uu____1006 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1017  ->
                       match uu____1017 with
                       | (k,v1) ->
                           let uu____1030 =
                             let uu____1033 = str k  in
                             let uu____1034 =
                               let uu____1037 =
                                 let uu____1040 = str v1  in [uu____1040]  in
                               FStar_Pprint.rarrow :: uu____1037  in
                             uu____1033 :: uu____1034  in
                           FStar_Pprint.concat uu____1030) keywords
                   in
                [uu____1006]  in
              FStar_Pprint.space :: uu____1003  in
            uu____999 :: uu____1000  in
          FStar_Pprint.concat uu____996  in
        FStar_Pprint.group uu____995
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1050 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1066 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1066
      | uu____1069 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1120::(e2,uu____1122)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1145 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1169,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1180,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1201 = extract_from_list e2  in e1 :: uu____1201
    | uu____1204 ->
        let uu____1205 =
          let uu____1207 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1207  in
        failwith uu____1205
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1221;
           FStar_Parser_AST.level = uu____1222;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1224 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1236;
           FStar_Parser_AST.level = uu____1237;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1239;
                                                         FStar_Parser_AST.level
                                                           = uu____1240;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1242;
                                                    FStar_Parser_AST.level =
                                                      uu____1243;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1245;
                FStar_Parser_AST.level = uu____1246;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1248;
           FStar_Parser_AST.level = uu____1249;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1251 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1263 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1264;
           FStar_Parser_AST.range = uu____1265;
           FStar_Parser_AST.level = uu____1266;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1267;
                                                         FStar_Parser_AST.range
                                                           = uu____1268;
                                                         FStar_Parser_AST.level
                                                           = uu____1269;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1271;
                                                    FStar_Parser_AST.level =
                                                      uu____1272;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1273;
                FStar_Parser_AST.range = uu____1274;
                FStar_Parser_AST.level = uu____1275;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1277;
           FStar_Parser_AST.level = uu____1278;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1280 = extract_from_ref_set e1  in
        let uu____1283 = extract_from_ref_set e2  in
        FStar_List.append uu____1280 uu____1283
    | uu____1286 ->
        let uu____1287 =
          let uu____1289 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1289  in
        failwith uu____1287
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1301 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1301
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1310 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1310
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1321 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1321 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1331 = FStar_Ident.text_of_id op  in uu____1331 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1401 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1421 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1432 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1443 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___111_1469  ->
    match uu___111_1469 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___112_1504  ->
      match uu___112_1504 with
      | FStar_Util.Inl c ->
          let uu____1517 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1517 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1533 .
    Prims.string ->
      ('Auu____1533 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1557  ->
      match uu____1557 with
      | (assoc_levels,tokens) ->
          let uu____1589 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1589 <> FStar_Pervasives_Native.None
  
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
  ((Prims.int * Prims.int * Prims.int) * token Prims.list) Prims.list) =
  let levels_from_associativity l uu___113_1761 =
    match uu___113_1761 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1811  ->
         match uu____1811 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1886 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1886 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1938) ->
          assoc_levels
      | uu____1976 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____2029 . ('Auu____2029 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2078 =
        FStar_List.tryFind
          (fun uu____2114  ->
             match uu____2114 with
             | (uu____2131,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2078 with
      | FStar_Pervasives_Native.Some ((uu____2160,l1,uu____2162),uu____2163)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2213 =
            let uu____2215 =
              let uu____2217 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2217  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2215
             in
          failwith uu____2213
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2252 = assign_levels level_associativity_spec op  in
    match uu____2252 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2311 =
      let uu____2314 =
        let uu____2320 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2320  in
      FStar_List.tryFind uu____2314 operatorInfix0ad12  in
    uu____2311 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2387 =
      let uu____2402 =
        let uu____2420 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2420  in
      FStar_List.tryFind uu____2402 opinfix34  in
    uu____2387 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2486 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2486
    then (Prims.parse_int "1")
    else
      (let uu____2499 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2499
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2545 . FStar_Ident.ident -> 'Auu____2545 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2563 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2563 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2572 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2572
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2594 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2594 [".()<-"; ".[]<-"]
      | uu____2602 -> false
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2646 .
    ('Auu____2646 -> FStar_Pprint.document) ->
      'Auu____2646 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2688 = FStar_ST.op_Bang comment_stack  in
          match uu____2688 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2758 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2758
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2800 =
                    let uu____2801 =
                      let uu____2802 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2802
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2801  in
                  comments_before_pos uu____2800 print_pos lookahead_pos))
              else
                (let uu____2805 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2805))
           in
        let uu____2808 =
          let uu____2814 =
            let uu____2815 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2815  in
          let uu____2816 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2814 uu____2816  in
        match uu____2808 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2825 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2825
              else comments  in
            let uu____2834 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2834
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2860 = FStar_ST.op_Bang comment_stack  in
          match uu____2860 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2954 =
                    let uu____2956 =
                      let uu____2958 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2958  in
                    uu____2956 - lbegin  in
                  max k uu____2954  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2963 =
                    let uu____2964 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2965 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2964 uu____2965  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2963  in
                let uu____2966 =
                  let uu____2968 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2968  in
                place_comments_until_pos (Prims.parse_int "1") uu____2966
                  pos_end doc2))
          | uu____2970 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2983 =
                     let uu____2985 = FStar_Range.line_of_pos pos_end  in
                     uu____2985 - lbegin  in
                   max (Prims.parse_int "1") uu____2983  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2991 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2991)
  
let separate_map_with_comments :
  'Auu____3005 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3005 -> FStar_Pprint.document) ->
          'Auu____3005 Prims.list ->
            ('Auu____3005 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3064 x =
              match uu____3064 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3082 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3082 doc1
                     in
                  let uu____3084 =
                    let uu____3086 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3086  in
                  let uu____3087 =
                    let uu____3088 =
                      let uu____3089 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3089  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3088  in
                  (uu____3084, uu____3087)
               in
            let uu____3091 =
              let uu____3098 = FStar_List.hd xs  in
              let uu____3099 = FStar_List.tl xs  in (uu____3098, uu____3099)
               in
            match uu____3091 with
            | (x,xs1) ->
                let init1 =
                  let uu____3116 =
                    let uu____3118 =
                      let uu____3119 = extract_range x  in
                      FStar_Range.end_of_range uu____3119  in
                    FStar_Range.line_of_pos uu____3118  in
                  let uu____3120 =
                    let uu____3121 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3121  in
                  (uu____3116, uu____3120)  in
                let uu____3123 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3123
  
let separate_map_with_comments_kw :
  'Auu____3150 'Auu____3151 .
    'Auu____3150 ->
      'Auu____3150 ->
        ('Auu____3150 -> 'Auu____3151 -> FStar_Pprint.document) ->
          'Auu____3151 Prims.list ->
            ('Auu____3151 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3215 x =
              match uu____3215 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3233 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3233 doc1
                     in
                  let uu____3235 =
                    let uu____3237 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3237  in
                  let uu____3238 =
                    let uu____3239 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3239  in
                  (uu____3235, uu____3238)
               in
            let uu____3241 =
              let uu____3248 = FStar_List.hd xs  in
              let uu____3249 = FStar_List.tl xs  in (uu____3248, uu____3249)
               in
            match uu____3241 with
            | (x,xs1) ->
                let init1 =
                  let uu____3266 =
                    let uu____3268 =
                      let uu____3269 = extract_range x  in
                      FStar_Range.end_of_range uu____3269  in
                    FStar_Range.line_of_pos uu____3268  in
                  let uu____3270 = f prefix1 x  in (uu____3266, uu____3270)
                   in
                let uu____3272 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3272
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4024)) ->
          let uu____4027 =
            let uu____4029 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4029 FStar_Util.is_upper  in
          if uu____4027
          then
            let uu____4035 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4035 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4038 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4045 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____4046 =
      let uu____4047 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4048 =
        let uu____4049 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4049  in
      FStar_Pprint.op_Hat_Hat uu____4047 uu____4048  in
    FStar_Pprint.op_Hat_Hat uu____4045 uu____4046

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4051 ->
        let uu____4052 =
          let uu____4053 = str "@ "  in
          let uu____4055 =
            let uu____4056 =
              let uu____4057 =
                let uu____4058 =
                  let uu____4059 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4059  in
                FStar_Pprint.op_Hat_Hat uu____4058 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4057  in
            FStar_Pprint.op_Hat_Hat uu____4056 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4053 uu____4055  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4052

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4062  ->
    match uu____4062 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4110 =
                match uu____4110 with
                | (kwd,arg) ->
                    let uu____4123 = str "@"  in
                    let uu____4125 =
                      let uu____4126 = str kwd  in
                      let uu____4127 =
                        let uu____4128 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4128
                         in
                      FStar_Pprint.op_Hat_Hat uu____4126 uu____4127  in
                    FStar_Pprint.op_Hat_Hat uu____4123 uu____4125
                 in
              let uu____4129 =
                let uu____4130 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____4130 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4129
           in
        let uu____4137 =
          let uu____4138 =
            let uu____4139 =
              let uu____4140 =
                let uu____4141 = str doc1  in
                let uu____4142 =
                  let uu____4143 =
                    let uu____4144 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4144  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4143  in
                FStar_Pprint.op_Hat_Hat uu____4141 uu____4142  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4140  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4139  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4138  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4137

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4148 =
          let uu____4149 = str "val"  in
          let uu____4151 =
            let uu____4152 =
              let uu____4153 = p_lident lid  in
              let uu____4154 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4153 uu____4154  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4152  in
          FStar_Pprint.op_Hat_Hat uu____4149 uu____4151  in
        let uu____4155 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4148 uu____4155
    | FStar_Parser_AST.TopLevelLet (uu____4158,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4183 =
               let uu____4184 = str "let"  in p_letlhs uu____4184 lb  in
             FStar_Pprint.group uu____4183) lbs
    | uu____4186 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_4201 =
          match uu___114_4201 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4209 = f x  in
              let uu____4210 =
                let uu____4211 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4211  in
              FStar_Pprint.op_Hat_Hat uu____4209 uu____4210
           in
        let uu____4212 = str "["  in
        let uu____4214 =
          let uu____4215 = p_list' l  in
          let uu____4216 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4215 uu____4216  in
        FStar_Pprint.op_Hat_Hat uu____4212 uu____4214

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4220 =
          let uu____4221 = str "open"  in
          let uu____4223 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4221 uu____4223  in
        FStar_Pprint.group uu____4220
    | FStar_Parser_AST.Include uid ->
        let uu____4225 =
          let uu____4226 = str "include"  in
          let uu____4228 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4226 uu____4228  in
        FStar_Pprint.group uu____4225
    | FStar_Parser_AST.Friend uid ->
        let uu____4230 =
          let uu____4231 = str "friend"  in
          let uu____4233 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4231 uu____4233  in
        FStar_Pprint.group uu____4230
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4236 =
          let uu____4237 = str "module"  in
          let uu____4239 =
            let uu____4240 =
              let uu____4241 = p_uident uid1  in
              let uu____4242 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4241 uu____4242  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4240  in
          FStar_Pprint.op_Hat_Hat uu____4237 uu____4239  in
        let uu____4243 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4236 uu____4243
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4245 =
          let uu____4246 = str "module"  in
          let uu____4248 =
            let uu____4249 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4249  in
          FStar_Pprint.op_Hat_Hat uu____4246 uu____4248  in
        FStar_Pprint.group uu____4245
    | FStar_Parser_AST.Tycon
        (true
         ,uu____4250,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____4287 = str "effect"  in
          let uu____4289 =
            let uu____4290 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4290  in
          FStar_Pprint.op_Hat_Hat uu____4287 uu____4289  in
        let uu____4291 =
          let uu____4292 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4292 FStar_Pprint.equals
           in
        let uu____4295 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4291 uu____4295
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____4326 =
          let uu____4327 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____4327  in
        let uu____4340 =
          let uu____4341 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4379 =
                    let uu____4380 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4380 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4379)) uu____4341
           in
        FStar_Pprint.op_Hat_Hat uu____4326 uu____4340
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4397 = str "let"  in
          let uu____4399 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4397 uu____4399  in
        let uu____4400 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4400 p_letbinding lbs
          (fun uu____4409  ->
             match uu____4409 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4418 = str "val"  in
        let uu____4420 =
          let uu____4421 =
            let uu____4422 = p_lident lid  in
            let uu____4423 =
              let uu____4424 =
                let uu____4425 =
                  let uu____4426 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4426  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4425  in
              FStar_Pprint.group uu____4424  in
            FStar_Pprint.op_Hat_Hat uu____4422 uu____4423  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4421  in
        FStar_Pprint.op_Hat_Hat uu____4418 uu____4420
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4432 =
            let uu____4434 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4434 FStar_Util.is_upper  in
          if uu____4432
          then FStar_Pprint.empty
          else
            (let uu____4442 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4442 FStar_Pprint.space)
           in
        let uu____4444 =
          let uu____4445 = p_ident id1  in
          let uu____4446 =
            let uu____4447 =
              let uu____4448 =
                let uu____4449 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4449  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4448  in
            FStar_Pprint.group uu____4447  in
          FStar_Pprint.op_Hat_Hat uu____4445 uu____4446  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4444
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4458 = str "exception"  in
        let uu____4460 =
          let uu____4461 =
            let uu____4462 = p_uident uid  in
            let uu____4463 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4467 =
                     let uu____4468 = str "of"  in
                     let uu____4470 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4468 uu____4470  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4467) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4462 uu____4463  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4461  in
        FStar_Pprint.op_Hat_Hat uu____4458 uu____4460
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4474 = str "new_effect"  in
        let uu____4476 =
          let uu____4477 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4477  in
        FStar_Pprint.op_Hat_Hat uu____4474 uu____4476
    | FStar_Parser_AST.SubEffect se ->
        let uu____4479 = str "sub_effect"  in
        let uu____4481 =
          let uu____4482 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4482  in
        FStar_Pprint.op_Hat_Hat uu____4479 uu____4481
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4485 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4485 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4486 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4488,uu____4489) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4517 = str "%splice"  in
        let uu____4519 =
          let uu____4520 =
            let uu____4521 = str ";"  in p_list p_uident uu____4521 ids  in
          let uu____4523 =
            let uu____4524 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4524  in
          FStar_Pprint.op_Hat_Hat uu____4520 uu____4523  in
        FStar_Pprint.op_Hat_Hat uu____4517 uu____4519

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_4527  ->
    match uu___115_4527 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4530 = str "#set-options"  in
        let uu____4532 =
          let uu____4533 =
            let uu____4534 = str s  in FStar_Pprint.dquotes uu____4534  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4533  in
        FStar_Pprint.op_Hat_Hat uu____4530 uu____4532
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4539 = str "#reset-options"  in
        let uu____4541 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4547 =
                 let uu____4548 = str s  in FStar_Pprint.dquotes uu____4548
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4547) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4539 uu____4541
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____4553 = str "#push-options"  in
        let uu____4555 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4561 =
                 let uu____4562 = str s  in FStar_Pprint.dquotes uu____4562
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4561) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4553 uu____4555
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4593  ->
      match uu____4593 with
      | (typedecl,fsdoc_opt) ->
          let uu____4606 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4606 with
           | (decl,body) ->
               let uu____4624 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4624)

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * (unit -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___116_4626  ->
      match uu___116_4626 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4656 = FStar_Pprint.empty  in
          let uu____4657 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4657, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4679 =
            let uu____4680 = p_typ false false t  in jump2 uu____4680  in
          let uu____4683 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4683, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4739 =
            match uu____4739 with
            | (lid1,t,doc_opt) ->
                let uu____4756 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4756
             in
          let p_fields uu____4772 =
            let uu____4773 =
              let uu____4774 =
                let uu____4775 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4775 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4774  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4773  in
          let uu____4784 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4784, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4849 =
            match uu____4849 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4878 =
                    let uu____4879 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4879  in
                  FStar_Range.extend_to_end_of_line uu____4878  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4907 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4921 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4921,
            ((fun uu____4928  ->
                let uu____4929 = datacon_doc ()  in jump2 uu____4929)))

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____4930  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4930 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4965 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4965  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4967 =
                        let uu____4970 =
                          let uu____4973 = p_fsdoc fsdoc  in
                          let uu____4974 =
                            let uu____4977 = cont lid_doc  in [uu____4977]
                             in
                          uu____4973 :: uu____4974  in
                        kw :: uu____4970  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4967
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4984 =
                        let uu____4985 =
                          let uu____4986 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4986 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4985
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4984
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5006 =
                          let uu____5007 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5007  in
                        prefix2 uu____5006 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5009  ->
      match uu____5009 with
      | (lid,t,doc_opt) ->
          let uu____5026 =
            let uu____5027 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5028 =
              let uu____5029 = p_lident lid  in
              let uu____5030 =
                let uu____5031 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5031  in
              FStar_Pprint.op_Hat_Hat uu____5029 uu____5030  in
            FStar_Pprint.op_Hat_Hat uu____5027 uu____5028  in
          FStar_Pprint.group uu____5026

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____5033  ->
    match uu____5033 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5067 =
            let uu____5068 =
              let uu____5069 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5069  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5068  in
          FStar_Pprint.group uu____5067  in
        let uu____5070 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5071 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5075 =
                 let uu____5076 =
                   let uu____5077 =
                     let uu____5078 =
                       let uu____5079 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5079
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5078  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5077  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5076  in
               FStar_Pprint.group uu____5075) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5070 uu____5071

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5083  ->
      match uu____5083 with
      | (pat,uu____5089) ->
          let uu____5090 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5109 =
                  let uu____5110 =
                    let uu____5111 =
                      let uu____5112 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5112
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5111  in
                  FStar_Pprint.group uu____5110  in
                (pat1, uu____5109)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5124 =
                  let uu____5125 =
                    let uu____5126 =
                      let uu____5127 =
                        let uu____5128 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5128
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5127
                       in
                    FStar_Pprint.group uu____5126  in
                  let uu____5129 =
                    let uu____5130 =
                      let uu____5131 = str "by"  in
                      let uu____5133 =
                        let uu____5134 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5134
                         in
                      FStar_Pprint.op_Hat_Hat uu____5131 uu____5133  in
                    FStar_Pprint.group uu____5130  in
                  FStar_Pprint.op_Hat_Hat uu____5125 uu____5129  in
                (pat1, uu____5124)
            | uu____5135 -> (pat, FStar_Pprint.empty)  in
          (match uu____5090 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5139);
                       FStar_Parser_AST.prange = uu____5140;_},pats)
                    ->
                    let uu____5150 =
                      let uu____5151 =
                        let uu____5152 =
                          let uu____5153 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5153  in
                        FStar_Pprint.group uu____5152  in
                      let uu____5154 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5151 uu____5154  in
                    prefix2_nonempty uu____5150 ascr_doc
                | uu____5155 ->
                    let uu____5156 =
                      let uu____5157 =
                        let uu____5158 =
                          let uu____5159 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5159  in
                        FStar_Pprint.group uu____5158  in
                      FStar_Pprint.op_Hat_Hat uu____5157 ascr_doc  in
                    FStar_Pprint.group uu____5156))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5161  ->
      match uu____5161 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____5172 =
            let uu____5173 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5173  in
          let uu____5174 =
            let uu____5175 =
              let uu____5176 =
                let uu____5177 =
                  let uu____5178 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5178  in
                FStar_Pprint.group uu____5177  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5176  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____5175  in
          FStar_Pprint.ifflat uu____5172 uu____5174

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_5179  ->
    match uu___117_5179 with
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
        let uu____5204 = p_uident uid  in
        let uu____5205 = p_binders true bs  in
        let uu____5207 =
          let uu____5208 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5208  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5204 uu____5205 uu____5207

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
          let uu____5223 =
            let uu____5224 =
              let uu____5225 =
                let uu____5226 = p_uident uid  in
                let uu____5227 = p_binders true bs  in
                let uu____5229 =
                  let uu____5230 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5230  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5226 uu____5227 uu____5229
                 in
              FStar_Pprint.group uu____5225  in
            let uu____5235 =
              let uu____5236 = str "with"  in
              let uu____5238 =
                let uu____5239 =
                  let uu____5240 =
                    let uu____5241 =
                      let uu____5242 =
                        let uu____5243 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5243
                         in
                      separate_map_last uu____5242 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5241  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5240  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5239  in
              FStar_Pprint.op_Hat_Hat uu____5236 uu____5238  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5224 uu____5235  in
          braces_with_nesting uu____5223

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____5247,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____5280 =
            let uu____5281 = p_lident lid  in
            let uu____5282 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5281 uu____5282  in
          let uu____5283 = p_simpleTerm ps false e  in
          prefix2 uu____5280 uu____5283
      | uu____5285 ->
          let uu____5286 =
            let uu____5288 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5288
             in
          failwith uu____5286

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5371 =
        match uu____5371 with
        | (kwd,t) ->
            let uu____5382 =
              let uu____5383 = str kwd  in
              let uu____5384 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5383 uu____5384  in
            let uu____5385 = p_simpleTerm ps false t  in
            prefix2 uu____5382 uu____5385
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5392 =
      let uu____5393 =
        let uu____5394 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5395 =
          let uu____5396 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5396  in
        FStar_Pprint.op_Hat_Hat uu____5394 uu____5395  in
      let uu____5398 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5393 uu____5398  in
    let uu____5399 =
      let uu____5400 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5400  in
    FStar_Pprint.op_Hat_Hat uu____5392 uu____5399

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_5401  ->
    match uu___118_5401 with
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
    | uu____5420 ->
        let uu____5421 =
          let uu____5422 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5422  in
        FStar_Pprint.op_Hat_Hat uu____5421 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_5425  ->
    match uu___119_5425 with
    | FStar_Parser_AST.Rec  ->
        let uu____5426 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5426
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_5428  ->
    match uu___120_5428 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____5432 = str "#["  in
        let uu____5434 =
          let uu____5435 = p_term false false t  in
          let uu____5438 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5435 uu____5438  in
        FStar_Pprint.op_Hat_Hat uu____5432 uu____5434

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____5444 =
          let uu____5445 =
            let uu____5446 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____5446  in
          FStar_Pprint.separate_map uu____5445 p_tuplePattern pats  in
        FStar_Pprint.group uu____5444
    | uu____5447 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____5456 =
          let uu____5457 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____5457 p_constructorPattern pats  in
        FStar_Pprint.group uu____5456
    | uu____5458 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____5461;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____5466 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____5467 = p_constructorPattern hd1  in
        let uu____5468 = p_constructorPattern tl1  in
        infix0 uu____5466 uu____5467 uu____5468
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____5470;_},pats)
        ->
        let uu____5476 = p_quident uid  in
        let uu____5477 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5476 uu____5477
    | uu____5478 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5494;
               FStar_Parser_AST.blevel = uu____5495;
               FStar_Parser_AST.aqual = uu____5496;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5505 =
               let uu____5506 = p_ident lid  in
               p_refinement aqual uu____5506 t1 phi  in
             soft_parens_with_nesting uu____5505
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5509;
               FStar_Parser_AST.blevel = uu____5510;
               FStar_Parser_AST.aqual = uu____5511;_},phi))
             ->
             let uu____5517 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____5517
         | uu____5518 ->
             let uu____5523 =
               let uu____5524 = p_tuplePattern pat  in
               let uu____5525 =
                 let uu____5526 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5526
                  in
               FStar_Pprint.op_Hat_Hat uu____5524 uu____5525  in
             soft_parens_with_nesting uu____5523)
    | FStar_Parser_AST.PatList pats ->
        let uu____5530 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5530 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5549 =
          match uu____5549 with
          | (lid,pat) ->
              let uu____5556 = p_qlident lid  in
              let uu____5557 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5556 uu____5557
           in
        let uu____5558 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5558
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5570 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5571 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5572 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5570 uu____5571 uu____5572
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5583 =
          let uu____5584 =
            let uu____5585 =
              let uu____5586 = FStar_Ident.text_of_id op  in str uu____5586
               in
            let uu____5588 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5585 uu____5588  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5584  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5583
    | FStar_Parser_AST.PatWild aqual ->
        let uu____5592 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____5592 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5600 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5601 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5600 uu____5601
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5603 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5607;
           FStar_Parser_AST.prange = uu____5608;_},uu____5609)
        ->
        let uu____5614 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5614
    | FStar_Parser_AST.PatTuple (uu____5615,false ) ->
        let uu____5622 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5622
    | uu____5623 ->
        let uu____5624 =
          let uu____5626 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5626  in
        failwith uu____5624

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5631;_},uu____5632)
        -> true
    | uu____5639 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5645 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5646 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5645 uu____5646
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5653;
                   FStar_Parser_AST.blevel = uu____5654;
                   FStar_Parser_AST.aqual = uu____5655;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5660 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5660 t1 phi
            | uu____5661 ->
                let t' =
                  let uu____5663 = is_typ_tuple t  in
                  if uu____5663
                  then
                    let uu____5666 = p_tmFormula t  in
                    soft_parens_with_nesting uu____5666
                  else p_tmFormula t  in
                let uu____5669 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5670 =
                  let uu____5671 = p_lident lid  in
                  let uu____5672 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____5671 uu____5672  in
                FStar_Pprint.op_Hat_Hat uu____5669 uu____5670
             in
          if is_atomic
          then
            let uu____5674 =
              let uu____5675 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5675  in
            FStar_Pprint.group uu____5674
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5678 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5686;
                  FStar_Parser_AST.blevel = uu____5687;
                  FStar_Parser_AST.aqual = uu____5688;_},phi)
               ->
               if is_atomic
               then
                 let uu____5693 =
                   let uu____5694 =
                     let uu____5695 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5695 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5694  in
                 FStar_Pprint.group uu____5693
               else
                 (let uu____5698 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5698)
           | uu____5699 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____5712 -> false
            | FStar_Parser_AST.App uu____5724 -> false
            | FStar_Parser_AST.Op uu____5732 -> false
            | uu____5740 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____5753 =
            let uu____5754 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____5755 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____5754 uu____5755  in
          let uu____5756 =
            let uu____5757 = p_appTerm t  in
            let uu____5758 =
              let uu____5759 =
                let uu____5760 =
                  let uu____5761 = soft_braces_with_nesting_tight phi1  in
                  let uu____5762 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____5761 uu____5762  in
                FStar_Pprint.group uu____5760  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____5759
               in
            FStar_Pprint.op_Hat_Hat uu____5757 uu____5758  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5753 uu____5756

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____5776 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____5776

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____5780 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____5783 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____5783)
       in
    if uu____5780
    then FStar_Pprint.underscore
    else (let uu____5788 = FStar_Ident.text_of_id lid  in str uu____5788)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____5791 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____5794 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____5794)
       in
    if uu____5791
    then FStar_Pprint.underscore
    else (let uu____5799 = FStar_Ident.text_of_lid lid  in str uu____5799)

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

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____5823 =
              let uu____5824 =
                let uu____5825 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5825 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5824  in
            let uu____5828 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5823 uu____5828
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5832 =
              let uu____5833 =
                let uu____5834 =
                  let uu____5835 = p_lident x  in
                  let uu____5836 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5835 uu____5836  in
                let uu____5837 =
                  let uu____5838 = p_noSeqTerm true false e1  in
                  let uu____5841 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5838 uu____5841  in
                op_Hat_Slash_Plus_Hat uu____5834 uu____5837  in
              FStar_Pprint.group uu____5833  in
            let uu____5842 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5832 uu____5842
        | uu____5843 ->
            let uu____5844 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5844

and (p_noSeqTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____5859 =
              let uu____5860 = p_tmIff e1  in
              let uu____5861 =
                let uu____5862 =
                  let uu____5863 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5863
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5862  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5860 uu____5861  in
            FStar_Pprint.group uu____5859
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5869 =
              let uu____5870 = p_tmIff e1  in
              let uu____5871 =
                let uu____5872 =
                  let uu____5873 =
                    let uu____5874 = p_typ false false t  in
                    let uu____5877 =
                      let uu____5878 = str "by"  in
                      let uu____5880 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5878 uu____5880  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5874 uu____5877  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5873
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5872  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5870 uu____5871  in
            FStar_Pprint.group uu____5869
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5881;_},e1::e2::e3::[])
            ->
            let uu____5888 =
              let uu____5889 =
                let uu____5890 =
                  let uu____5891 = p_atomicTermNotQUident e1  in
                  let uu____5892 =
                    let uu____5893 =
                      let uu____5894 =
                        let uu____5895 = p_term false false e2  in
                        soft_parens_with_nesting uu____5895  in
                      let uu____5898 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5894 uu____5898  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5893  in
                  FStar_Pprint.op_Hat_Hat uu____5891 uu____5892  in
                FStar_Pprint.group uu____5890  in
              let uu____5899 =
                let uu____5900 = p_noSeqTerm ps pb e3  in jump2 uu____5900
                 in
              FStar_Pprint.op_Hat_Hat uu____5889 uu____5899  in
            FStar_Pprint.group uu____5888
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5901;_},e1::e2::e3::[])
            ->
            let uu____5908 =
              let uu____5909 =
                let uu____5910 =
                  let uu____5911 = p_atomicTermNotQUident e1  in
                  let uu____5912 =
                    let uu____5913 =
                      let uu____5914 =
                        let uu____5915 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5915  in
                      let uu____5918 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5914 uu____5918  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5913  in
                  FStar_Pprint.op_Hat_Hat uu____5911 uu____5912  in
                FStar_Pprint.group uu____5910  in
              let uu____5919 =
                let uu____5920 = p_noSeqTerm ps pb e3  in jump2 uu____5920
                 in
              FStar_Pprint.op_Hat_Hat uu____5909 uu____5919  in
            FStar_Pprint.group uu____5908
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5930 =
              let uu____5931 = str "requires"  in
              let uu____5933 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5931 uu____5933  in
            FStar_Pprint.group uu____5930
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5943 =
              let uu____5944 = str "ensures"  in
              let uu____5946 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5944 uu____5946  in
            FStar_Pprint.group uu____5943
        | FStar_Parser_AST.Attributes es ->
            let uu____5950 =
              let uu____5951 = str "attributes"  in
              let uu____5953 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5951 uu____5953  in
            FStar_Pprint.group uu____5950
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5958 =
                let uu____5959 =
                  let uu____5960 = str "if"  in
                  let uu____5962 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5960 uu____5962  in
                let uu____5965 =
                  let uu____5966 = str "then"  in
                  let uu____5968 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5966 uu____5968  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5959 uu____5965  in
              FStar_Pprint.group uu____5958
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5972,uu____5973,e31) when
                     is_unit e31 ->
                     let uu____5975 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5975
                 | uu____5978 -> p_noSeqTerm false false e2  in
               let uu____5981 =
                 let uu____5982 =
                   let uu____5983 = str "if"  in
                   let uu____5985 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5983 uu____5985  in
                 let uu____5988 =
                   let uu____5989 =
                     let uu____5990 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5990 e2_doc  in
                   let uu____5992 =
                     let uu____5993 = str "else"  in
                     let uu____5995 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5993 uu____5995  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5989 uu____5992  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5982 uu____5988  in
               FStar_Pprint.group uu____5981)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____6018 =
              let uu____6019 =
                let uu____6020 =
                  let uu____6021 = str "try"  in
                  let uu____6023 = p_noSeqTerm false false e1  in
                  prefix2 uu____6021 uu____6023  in
                let uu____6026 =
                  let uu____6027 = str "with"  in
                  let uu____6029 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6027 uu____6029  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6020 uu____6026  in
              FStar_Pprint.group uu____6019  in
            let uu____6038 = paren_if (ps || pb)  in uu____6038 uu____6018
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____6065 =
              let uu____6066 =
                let uu____6067 =
                  let uu____6068 = str "match"  in
                  let uu____6070 = p_noSeqTerm false false e1  in
                  let uu____6073 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6068 uu____6070 uu____6073
                   in
                let uu____6077 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6067 uu____6077  in
              FStar_Pprint.group uu____6066  in
            let uu____6086 = paren_if (ps || pb)  in uu____6086 uu____6065
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____6093 =
              let uu____6094 =
                let uu____6095 =
                  let uu____6096 = str "let open"  in
                  let uu____6098 = p_quident uid  in
                  let uu____6099 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6096 uu____6098 uu____6099
                   in
                let uu____6103 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6095 uu____6103  in
              FStar_Pprint.group uu____6094  in
            let uu____6105 = paren_if ps  in uu____6105 uu____6093
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____6170 is_last =
              match uu____6170 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____6204 =
                          let uu____6205 = str "let"  in
                          let uu____6207 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6205 uu____6207
                           in
                        FStar_Pprint.group uu____6204
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____6210 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____6218 =
                    if is_last
                    then
                      let uu____6220 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____6221 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____6220 doc_expr uu____6221
                    else
                      (let uu____6227 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____6227)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____6218
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6278 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6278
                     else
                       (let uu____6289 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6289)) lbs
               in
            let lbs_doc =
              let uu____6299 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6299  in
            let uu____6300 =
              let uu____6301 =
                let uu____6302 =
                  let uu____6303 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6303
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6302  in
              FStar_Pprint.group uu____6301  in
            let uu____6305 = paren_if ps  in uu____6305 uu____6300
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6312;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6315;
                                                             FStar_Parser_AST.level
                                                               = uu____6316;_})
            when matches_var maybe_x x ->
            let uu____6343 =
              let uu____6344 =
                let uu____6345 = str "function"  in
                let uu____6347 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6345 uu____6347  in
              FStar_Pprint.group uu____6344  in
            let uu____6356 = paren_if (ps || pb)  in uu____6356 uu____6343
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____6362 =
              let uu____6363 = str "quote"  in
              let uu____6365 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6363 uu____6365  in
            FStar_Pprint.group uu____6362
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____6367 =
              let uu____6368 = str "`"  in
              let uu____6370 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6368 uu____6370  in
            FStar_Pprint.group uu____6367
        | FStar_Parser_AST.VQuote e1 ->
            let uu____6372 =
              let uu____6373 = str "`%"  in
              let uu____6375 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6373 uu____6375  in
            FStar_Pprint.group uu____6372
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____6377;
              FStar_Parser_AST.level = uu____6378;_}
            ->
            let uu____6379 =
              let uu____6380 = str "`@"  in
              let uu____6382 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6380 uu____6382  in
            FStar_Pprint.group uu____6379
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____6384 =
              let uu____6385 = str "`#"  in
              let uu____6387 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6385 uu____6387  in
            FStar_Pprint.group uu____6384
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____6396 = str "calc"  in
              let uu____6398 =
                let uu____6399 =
                  let uu____6400 = p_noSeqTerm false false rel  in
                  let uu____6403 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____6400 uu____6403  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6399  in
              FStar_Pprint.op_Hat_Hat uu____6396 uu____6398  in
            let bot = FStar_Pprint.rbrace  in
            let uu____6405 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____6406 =
              let uu____6407 =
                let uu____6408 =
                  let uu____6409 = p_noSeqTerm false false init1  in
                  let uu____6412 =
                    let uu____6413 = str ";"  in
                    let uu____6415 =
                      let uu____6416 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____6416
                       in
                    FStar_Pprint.op_Hat_Hat uu____6413 uu____6415  in
                  FStar_Pprint.op_Hat_Hat uu____6409 uu____6412  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6408  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____6407
               in
            FStar_Pprint.enclose head1 uu____6405 uu____6406
        | uu____6418 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____6419  ->
    fun uu____6420  ->
      match uu____6420 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____6425 =
            let uu____6426 = p_noSeqTerm false false rel  in
            let uu____6429 =
              let uu____6430 =
                let uu____6431 =
                  let uu____6432 =
                    let uu____6433 = p_noSeqTerm false false just  in
                    let uu____6436 =
                      let uu____6437 =
                        let uu____6438 =
                          let uu____6439 =
                            let uu____6440 = p_noSeqTerm false false next  in
                            let uu____6443 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____6440 uu____6443  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____6439
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____6438
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6437
                       in
                    FStar_Pprint.op_Hat_Hat uu____6433 uu____6436  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6432  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6431  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6430  in
            FStar_Pprint.op_Hat_Hat uu____6426 uu____6429  in
          FStar_Pprint.group uu____6425

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_6445  ->
    match uu___121_6445 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6457 =
          let uu____6458 = str "[@"  in
          let uu____6460 =
            let uu____6461 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____6462 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6461 uu____6462  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6458 uu____6460  in
        FStar_Pprint.group uu____6457

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6494 =
                   let uu____6495 =
                     let uu____6496 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6496 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6495 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6494 term_doc
             | pats ->
                 let uu____6504 =
                   let uu____6505 =
                     let uu____6506 =
                       let uu____6507 =
                         let uu____6508 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6508
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6507 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6511 = p_trigger trigger  in
                     prefix2 uu____6506 uu____6511  in
                   FStar_Pprint.group uu____6505  in
                 prefix2 uu____6504 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6532 =
                   let uu____6533 =
                     let uu____6534 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6534 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6533 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6532 term_doc
             | pats ->
                 let uu____6542 =
                   let uu____6543 =
                     let uu____6544 =
                       let uu____6545 =
                         let uu____6546 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6546
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6545 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6549 = p_trigger trigger  in
                     prefix2 uu____6544 uu____6549  in
                   FStar_Pprint.group uu____6543  in
                 prefix2 uu____6542 term_doc)
        | uu____6550 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6552 -> str "forall"
    | FStar_Parser_AST.QExists uu____6566 -> str "exists"
    | uu____6580 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_6582  ->
    match uu___122_6582 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6594 =
          let uu____6595 =
            let uu____6596 =
              let uu____6597 = str "pattern"  in
              let uu____6599 =
                let uu____6600 =
                  let uu____6601 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____6601
                   in
                FStar_Pprint.op_Hat_Hat uu____6600 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6597 uu____6599  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6596  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6595  in
        FStar_Pprint.group uu____6594

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6609 = str "\\/"  in
    FStar_Pprint.separate_map uu____6609 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6616 =
      let uu____6617 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____6617 p_appTerm pats  in
    FStar_Pprint.group uu____6616

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____6629 =
              let uu____6630 =
                let uu____6631 = str "fun"  in
                let uu____6633 =
                  let uu____6634 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6634
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____6631 uu____6633  in
              let uu____6635 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____6630 uu____6635  in
            let uu____6637 = paren_if ps  in uu____6637 uu____6629
        | uu____6642 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____6650  ->
      match uu____6650 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____6674 =
                    let uu____6675 =
                      let uu____6676 =
                        let uu____6677 = p_tuplePattern p  in
                        let uu____6678 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____6677 uu____6678  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6676
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6675  in
                  FStar_Pprint.group uu____6674
              | FStar_Pervasives_Native.Some f ->
                  let uu____6680 =
                    let uu____6681 =
                      let uu____6682 =
                        let uu____6683 =
                          let uu____6684 =
                            let uu____6685 = p_tuplePattern p  in
                            let uu____6686 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6685
                              uu____6686
                             in
                          FStar_Pprint.group uu____6684  in
                        let uu____6688 =
                          let uu____6689 =
                            let uu____6692 = p_tmFormula f  in
                            [uu____6692; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____6689  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6683 uu____6688
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6682
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6681  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____6680
               in
            let uu____6694 =
              let uu____6695 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____6695  in
            FStar_Pprint.group uu____6694  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____6705 =
                      let uu____6706 =
                        let uu____6707 =
                          let uu____6708 =
                            let uu____6709 =
                              let uu____6710 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____6710  in
                            FStar_Pprint.separate_map uu____6709
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6708
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6707
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6706  in
                    FStar_Pprint.group uu____6705
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6712 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____6714;_},e1::e2::[])
        ->
        let uu____6720 = str "<==>"  in
        let uu____6722 = p_tmImplies e1  in
        let uu____6723 = p_tmIff e2  in
        infix0 uu____6720 uu____6722 uu____6723
    | uu____6724 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____6726;_},e1::e2::[])
        ->
        let uu____6732 = str "==>"  in
        let uu____6734 = p_tmArrow p_tmFormula e1  in
        let uu____6735 = p_tmImplies e2  in
        infix0 uu____6732 uu____6734 uu____6735
    | uu____6736 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____6744 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____6744 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_5 when _0_5 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____6769 ->
               let uu____6770 =
                 let uu____6771 =
                   let uu____6772 =
                     let uu____6773 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6773
                      in
                   FStar_Pprint.separate uu____6772 terms  in
                 let uu____6774 =
                   let uu____6775 =
                     let uu____6776 =
                       let uu____6777 =
                         let uu____6778 =
                           let uu____6779 =
                             let uu____6780 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____6780
                              in
                           FStar_Pprint.separate uu____6779 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____6778 last_op  in
                       let uu____6781 =
                         let uu____6782 =
                           let uu____6783 =
                             let uu____6784 =
                               let uu____6785 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6785
                                in
                             FStar_Pprint.separate uu____6784 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____6783 last_op  in
                         jump2 uu____6782  in
                       FStar_Pprint.ifflat uu____6777 uu____6781  in
                     FStar_Pprint.group uu____6776  in
                   let uu____6786 = FStar_List.hd last1  in
                   prefix2 uu____6775 uu____6786  in
                 FStar_Pprint.ifflat uu____6771 uu____6774  in
               FStar_Pprint.group uu____6770)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____6799 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____6805 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____6799 uu____6805
      | uu____6808 -> let uu____6809 = p_Tm e  in [uu____6809]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____6812 =
        let uu____6813 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____6813 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6812  in
    let disj =
      let uu____6816 =
        let uu____6817 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____6817 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6816  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6837;_},e1::e2::[])
        ->
        let uu____6843 = p_tmDisjunction e1  in
        let uu____6848 = let uu____6853 = p_tmConjunction e2  in [uu____6853]
           in
        FStar_List.append uu____6843 uu____6848
    | uu____6862 -> let uu____6863 = p_tmConjunction e  in [uu____6863]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6873;_},e1::e2::[])
        ->
        let uu____6879 = p_tmConjunction e1  in
        let uu____6882 = let uu____6885 = p_tmTuple e2  in [uu____6885]  in
        FStar_List.append uu____6879 uu____6882
    | uu____6886 -> let uu____6887 = p_tmTuple e  in [uu____6887]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____6904 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____6904
          (fun uu____6912  ->
             match uu____6912 with | (e1,uu____6918) -> p_tmEq e1) args
    | uu____6919 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____6928 =
             let uu____6929 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6929  in
           FStar_Pprint.group uu____6928)

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
               (let uu____6948 = FStar_Ident.text_of_id op  in
                uu____6948 = "="))
              ||
              (let uu____6953 = FStar_Ident.text_of_id op  in
               uu____6953 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6959 = levels op1  in
            (match uu____6959 with
             | (left1,mine,right1) ->
                 let uu____6978 =
                   let uu____6979 = FStar_All.pipe_left str op1  in
                   let uu____6981 = p_tmEqWith' p_X left1 e1  in
                   let uu____6982 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6979 uu____6981 uu____6982  in
                 paren_if_gt curr mine uu____6978)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6983;_},e1::e2::[])
            ->
            let uu____6989 =
              let uu____6990 = p_tmEqWith p_X e1  in
              let uu____6991 =
                let uu____6992 =
                  let uu____6993 =
                    let uu____6994 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6994  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6993  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6992  in
              FStar_Pprint.op_Hat_Hat uu____6990 uu____6991  in
            FStar_Pprint.group uu____6989
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6995;_},e1::[])
            ->
            let uu____7000 = levels "-"  in
            (match uu____7000 with
             | (left1,mine,right1) ->
                 let uu____7020 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____7020)
        | uu____7021 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____7069)::(e2,uu____7071)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____7091 = is_list e  in Prims.op_Negation uu____7091)
              ->
              let op = "::"  in
              let uu____7096 = levels op  in
              (match uu____7096 with
               | (left1,mine,right1) ->
                   let uu____7115 =
                     let uu____7116 = str op  in
                     let uu____7117 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7119 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7116 uu____7117 uu____7119  in
                   paren_if_gt curr mine uu____7115)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____7138 = levels op  in
              (match uu____7138 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____7172 = p_binder false b  in
                         let uu____7174 =
                           let uu____7175 =
                             let uu____7176 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7176 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7175
                            in
                         FStar_Pprint.op_Hat_Hat uu____7172 uu____7174
                     | FStar_Util.Inr t ->
                         let uu____7178 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____7180 =
                           let uu____7181 =
                             let uu____7182 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7182 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7181
                            in
                         FStar_Pprint.op_Hat_Hat uu____7178 uu____7180
                      in
                   let uu____7183 =
                     let uu____7184 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____7189 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____7184 uu____7189  in
                   paren_if_gt curr mine uu____7183)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____7191;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____7221 = levels op  in
              (match uu____7221 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____7241 = str op  in
                     let uu____7242 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____7244 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____7241 uu____7242 uu____7244
                   else
                     (let uu____7248 =
                        let uu____7249 = str op  in
                        let uu____7250 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____7252 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____7249 uu____7250 uu____7252  in
                      paren_if_gt curr mine uu____7248))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____7261 = levels op1  in
              (match uu____7261 with
               | (left1,mine,right1) ->
                   let uu____7280 =
                     let uu____7281 = str op1  in
                     let uu____7282 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7284 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7281 uu____7282 uu____7284  in
                   paren_if_gt curr mine uu____7280)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____7304 =
                let uu____7305 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____7306 =
                  let uu____7307 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____7307 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____7305 uu____7306  in
              braces_with_nesting uu____7304
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____7312;_},e1::[])
              ->
              let uu____7317 =
                let uu____7318 = str "~"  in
                let uu____7320 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____7318 uu____7320  in
              FStar_Pprint.group uu____7317
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____7322;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____7331 = levels op  in
                   (match uu____7331 with
                    | (left1,mine,right1) ->
                        let uu____7350 =
                          let uu____7351 = str op  in
                          let uu____7352 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____7354 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____7351 uu____7352 uu____7354  in
                        paren_if_gt curr mine uu____7350)
               | uu____7356 -> p_X e)
          | uu____7357 -> p_X e

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
        let uu____7364 =
          let uu____7365 = p_lident lid  in
          let uu____7366 =
            let uu____7367 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7367  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7365 uu____7366  in
        FStar_Pprint.group uu____7364
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____7370 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____7372 = p_appTerm e  in
    let uu____7373 =
      let uu____7374 =
        let uu____7375 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____7375 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7374  in
    FStar_Pprint.op_Hat_Hat uu____7372 uu____7373

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____7381 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____7381 t phi
      | FStar_Parser_AST.TAnnotated uu____7382 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____7388 ->
          let uu____7389 =
            let uu____7391 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7391
             in
          failwith uu____7389
      | FStar_Parser_AST.TVariable uu____7394 ->
          let uu____7395 =
            let uu____7397 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7397
             in
          failwith uu____7395
      | FStar_Parser_AST.NoName uu____7400 ->
          let uu____7401 =
            let uu____7403 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7403
             in
          failwith uu____7401

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____7407  ->
      match uu____7407 with
      | (lid,e) ->
          let uu____7415 =
            let uu____7416 = p_qlident lid  in
            let uu____7417 =
              let uu____7418 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____7418
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____7416 uu____7417  in
          FStar_Pprint.group uu____7415

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____7421 when is_general_application e ->
        let uu____7428 = head_and_args e  in
        (match uu____7428 with
         | (head1,args) ->
             let uu____7453 =
               let uu____7464 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____7464
               then
                 let uu____7498 =
                   FStar_Util.take
                     (fun uu____7522  ->
                        match uu____7522 with
                        | (uu____7528,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____7498 with
                 | (fs_typ_args,args1) ->
                     let uu____7566 =
                       let uu____7567 = p_indexingTerm head1  in
                       let uu____7568 =
                         let uu____7569 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____7569 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____7567 uu____7568  in
                     (uu____7566, args1)
               else
                 (let uu____7584 = p_indexingTerm head1  in
                  (uu____7584, args))
                in
             (match uu____7453 with
              | (head_doc,args1) ->
                  let uu____7605 =
                    let uu____7606 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____7606 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____7605))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____7628 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____7628)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____7647 =
               let uu____7648 = p_quident lid  in
               let uu____7649 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____7648 uu____7649  in
             FStar_Pprint.group uu____7647
         | hd1::tl1 ->
             let uu____7666 =
               let uu____7667 =
                 let uu____7668 =
                   let uu____7669 = p_quident lid  in
                   let uu____7670 = p_argTerm hd1  in
                   prefix2 uu____7669 uu____7670  in
                 FStar_Pprint.group uu____7668  in
               let uu____7671 =
                 let uu____7672 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____7672  in
               FStar_Pprint.op_Hat_Hat uu____7667 uu____7671  in
             FStar_Pprint.group uu____7666)
    | uu____7677 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____7688 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____7688 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____7692 = str "#"  in
        let uu____7694 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____7692 uu____7694
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____7697 = str "#["  in
        let uu____7699 =
          let uu____7700 = p_indexingTerm t  in
          let uu____7701 =
            let uu____7702 = str "]"  in
            let uu____7704 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____7702 uu____7704  in
          FStar_Pprint.op_Hat_Hat uu____7700 uu____7701  in
        FStar_Pprint.op_Hat_Hat uu____7697 uu____7699
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____7706  ->
    match uu____7706 with | (e,uu____7712) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____7717;_},e1::e2::[])
          ->
          let uu____7723 =
            let uu____7724 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7725 =
              let uu____7726 =
                let uu____7727 = p_term false false e2  in
                soft_parens_with_nesting uu____7727  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7726  in
            FStar_Pprint.op_Hat_Hat uu____7724 uu____7725  in
          FStar_Pprint.group uu____7723
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____7730;_},e1::e2::[])
          ->
          let uu____7736 =
            let uu____7737 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7738 =
              let uu____7739 =
                let uu____7740 = p_term false false e2  in
                soft_brackets_with_nesting uu____7740  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7739  in
            FStar_Pprint.op_Hat_Hat uu____7737 uu____7738  in
          FStar_Pprint.group uu____7736
      | uu____7743 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____7748 = p_quident lid  in
        let uu____7749 =
          let uu____7750 =
            let uu____7751 = p_term false false e1  in
            soft_parens_with_nesting uu____7751  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7750  in
        FStar_Pprint.op_Hat_Hat uu____7748 uu____7749
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7759 =
          let uu____7760 = FStar_Ident.text_of_id op  in str uu____7760  in
        let uu____7762 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____7759 uu____7762
    | uu____7763 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____7774 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7783 =
          let uu____7784 = FStar_Ident.text_of_id op  in str uu____7784  in
        let uu____7786 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____7783 uu____7786
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____7790 =
          let uu____7791 =
            let uu____7792 =
              let uu____7793 = FStar_Ident.text_of_id op  in str uu____7793
               in
            let uu____7795 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____7792 uu____7795  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7791  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7790
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____7810 = all_explicit args  in
        if uu____7810
        then
          let uu____7813 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____7814 =
            let uu____7815 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____7816 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____7815 p_tmEq uu____7816  in
          let uu____7823 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____7813 uu____7814 uu____7823
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____7845 =
                 let uu____7846 = p_quident lid  in
                 let uu____7847 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7846 uu____7847  in
               FStar_Pprint.group uu____7845
           | hd1::tl1 ->
               let uu____7864 =
                 let uu____7865 =
                   let uu____7866 =
                     let uu____7867 = p_quident lid  in
                     let uu____7868 = p_argTerm hd1  in
                     prefix2 uu____7867 uu____7868  in
                   FStar_Pprint.group uu____7866  in
                 let uu____7869 =
                   let uu____7870 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____7870  in
                 FStar_Pprint.op_Hat_Hat uu____7865 uu____7869  in
               FStar_Pprint.group uu____7864)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____7877 =
          let uu____7878 = p_atomicTermNotQUident e1  in
          let uu____7879 =
            let uu____7880 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7880  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____7878 uu____7879
           in
        FStar_Pprint.group uu____7877
    | uu____7883 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____7888 = p_quident constr_lid  in
        let uu____7889 =
          let uu____7890 =
            let uu____7891 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7891  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7890  in
        FStar_Pprint.op_Hat_Hat uu____7888 uu____7889
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____7893 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____7893 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____7895 = p_term false false e1  in
        soft_parens_with_nesting uu____7895
    | uu____7898 when is_array e ->
        let es = extract_from_list e  in
        let uu____7902 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____7903 =
          let uu____7904 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____7904
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____7909 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7902 uu____7903 uu____7909
    | uu____7912 when is_list e ->
        let uu____7913 =
          let uu____7914 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7915 = extract_from_list e  in
          separate_map_or_flow_last uu____7914
            (fun ps  -> p_noSeqTerm ps false) uu____7915
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____7913 FStar_Pprint.rbracket
    | uu____7924 when is_lex_list e ->
        let uu____7925 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____7926 =
          let uu____7927 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7928 = extract_from_list e  in
          separate_map_or_flow_last uu____7927
            (fun ps  -> p_noSeqTerm ps false) uu____7928
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7925 uu____7926 FStar_Pprint.rbracket
    | uu____7937 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____7941 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____7942 =
          let uu____7943 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____7943 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7941 uu____7942 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____7953 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____7956 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____7953 uu____7956
    | FStar_Parser_AST.Op (op,args) when
        let uu____7965 = handleable_op op args  in
        Prims.op_Negation uu____7965 ->
        let uu____7967 =
          let uu____7969 =
            let uu____7971 = FStar_Ident.text_of_id op  in
            let uu____7973 =
              let uu____7975 =
                let uu____7977 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____7977
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____7975  in
            Prims.strcat uu____7971 uu____7973  in
          Prims.strcat "Operation " uu____7969  in
        failwith uu____7967
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7983 = str "u#"  in
        let uu____7985 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____7983 uu____7985
    | FStar_Parser_AST.Wild  ->
        let uu____7986 = p_term false false e  in
        soft_parens_with_nesting uu____7986
    | FStar_Parser_AST.Const uu____7989 ->
        let uu____7990 = p_term false false e  in
        soft_parens_with_nesting uu____7990
    | FStar_Parser_AST.Op uu____7993 ->
        let uu____8000 = p_term false false e  in
        soft_parens_with_nesting uu____8000
    | FStar_Parser_AST.Tvar uu____8003 ->
        let uu____8004 = p_term false false e  in
        soft_parens_with_nesting uu____8004
    | FStar_Parser_AST.Var uu____8007 ->
        let uu____8008 = p_term false false e  in
        soft_parens_with_nesting uu____8008
    | FStar_Parser_AST.Name uu____8011 ->
        let uu____8012 = p_term false false e  in
        soft_parens_with_nesting uu____8012
    | FStar_Parser_AST.Construct uu____8015 ->
        let uu____8026 = p_term false false e  in
        soft_parens_with_nesting uu____8026
    | FStar_Parser_AST.Abs uu____8029 ->
        let uu____8036 = p_term false false e  in
        soft_parens_with_nesting uu____8036
    | FStar_Parser_AST.App uu____8039 ->
        let uu____8046 = p_term false false e  in
        soft_parens_with_nesting uu____8046
    | FStar_Parser_AST.Let uu____8049 ->
        let uu____8070 = p_term false false e  in
        soft_parens_with_nesting uu____8070
    | FStar_Parser_AST.LetOpen uu____8073 ->
        let uu____8078 = p_term false false e  in
        soft_parens_with_nesting uu____8078
    | FStar_Parser_AST.Seq uu____8081 ->
        let uu____8086 = p_term false false e  in
        soft_parens_with_nesting uu____8086
    | FStar_Parser_AST.Bind uu____8089 ->
        let uu____8096 = p_term false false e  in
        soft_parens_with_nesting uu____8096
    | FStar_Parser_AST.If uu____8099 ->
        let uu____8106 = p_term false false e  in
        soft_parens_with_nesting uu____8106
    | FStar_Parser_AST.Match uu____8109 ->
        let uu____8124 = p_term false false e  in
        soft_parens_with_nesting uu____8124
    | FStar_Parser_AST.TryWith uu____8127 ->
        let uu____8142 = p_term false false e  in
        soft_parens_with_nesting uu____8142
    | FStar_Parser_AST.Ascribed uu____8145 ->
        let uu____8154 = p_term false false e  in
        soft_parens_with_nesting uu____8154
    | FStar_Parser_AST.Record uu____8157 ->
        let uu____8170 = p_term false false e  in
        soft_parens_with_nesting uu____8170
    | FStar_Parser_AST.Project uu____8173 ->
        let uu____8178 = p_term false false e  in
        soft_parens_with_nesting uu____8178
    | FStar_Parser_AST.Product uu____8181 ->
        let uu____8188 = p_term false false e  in
        soft_parens_with_nesting uu____8188
    | FStar_Parser_AST.Sum uu____8191 ->
        let uu____8202 = p_term false false e  in
        soft_parens_with_nesting uu____8202
    | FStar_Parser_AST.QForall uu____8205 ->
        let uu____8218 = p_term false false e  in
        soft_parens_with_nesting uu____8218
    | FStar_Parser_AST.QExists uu____8221 ->
        let uu____8234 = p_term false false e  in
        soft_parens_with_nesting uu____8234
    | FStar_Parser_AST.Refine uu____8237 ->
        let uu____8242 = p_term false false e  in
        soft_parens_with_nesting uu____8242
    | FStar_Parser_AST.NamedTyp uu____8245 ->
        let uu____8250 = p_term false false e  in
        soft_parens_with_nesting uu____8250
    | FStar_Parser_AST.Requires uu____8253 ->
        let uu____8261 = p_term false false e  in
        soft_parens_with_nesting uu____8261
    | FStar_Parser_AST.Ensures uu____8264 ->
        let uu____8272 = p_term false false e  in
        soft_parens_with_nesting uu____8272
    | FStar_Parser_AST.Attributes uu____8275 ->
        let uu____8278 = p_term false false e  in
        soft_parens_with_nesting uu____8278
    | FStar_Parser_AST.Quote uu____8281 ->
        let uu____8286 = p_term false false e  in
        soft_parens_with_nesting uu____8286
    | FStar_Parser_AST.VQuote uu____8289 ->
        let uu____8290 = p_term false false e  in
        soft_parens_with_nesting uu____8290
    | FStar_Parser_AST.Antiquote uu____8293 ->
        let uu____8294 = p_term false false e  in
        soft_parens_with_nesting uu____8294
    | FStar_Parser_AST.CalcProof uu____8297 ->
        let uu____8306 = p_term false false e  in
        soft_parens_with_nesting uu____8306

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_8309  ->
    match uu___125_8309 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____8318) ->
        let uu____8321 = str s  in FStar_Pprint.dquotes uu____8321
    | FStar_Const.Const_bytearray (bytes,uu____8323) ->
        let uu____8328 =
          let uu____8329 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____8329  in
        let uu____8330 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____8328 uu____8330
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_8353 =
          match uu___123_8353 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_8360 =
          match uu___124_8360 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____8375  ->
               match uu____8375 with
               | (s,w) ->
                   let uu____8382 = signedness s  in
                   let uu____8383 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____8382 uu____8383)
            sign_width_opt
           in
        let uu____8384 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____8384 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____8388 = FStar_Range.string_of_range r  in str uu____8388
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____8392 = p_quident lid  in
        let uu____8393 =
          let uu____8394 =
            let uu____8395 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8395  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____8394  in
        FStar_Pprint.op_Hat_Hat uu____8392 uu____8393

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____8398 = str "u#"  in
    let uu____8400 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____8398 uu____8400

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____8402;_},u1::u2::[])
        ->
        let uu____8408 =
          let uu____8409 = p_universeFrom u1  in
          let uu____8410 =
            let uu____8411 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____8411  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8409 uu____8410  in
        FStar_Pprint.group uu____8408
    | FStar_Parser_AST.App uu____8412 ->
        let uu____8419 = head_and_args u  in
        (match uu____8419 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____8445 =
                    let uu____8446 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____8447 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____8455  ->
                           match uu____8455 with
                           | (u1,uu____8461) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____8446 uu____8447  in
                  FStar_Pprint.group uu____8445
              | uu____8462 ->
                  let uu____8463 =
                    let uu____8465 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____8465
                     in
                  failwith uu____8463))
    | uu____8468 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____8494 = FStar_Ident.text_of_id id1  in str uu____8494
    | FStar_Parser_AST.Paren u1 ->
        let uu____8497 = p_universeFrom u1  in
        soft_parens_with_nesting uu____8497
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____8498;_},uu____8499::uu____8500::[])
        ->
        let uu____8504 = p_universeFrom u  in
        soft_parens_with_nesting uu____8504
    | FStar_Parser_AST.App uu____8505 ->
        let uu____8512 = p_universeFrom u  in
        soft_parens_with_nesting uu____8512
    | uu____8513 ->
        let uu____8514 =
          let uu____8516 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____8516
           in
        failwith uu____8514

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
       | FStar_Parser_AST.Module (uu____8605,decls) ->
           let uu____8611 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____8611
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____8620,decls,uu____8622) ->
           let uu____8629 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____8629
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____8689  ->
         match uu____8689 with | (comment,range) -> str comment) comments
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____8740,decls) -> decls
        | FStar_Parser_AST.Interface (uu____8746,decls,uu____8748) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____8800 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____8813;
                 FStar_Parser_AST.doc = uu____8814;
                 FStar_Parser_AST.quals = uu____8815;
                 FStar_Parser_AST.attrs = uu____8816;_}::uu____8817 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____8823 =
                   let uu____8826 =
                     let uu____8829 = FStar_List.tl ds  in d :: uu____8829
                      in
                   d0 :: uu____8826  in
                 (uu____8823, (d0.FStar_Parser_AST.drange))
             | uu____8834 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____8800 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____8897 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____8897 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____9004 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____9004, comments1))))))
  