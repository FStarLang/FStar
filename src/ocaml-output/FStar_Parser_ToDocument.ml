open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___126_43  ->
         match uu___126_43 with
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
  fun uu___127_1469  ->
    match uu___127_1469 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___128_1504  ->
      match uu___128_1504 with
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
  let levels_from_associativity l uu___129_1761 =
    match uu___129_1761 with
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
         (id1,uu____4015)) ->
          let uu____4018 =
            let uu____4020 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4020 FStar_Util.is_upper  in
          if uu____4018
          then
            let uu____4026 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4026 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4029 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4036 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____4037 =
      let uu____4038 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4039 =
        let uu____4040 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4040  in
      FStar_Pprint.op_Hat_Hat uu____4038 uu____4039  in
    FStar_Pprint.op_Hat_Hat uu____4036 uu____4037

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4042 ->
        let uu____4043 =
          let uu____4044 = str "@ "  in
          let uu____4046 =
            let uu____4047 =
              let uu____4048 =
                let uu____4049 =
                  let uu____4050 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4050  in
                FStar_Pprint.op_Hat_Hat uu____4049 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4048  in
            FStar_Pprint.op_Hat_Hat uu____4047 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4044 uu____4046  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4043

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4053  ->
    match uu____4053 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4101 =
                match uu____4101 with
                | (kwd,arg) ->
                    let uu____4114 = str "@"  in
                    let uu____4116 =
                      let uu____4117 = str kwd  in
                      let uu____4118 =
                        let uu____4119 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4119
                         in
                      FStar_Pprint.op_Hat_Hat uu____4117 uu____4118  in
                    FStar_Pprint.op_Hat_Hat uu____4114 uu____4116
                 in
              let uu____4120 =
                let uu____4121 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____4121 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4120
           in
        let uu____4128 =
          let uu____4129 =
            let uu____4130 =
              let uu____4131 =
                let uu____4132 = str doc1  in
                let uu____4133 =
                  let uu____4134 =
                    let uu____4135 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4135  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4134  in
                FStar_Pprint.op_Hat_Hat uu____4132 uu____4133  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4131  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4130  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4129  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4128

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4139 =
          let uu____4140 = str "val"  in
          let uu____4142 =
            let uu____4143 =
              let uu____4144 = p_lident lid  in
              let uu____4145 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4144 uu____4145  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4143  in
          FStar_Pprint.op_Hat_Hat uu____4140 uu____4142  in
        let uu____4146 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4139 uu____4146
    | FStar_Parser_AST.TopLevelLet (uu____4149,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4174 =
               let uu____4175 = str "let"  in p_letlhs uu____4175 lb  in
             FStar_Pprint.group uu____4174) lbs
    | uu____4177 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___130_4192 =
          match uu___130_4192 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4200 = f x  in
              let uu____4201 =
                let uu____4202 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4202  in
              FStar_Pprint.op_Hat_Hat uu____4200 uu____4201
           in
        let uu____4203 = str "["  in
        let uu____4205 =
          let uu____4206 = p_list' l  in
          let uu____4207 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4206 uu____4207  in
        FStar_Pprint.op_Hat_Hat uu____4203 uu____4205

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4211 =
          let uu____4212 = str "open"  in
          let uu____4214 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4212 uu____4214  in
        FStar_Pprint.group uu____4211
    | FStar_Parser_AST.Include uid ->
        let uu____4216 =
          let uu____4217 = str "include"  in
          let uu____4219 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4217 uu____4219  in
        FStar_Pprint.group uu____4216
    | FStar_Parser_AST.Friend uid ->
        let uu____4221 =
          let uu____4222 = str "friend"  in
          let uu____4224 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4222 uu____4224  in
        FStar_Pprint.group uu____4221
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4227 =
          let uu____4228 = str "module"  in
          let uu____4230 =
            let uu____4231 =
              let uu____4232 = p_uident uid1  in
              let uu____4233 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4232 uu____4233  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4231  in
          FStar_Pprint.op_Hat_Hat uu____4228 uu____4230  in
        let uu____4234 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4227 uu____4234
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4236 =
          let uu____4237 = str "module"  in
          let uu____4239 =
            let uu____4240 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4240  in
          FStar_Pprint.op_Hat_Hat uu____4237 uu____4239  in
        FStar_Pprint.group uu____4236
    | FStar_Parser_AST.Tycon
        (true
         ,uu____4241,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____4278 = str "effect"  in
          let uu____4280 =
            let uu____4281 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4281  in
          FStar_Pprint.op_Hat_Hat uu____4278 uu____4280  in
        let uu____4282 =
          let uu____4283 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4283 FStar_Pprint.equals
           in
        let uu____4286 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4282 uu____4286
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____4317 =
          let uu____4318 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____4318  in
        let uu____4331 =
          let uu____4332 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4370 =
                    let uu____4371 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4371 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4370)) uu____4332
           in
        FStar_Pprint.op_Hat_Hat uu____4317 uu____4331
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4388 = str "let"  in
          let uu____4390 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4388 uu____4390  in
        let uu____4391 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4391 p_letbinding lbs
          (fun uu____4400  ->
             match uu____4400 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4409 = str "val"  in
        let uu____4411 =
          let uu____4412 =
            let uu____4413 = p_lident lid  in
            let uu____4414 =
              let uu____4415 =
                let uu____4416 =
                  let uu____4417 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4417  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4416  in
              FStar_Pprint.group uu____4415  in
            FStar_Pprint.op_Hat_Hat uu____4413 uu____4414  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4412  in
        FStar_Pprint.op_Hat_Hat uu____4409 uu____4411
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4423 =
            let uu____4425 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4425 FStar_Util.is_upper  in
          if uu____4423
          then FStar_Pprint.empty
          else
            (let uu____4433 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4433 FStar_Pprint.space)
           in
        let uu____4435 =
          let uu____4436 = p_ident id1  in
          let uu____4437 =
            let uu____4438 =
              let uu____4439 =
                let uu____4440 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4440  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4439  in
            FStar_Pprint.group uu____4438  in
          FStar_Pprint.op_Hat_Hat uu____4436 uu____4437  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4435
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4449 = str "exception"  in
        let uu____4451 =
          let uu____4452 =
            let uu____4453 = p_uident uid  in
            let uu____4454 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4458 =
                     let uu____4459 = str "of"  in
                     let uu____4461 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4459 uu____4461  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4458) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4453 uu____4454  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4452  in
        FStar_Pprint.op_Hat_Hat uu____4449 uu____4451
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4465 = str "new_effect"  in
        let uu____4467 =
          let uu____4468 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4468  in
        FStar_Pprint.op_Hat_Hat uu____4465 uu____4467
    | FStar_Parser_AST.SubEffect se ->
        let uu____4470 = str "sub_effect"  in
        let uu____4472 =
          let uu____4473 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4473  in
        FStar_Pprint.op_Hat_Hat uu____4470 uu____4472
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4476 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4476 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4477 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4479,uu____4480) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4508 = str "%splice"  in
        let uu____4510 =
          let uu____4511 =
            let uu____4512 = str ";"  in p_list p_uident uu____4512 ids  in
          let uu____4514 =
            let uu____4515 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4515  in
          FStar_Pprint.op_Hat_Hat uu____4511 uu____4514  in
        FStar_Pprint.op_Hat_Hat uu____4508 uu____4510

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___131_4518  ->
    match uu___131_4518 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4521 = str "#set-options"  in
        let uu____4523 =
          let uu____4524 =
            let uu____4525 = str s  in FStar_Pprint.dquotes uu____4525  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4524  in
        FStar_Pprint.op_Hat_Hat uu____4521 uu____4523
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4530 = str "#reset-options"  in
        let uu____4532 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4538 =
                 let uu____4539 = str s  in FStar_Pprint.dquotes uu____4539
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4538) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4530 uu____4532
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____4544 = str "#push-options"  in
        let uu____4546 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4552 =
                 let uu____4553 = str s  in FStar_Pprint.dquotes uu____4553
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4552) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4544 uu____4546
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
    fun uu____4584  ->
      match uu____4584 with
      | (typedecl,fsdoc_opt) ->
          let uu____4597 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4597 with
           | (decl,body) ->
               let uu____4615 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4615)

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * (unit -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___132_4617  ->
      match uu___132_4617 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4647 = FStar_Pprint.empty  in
          let uu____4648 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4648, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4670 =
            let uu____4671 = p_typ false false t  in jump2 uu____4671  in
          let uu____4674 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4674, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4730 =
            match uu____4730 with
            | (lid1,t,doc_opt) ->
                let uu____4747 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4747
             in
          let p_fields uu____4763 =
            let uu____4764 =
              let uu____4765 =
                let uu____4766 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4766 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4765  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4764  in
          let uu____4775 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4775, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4840 =
            match uu____4840 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4869 =
                    let uu____4870 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4870  in
                  FStar_Range.extend_to_end_of_line uu____4869  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4898 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4912 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4912,
            ((fun uu____4919  ->
                let uu____4920 = datacon_doc ()  in jump2 uu____4920)))

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____4921  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4921 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4956 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4956  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4958 =
                        let uu____4961 =
                          let uu____4964 = p_fsdoc fsdoc  in
                          let uu____4965 =
                            let uu____4968 = cont lid_doc  in [uu____4968]
                             in
                          uu____4964 :: uu____4965  in
                        kw :: uu____4961  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4958
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4975 =
                        let uu____4976 =
                          let uu____4977 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4977 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4976
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4975
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4997 =
                          let uu____4998 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4998  in
                        prefix2 uu____4997 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5000  ->
      match uu____5000 with
      | (lid,t,doc_opt) ->
          let uu____5017 =
            let uu____5018 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5019 =
              let uu____5020 = p_lident lid  in
              let uu____5021 =
                let uu____5022 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5022  in
              FStar_Pprint.op_Hat_Hat uu____5020 uu____5021  in
            FStar_Pprint.op_Hat_Hat uu____5018 uu____5019  in
          FStar_Pprint.group uu____5017

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____5024  ->
    match uu____5024 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5058 =
            let uu____5059 =
              let uu____5060 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5060  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5059  in
          FStar_Pprint.group uu____5058  in
        let uu____5061 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5062 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5066 =
                 let uu____5067 =
                   let uu____5068 =
                     let uu____5069 =
                       let uu____5070 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5070
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5069  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5068  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5067  in
               FStar_Pprint.group uu____5066) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5061 uu____5062

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5074  ->
      match uu____5074 with
      | (pat,uu____5080) ->
          let uu____5081 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5100 =
                  let uu____5101 =
                    let uu____5102 =
                      let uu____5103 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5103
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5102  in
                  FStar_Pprint.group uu____5101  in
                (pat1, uu____5100)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5115 =
                  let uu____5116 =
                    let uu____5117 =
                      let uu____5118 =
                        let uu____5119 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5119
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5118
                       in
                    FStar_Pprint.group uu____5117  in
                  let uu____5120 =
                    let uu____5121 =
                      let uu____5122 = str "by"  in
                      let uu____5124 =
                        let uu____5125 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5125
                         in
                      FStar_Pprint.op_Hat_Hat uu____5122 uu____5124  in
                    FStar_Pprint.group uu____5121  in
                  FStar_Pprint.op_Hat_Hat uu____5116 uu____5120  in
                (pat1, uu____5115)
            | uu____5126 -> (pat, FStar_Pprint.empty)  in
          (match uu____5081 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5130);
                       FStar_Parser_AST.prange = uu____5131;_},pats)
                    ->
                    let uu____5141 =
                      let uu____5142 =
                        let uu____5143 =
                          let uu____5144 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5144  in
                        FStar_Pprint.group uu____5143  in
                      let uu____5145 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5142 uu____5145  in
                    prefix2_nonempty uu____5141 ascr_doc
                | uu____5146 ->
                    let uu____5147 =
                      let uu____5148 =
                        let uu____5149 =
                          let uu____5150 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5150  in
                        FStar_Pprint.group uu____5149  in
                      FStar_Pprint.op_Hat_Hat uu____5148 ascr_doc  in
                    FStar_Pprint.group uu____5147))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5152  ->
      match uu____5152 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____5163 =
            let uu____5164 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5164  in
          let uu____5165 =
            let uu____5166 =
              let uu____5167 =
                let uu____5168 =
                  let uu____5169 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5169  in
                FStar_Pprint.group uu____5168  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5167  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____5166  in
          FStar_Pprint.ifflat uu____5163 uu____5165

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___133_5170  ->
    match uu___133_5170 with
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
        let uu____5195 = p_uident uid  in
        let uu____5196 = p_binders true bs  in
        let uu____5198 =
          let uu____5199 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5199  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5195 uu____5196 uu____5198

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
          let uu____5214 =
            let uu____5215 =
              let uu____5216 =
                let uu____5217 = p_uident uid  in
                let uu____5218 = p_binders true bs  in
                let uu____5220 =
                  let uu____5221 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5221  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5217 uu____5218 uu____5220
                 in
              FStar_Pprint.group uu____5216  in
            let uu____5226 =
              let uu____5227 = str "with"  in
              let uu____5229 =
                let uu____5230 =
                  let uu____5231 =
                    let uu____5232 =
                      let uu____5233 =
                        let uu____5234 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5234
                         in
                      separate_map_last uu____5233 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5232  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5231  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5230  in
              FStar_Pprint.op_Hat_Hat uu____5227 uu____5229  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5215 uu____5226  in
          braces_with_nesting uu____5214

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____5238,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____5271 =
            let uu____5272 = p_lident lid  in
            let uu____5273 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5272 uu____5273  in
          let uu____5274 = p_simpleTerm ps false e  in
          prefix2 uu____5271 uu____5274
      | uu____5276 ->
          let uu____5277 =
            let uu____5279 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5279
             in
          failwith uu____5277

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5362 =
        match uu____5362 with
        | (kwd,t) ->
            let uu____5373 =
              let uu____5374 = str kwd  in
              let uu____5375 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5374 uu____5375  in
            let uu____5376 = p_simpleTerm ps false t  in
            prefix2 uu____5373 uu____5376
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5383 =
      let uu____5384 =
        let uu____5385 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5386 =
          let uu____5387 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5387  in
        FStar_Pprint.op_Hat_Hat uu____5385 uu____5386  in
      let uu____5389 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5384 uu____5389  in
    let uu____5390 =
      let uu____5391 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5391  in
    FStar_Pprint.op_Hat_Hat uu____5383 uu____5390

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___134_5392  ->
    match uu___134_5392 with
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
    | uu____5411 ->
        let uu____5412 =
          let uu____5413 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5413  in
        FStar_Pprint.op_Hat_Hat uu____5412 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___135_5416  ->
    match uu___135_5416 with
    | FStar_Parser_AST.Rec  ->
        let uu____5417 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5417
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___136_5419  ->
    match uu___136_5419 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____5423 = str "#["  in
        let uu____5425 =
          let uu____5426 = p_term false false t  in
          let uu____5429 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5426 uu____5429  in
        FStar_Pprint.op_Hat_Hat uu____5423 uu____5425

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____5435 =
          let uu____5436 =
            let uu____5437 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____5437  in
          FStar_Pprint.separate_map uu____5436 p_tuplePattern pats  in
        FStar_Pprint.group uu____5435
    | uu____5438 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____5447 =
          let uu____5448 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____5448 p_constructorPattern pats  in
        FStar_Pprint.group uu____5447
    | uu____5449 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____5452;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____5457 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____5458 = p_constructorPattern hd1  in
        let uu____5459 = p_constructorPattern tl1  in
        infix0 uu____5457 uu____5458 uu____5459
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____5461;_},pats)
        ->
        let uu____5467 = p_quident uid  in
        let uu____5468 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5467 uu____5468
    | uu____5469 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5485;
               FStar_Parser_AST.blevel = uu____5486;
               FStar_Parser_AST.aqual = uu____5487;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5496 =
               let uu____5497 = p_ident lid  in
               p_refinement aqual uu____5497 t1 phi  in
             soft_parens_with_nesting uu____5496
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5500;
               FStar_Parser_AST.blevel = uu____5501;
               FStar_Parser_AST.aqual = uu____5502;_},phi))
             ->
             let uu____5508 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____5508
         | uu____5509 ->
             let uu____5514 =
               let uu____5515 = p_tuplePattern pat  in
               let uu____5516 =
                 let uu____5517 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5517
                  in
               FStar_Pprint.op_Hat_Hat uu____5515 uu____5516  in
             soft_parens_with_nesting uu____5514)
    | FStar_Parser_AST.PatList pats ->
        let uu____5521 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5521 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5540 =
          match uu____5540 with
          | (lid,pat) ->
              let uu____5547 = p_qlident lid  in
              let uu____5548 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5547 uu____5548
           in
        let uu____5549 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5549
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5561 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5562 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5563 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5561 uu____5562 uu____5563
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5574 =
          let uu____5575 =
            let uu____5576 =
              let uu____5577 = FStar_Ident.text_of_id op  in str uu____5577
               in
            let uu____5579 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5576 uu____5579  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5575  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5574
    | FStar_Parser_AST.PatWild aqual ->
        let uu____5583 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____5583 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5591 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5592 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5591 uu____5592
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5594 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5598;
           FStar_Parser_AST.prange = uu____5599;_},uu____5600)
        ->
        let uu____5605 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5605
    | FStar_Parser_AST.PatTuple (uu____5606,false ) ->
        let uu____5613 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5613
    | uu____5614 ->
        let uu____5615 =
          let uu____5617 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5617  in
        failwith uu____5615

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5622;_},uu____5623)
        -> true
    | uu____5630 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5636 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5637 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5636 uu____5637
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5644;
                   FStar_Parser_AST.blevel = uu____5645;
                   FStar_Parser_AST.aqual = uu____5646;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5651 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5651 t1 phi
            | uu____5652 ->
                let t' =
                  let uu____5654 = is_typ_tuple t  in
                  if uu____5654
                  then
                    let uu____5657 = p_tmFormula t  in
                    soft_parens_with_nesting uu____5657
                  else p_tmFormula t  in
                let uu____5660 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5661 =
                  let uu____5662 = p_lident lid  in
                  let uu____5663 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____5662 uu____5663  in
                FStar_Pprint.op_Hat_Hat uu____5660 uu____5661
             in
          if is_atomic
          then
            let uu____5665 =
              let uu____5666 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5666  in
            FStar_Pprint.group uu____5665
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5669 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5677;
                  FStar_Parser_AST.blevel = uu____5678;
                  FStar_Parser_AST.aqual = uu____5679;_},phi)
               ->
               if is_atomic
               then
                 let uu____5684 =
                   let uu____5685 =
                     let uu____5686 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5686 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5685  in
                 FStar_Pprint.group uu____5684
               else
                 (let uu____5689 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5689)
           | uu____5690 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____5703 -> false
            | FStar_Parser_AST.App uu____5715 -> false
            | FStar_Parser_AST.Op uu____5723 -> false
            | uu____5731 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____5744 =
            let uu____5745 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____5746 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____5745 uu____5746  in
          let uu____5747 =
            let uu____5748 = p_appTerm t  in
            let uu____5749 =
              let uu____5750 =
                let uu____5751 =
                  let uu____5752 = soft_braces_with_nesting_tight phi1  in
                  let uu____5753 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____5752 uu____5753  in
                FStar_Pprint.group uu____5751  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____5750
               in
            FStar_Pprint.op_Hat_Hat uu____5748 uu____5749  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5744 uu____5747

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____5767 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____5767

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____5771 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____5774 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____5774)
       in
    if uu____5771
    then FStar_Pprint.underscore
    else (let uu____5779 = FStar_Ident.text_of_id lid  in str uu____5779)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____5782 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____5785 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____5785)
       in
    if uu____5782
    then FStar_Pprint.underscore
    else (let uu____5790 = FStar_Ident.text_of_lid lid  in str uu____5790)

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
            let uu____5814 =
              let uu____5815 =
                let uu____5816 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5816 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5815  in
            let uu____5819 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5814 uu____5819
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5823 =
              let uu____5824 =
                let uu____5825 =
                  let uu____5826 = p_lident x  in
                  let uu____5827 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5826 uu____5827  in
                let uu____5828 =
                  let uu____5829 = p_noSeqTerm true false e1  in
                  let uu____5832 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5829 uu____5832  in
                op_Hat_Slash_Plus_Hat uu____5825 uu____5828  in
              FStar_Pprint.group uu____5824  in
            let uu____5833 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5823 uu____5833
        | uu____5834 ->
            let uu____5835 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5835

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
            let uu____5850 =
              let uu____5851 = p_tmIff e1  in
              let uu____5852 =
                let uu____5853 =
                  let uu____5854 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5854
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5853  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5851 uu____5852  in
            FStar_Pprint.group uu____5850
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5860 =
              let uu____5861 = p_tmIff e1  in
              let uu____5862 =
                let uu____5863 =
                  let uu____5864 =
                    let uu____5865 = p_typ false false t  in
                    let uu____5868 =
                      let uu____5869 = str "by"  in
                      let uu____5871 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5869 uu____5871  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5865 uu____5868  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5864
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5863  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5861 uu____5862  in
            FStar_Pprint.group uu____5860
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5872;_},e1::e2::e3::[])
            ->
            let uu____5879 =
              let uu____5880 =
                let uu____5881 =
                  let uu____5882 = p_atomicTermNotQUident e1  in
                  let uu____5883 =
                    let uu____5884 =
                      let uu____5885 =
                        let uu____5886 = p_term false false e2  in
                        soft_parens_with_nesting uu____5886  in
                      let uu____5889 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5885 uu____5889  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5884  in
                  FStar_Pprint.op_Hat_Hat uu____5882 uu____5883  in
                FStar_Pprint.group uu____5881  in
              let uu____5890 =
                let uu____5891 = p_noSeqTerm ps pb e3  in jump2 uu____5891
                 in
              FStar_Pprint.op_Hat_Hat uu____5880 uu____5890  in
            FStar_Pprint.group uu____5879
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5892;_},e1::e2::e3::[])
            ->
            let uu____5899 =
              let uu____5900 =
                let uu____5901 =
                  let uu____5902 = p_atomicTermNotQUident e1  in
                  let uu____5903 =
                    let uu____5904 =
                      let uu____5905 =
                        let uu____5906 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5906  in
                      let uu____5909 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5905 uu____5909  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5904  in
                  FStar_Pprint.op_Hat_Hat uu____5902 uu____5903  in
                FStar_Pprint.group uu____5901  in
              let uu____5910 =
                let uu____5911 = p_noSeqTerm ps pb e3  in jump2 uu____5911
                 in
              FStar_Pprint.op_Hat_Hat uu____5900 uu____5910  in
            FStar_Pprint.group uu____5899
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5921 =
              let uu____5922 = str "requires"  in
              let uu____5924 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5922 uu____5924  in
            FStar_Pprint.group uu____5921
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5934 =
              let uu____5935 = str "ensures"  in
              let uu____5937 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5935 uu____5937  in
            FStar_Pprint.group uu____5934
        | FStar_Parser_AST.Attributes es ->
            let uu____5941 =
              let uu____5942 = str "attributes"  in
              let uu____5944 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5942 uu____5944  in
            FStar_Pprint.group uu____5941
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5949 =
                let uu____5950 =
                  let uu____5951 = str "if"  in
                  let uu____5953 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5951 uu____5953  in
                let uu____5956 =
                  let uu____5957 = str "then"  in
                  let uu____5959 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5957 uu____5959  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5950 uu____5956  in
              FStar_Pprint.group uu____5949
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5963,uu____5964,e31) when
                     is_unit e31 ->
                     let uu____5966 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5966
                 | uu____5969 -> p_noSeqTerm false false e2  in
               let uu____5972 =
                 let uu____5973 =
                   let uu____5974 = str "if"  in
                   let uu____5976 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5974 uu____5976  in
                 let uu____5979 =
                   let uu____5980 =
                     let uu____5981 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5981 e2_doc  in
                   let uu____5983 =
                     let uu____5984 = str "else"  in
                     let uu____5986 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5984 uu____5986  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5980 uu____5983  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5973 uu____5979  in
               FStar_Pprint.group uu____5972)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____6009 =
              let uu____6010 =
                let uu____6011 =
                  let uu____6012 = str "try"  in
                  let uu____6014 = p_noSeqTerm false false e1  in
                  prefix2 uu____6012 uu____6014  in
                let uu____6017 =
                  let uu____6018 = str "with"  in
                  let uu____6020 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6018 uu____6020  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6011 uu____6017  in
              FStar_Pprint.group uu____6010  in
            let uu____6029 = paren_if (ps || pb)  in uu____6029 uu____6009
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____6056 =
              let uu____6057 =
                let uu____6058 =
                  let uu____6059 = str "match"  in
                  let uu____6061 = p_noSeqTerm false false e1  in
                  let uu____6064 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6059 uu____6061 uu____6064
                   in
                let uu____6068 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6058 uu____6068  in
              FStar_Pprint.group uu____6057  in
            let uu____6077 = paren_if (ps || pb)  in uu____6077 uu____6056
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____6084 =
              let uu____6085 =
                let uu____6086 =
                  let uu____6087 = str "let open"  in
                  let uu____6089 = p_quident uid  in
                  let uu____6090 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____6087 uu____6089 uu____6090
                   in
                let uu____6094 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6086 uu____6094  in
              FStar_Pprint.group uu____6085  in
            let uu____6096 = paren_if ps  in uu____6096 uu____6084
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____6161 is_last =
              match uu____6161 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____6195 =
                          let uu____6196 = str "let"  in
                          let uu____6198 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6196 uu____6198
                           in
                        FStar_Pprint.group uu____6195
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____6201 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____6209 =
                    if is_last
                    then
                      let uu____6211 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____6212 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____6211 doc_expr uu____6212
                    else
                      (let uu____6218 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____6218)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____6209
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6269 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6269
                     else
                       (let uu____6280 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6280)) lbs
               in
            let lbs_doc =
              let uu____6290 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6290  in
            let uu____6291 =
              let uu____6292 =
                let uu____6293 =
                  let uu____6294 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6294
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6293  in
              FStar_Pprint.group uu____6292  in
            let uu____6296 = paren_if ps  in uu____6296 uu____6291
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6303;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6306;
                                                             FStar_Parser_AST.level
                                                               = uu____6307;_})
            when matches_var maybe_x x ->
            let uu____6334 =
              let uu____6335 =
                let uu____6336 = str "function"  in
                let uu____6338 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6336 uu____6338  in
              FStar_Pprint.group uu____6335  in
            let uu____6347 = paren_if (ps || pb)  in uu____6347 uu____6334
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____6353 =
              let uu____6354 = str "quote"  in
              let uu____6356 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6354 uu____6356  in
            FStar_Pprint.group uu____6353
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____6358 =
              let uu____6359 = str "`"  in
              let uu____6361 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6359 uu____6361  in
            FStar_Pprint.group uu____6358
        | FStar_Parser_AST.VQuote e1 ->
            let uu____6363 =
              let uu____6364 = str "`%"  in
              let uu____6366 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6364 uu____6366  in
            FStar_Pprint.group uu____6363
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____6368;
              FStar_Parser_AST.level = uu____6369;_}
            ->
            let uu____6370 =
              let uu____6371 = str "`@"  in
              let uu____6373 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6371 uu____6373  in
            FStar_Pprint.group uu____6370
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____6375 =
              let uu____6376 = str "`#"  in
              let uu____6378 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6376 uu____6378  in
            FStar_Pprint.group uu____6375
        | uu____6379 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___137_6380  ->
    match uu___137_6380 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6392 =
          let uu____6393 = str "[@"  in
          let uu____6395 =
            let uu____6396 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____6397 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6396 uu____6397  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6393 uu____6395  in
        FStar_Pprint.group uu____6392

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
                 let uu____6429 =
                   let uu____6430 =
                     let uu____6431 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6431 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6430 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6429 term_doc
             | pats ->
                 let uu____6439 =
                   let uu____6440 =
                     let uu____6441 =
                       let uu____6442 =
                         let uu____6443 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6443
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6442 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6446 = p_trigger trigger  in
                     prefix2 uu____6441 uu____6446  in
                   FStar_Pprint.group uu____6440  in
                 prefix2 uu____6439 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6467 =
                   let uu____6468 =
                     let uu____6469 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6469 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6468 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6467 term_doc
             | pats ->
                 let uu____6477 =
                   let uu____6478 =
                     let uu____6479 =
                       let uu____6480 =
                         let uu____6481 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6481
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6480 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6484 = p_trigger trigger  in
                     prefix2 uu____6479 uu____6484  in
                   FStar_Pprint.group uu____6478  in
                 prefix2 uu____6477 term_doc)
        | uu____6485 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6487 -> str "forall"
    | FStar_Parser_AST.QExists uu____6501 -> str "exists"
    | uu____6515 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___138_6517  ->
    match uu___138_6517 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6529 =
          let uu____6530 =
            let uu____6531 =
              let uu____6532 = str "pattern"  in
              let uu____6534 =
                let uu____6535 =
                  let uu____6536 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____6536
                   in
                FStar_Pprint.op_Hat_Hat uu____6535 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6532 uu____6534  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6531  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6530  in
        FStar_Pprint.group uu____6529

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6544 = str "\\/"  in
    FStar_Pprint.separate_map uu____6544 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6551 =
      let uu____6552 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____6552 p_appTerm pats  in
    FStar_Pprint.group uu____6551

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____6564 =
              let uu____6565 =
                let uu____6566 = str "fun"  in
                let uu____6568 =
                  let uu____6569 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6569
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____6566 uu____6568  in
              let uu____6570 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____6565 uu____6570  in
            let uu____6572 = paren_if ps  in uu____6572 uu____6564
        | uu____6577 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____6585  ->
      match uu____6585 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____6609 =
                    let uu____6610 =
                      let uu____6611 =
                        let uu____6612 = p_tuplePattern p  in
                        let uu____6613 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____6612 uu____6613  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6611
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6610  in
                  FStar_Pprint.group uu____6609
              | FStar_Pervasives_Native.Some f ->
                  let uu____6615 =
                    let uu____6616 =
                      let uu____6617 =
                        let uu____6618 =
                          let uu____6619 =
                            let uu____6620 = p_tuplePattern p  in
                            let uu____6621 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6620
                              uu____6621
                             in
                          FStar_Pprint.group uu____6619  in
                        let uu____6623 =
                          let uu____6624 =
                            let uu____6627 = p_tmFormula f  in
                            [uu____6627; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____6624  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6618 uu____6623
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6617
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6616  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____6615
               in
            let uu____6629 =
              let uu____6630 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____6630  in
            FStar_Pprint.group uu____6629  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____6640 =
                      let uu____6641 =
                        let uu____6642 =
                          let uu____6643 =
                            let uu____6644 =
                              let uu____6645 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____6645  in
                            FStar_Pprint.separate_map uu____6644
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6643
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6642
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6641  in
                    FStar_Pprint.group uu____6640
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6647 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____6649;_},e1::e2::[])
        ->
        let uu____6655 = str "<==>"  in
        let uu____6657 = p_tmImplies e1  in
        let uu____6658 = p_tmIff e2  in
        infix0 uu____6655 uu____6657 uu____6658
    | uu____6659 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____6661;_},e1::e2::[])
        ->
        let uu____6667 = str "==>"  in
        let uu____6669 = p_tmArrow p_tmFormula e1  in
        let uu____6670 = p_tmImplies e2  in
        infix0 uu____6667 uu____6669 uu____6670
    | uu____6671 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____6679 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____6679 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_5 when _0_5 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____6704 ->
               let uu____6705 =
                 let uu____6706 =
                   let uu____6707 =
                     let uu____6708 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6708
                      in
                   FStar_Pprint.separate uu____6707 terms  in
                 let uu____6709 =
                   let uu____6710 =
                     let uu____6711 =
                       let uu____6712 =
                         let uu____6713 =
                           let uu____6714 =
                             let uu____6715 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____6715
                              in
                           FStar_Pprint.separate uu____6714 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____6713 last_op  in
                       let uu____6716 =
                         let uu____6717 =
                           let uu____6718 =
                             let uu____6719 =
                               let uu____6720 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6720
                                in
                             FStar_Pprint.separate uu____6719 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____6718 last_op  in
                         jump2 uu____6717  in
                       FStar_Pprint.ifflat uu____6712 uu____6716  in
                     FStar_Pprint.group uu____6711  in
                   let uu____6721 = FStar_List.hd last1  in
                   prefix2 uu____6710 uu____6721  in
                 FStar_Pprint.ifflat uu____6706 uu____6709  in
               FStar_Pprint.group uu____6705)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____6734 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____6740 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____6734 uu____6740
      | uu____6743 -> let uu____6744 = p_Tm e  in [uu____6744]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____6747 =
        let uu____6748 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____6748 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6747  in
    let disj =
      let uu____6751 =
        let uu____6752 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____6752 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6751  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6772;_},e1::e2::[])
        ->
        let uu____6778 = p_tmDisjunction e1  in
        let uu____6783 = let uu____6788 = p_tmConjunction e2  in [uu____6788]
           in
        FStar_List.append uu____6778 uu____6783
    | uu____6797 -> let uu____6798 = p_tmConjunction e  in [uu____6798]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6808;_},e1::e2::[])
        ->
        let uu____6814 = p_tmConjunction e1  in
        let uu____6817 = let uu____6820 = p_tmTuple e2  in [uu____6820]  in
        FStar_List.append uu____6814 uu____6817
    | uu____6821 -> let uu____6822 = p_tmTuple e  in [uu____6822]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____6839 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____6839
          (fun uu____6847  ->
             match uu____6847 with | (e1,uu____6853) -> p_tmEq e1) args
    | uu____6854 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____6863 =
             let uu____6864 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6864  in
           FStar_Pprint.group uu____6863)

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
               (let uu____6883 = FStar_Ident.text_of_id op  in
                uu____6883 = "="))
              ||
              (let uu____6888 = FStar_Ident.text_of_id op  in
               uu____6888 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6894 = levels op1  in
            (match uu____6894 with
             | (left1,mine,right1) ->
                 let uu____6913 =
                   let uu____6914 = FStar_All.pipe_left str op1  in
                   let uu____6916 = p_tmEqWith' p_X left1 e1  in
                   let uu____6917 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6914 uu____6916 uu____6917  in
                 paren_if_gt curr mine uu____6913)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6918;_},e1::e2::[])
            ->
            let uu____6924 =
              let uu____6925 = p_tmEqWith p_X e1  in
              let uu____6926 =
                let uu____6927 =
                  let uu____6928 =
                    let uu____6929 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6929  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6928  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6927  in
              FStar_Pprint.op_Hat_Hat uu____6925 uu____6926  in
            FStar_Pprint.group uu____6924
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6930;_},e1::[])
            ->
            let uu____6935 = levels "-"  in
            (match uu____6935 with
             | (left1,mine,right1) ->
                 let uu____6955 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6955)
        | uu____6956 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____7004)::(e2,uu____7006)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____7026 = is_list e  in Prims.op_Negation uu____7026)
              ->
              let op = "::"  in
              let uu____7031 = levels op  in
              (match uu____7031 with
               | (left1,mine,right1) ->
                   let uu____7050 =
                     let uu____7051 = str op  in
                     let uu____7052 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7054 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7051 uu____7052 uu____7054  in
                   paren_if_gt curr mine uu____7050)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____7073 = levels op  in
              (match uu____7073 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____7107 = p_binder false b  in
                         let uu____7109 =
                           let uu____7110 =
                             let uu____7111 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7111 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7110
                            in
                         FStar_Pprint.op_Hat_Hat uu____7107 uu____7109
                     | FStar_Util.Inr t ->
                         let uu____7113 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____7115 =
                           let uu____7116 =
                             let uu____7117 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____7117 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____7116
                            in
                         FStar_Pprint.op_Hat_Hat uu____7113 uu____7115
                      in
                   let uu____7118 =
                     let uu____7119 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____7124 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____7119 uu____7124  in
                   paren_if_gt curr mine uu____7118)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____7126;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____7156 = levels op  in
              (match uu____7156 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____7176 = str op  in
                     let uu____7177 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____7179 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____7176 uu____7177 uu____7179
                   else
                     (let uu____7183 =
                        let uu____7184 = str op  in
                        let uu____7185 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____7187 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____7184 uu____7185 uu____7187  in
                      paren_if_gt curr mine uu____7183))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____7196 = levels op1  in
              (match uu____7196 with
               | (left1,mine,right1) ->
                   let uu____7215 =
                     let uu____7216 = str op1  in
                     let uu____7217 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____7219 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____7216 uu____7217 uu____7219  in
                   paren_if_gt curr mine uu____7215)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____7239 =
                let uu____7240 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____7241 =
                  let uu____7242 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____7242 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____7240 uu____7241  in
              braces_with_nesting uu____7239
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____7247;_},e1::[])
              ->
              let uu____7252 =
                let uu____7253 = str "~"  in
                let uu____7255 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____7253 uu____7255  in
              FStar_Pprint.group uu____7252
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____7257;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____7266 = levels op  in
                   (match uu____7266 with
                    | (left1,mine,right1) ->
                        let uu____7285 =
                          let uu____7286 = str op  in
                          let uu____7287 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____7289 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____7286 uu____7287 uu____7289  in
                        paren_if_gt curr mine uu____7285)
               | uu____7291 -> p_X e)
          | uu____7292 -> p_X e

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
        let uu____7299 =
          let uu____7300 = p_lident lid  in
          let uu____7301 =
            let uu____7302 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7302  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7300 uu____7301  in
        FStar_Pprint.group uu____7299
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____7305 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____7307 = p_appTerm e  in
    let uu____7308 =
      let uu____7309 =
        let uu____7310 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____7310 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7309  in
    FStar_Pprint.op_Hat_Hat uu____7307 uu____7308

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____7316 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____7316 t phi
      | FStar_Parser_AST.TAnnotated uu____7317 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____7323 ->
          let uu____7324 =
            let uu____7326 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7326
             in
          failwith uu____7324
      | FStar_Parser_AST.TVariable uu____7329 ->
          let uu____7330 =
            let uu____7332 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7332
             in
          failwith uu____7330
      | FStar_Parser_AST.NoName uu____7335 ->
          let uu____7336 =
            let uu____7338 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7338
             in
          failwith uu____7336

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____7342  ->
      match uu____7342 with
      | (lid,e) ->
          let uu____7350 =
            let uu____7351 = p_qlident lid  in
            let uu____7352 =
              let uu____7353 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____7353
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____7351 uu____7352  in
          FStar_Pprint.group uu____7350

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____7356 when is_general_application e ->
        let uu____7363 = head_and_args e  in
        (match uu____7363 with
         | (head1,args) ->
             let uu____7388 =
               let uu____7399 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____7399
               then
                 let uu____7433 =
                   FStar_Util.take
                     (fun uu____7457  ->
                        match uu____7457 with
                        | (uu____7463,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____7433 with
                 | (fs_typ_args,args1) ->
                     let uu____7501 =
                       let uu____7502 = p_indexingTerm head1  in
                       let uu____7503 =
                         let uu____7504 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____7504 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____7502 uu____7503  in
                     (uu____7501, args1)
               else
                 (let uu____7519 = p_indexingTerm head1  in
                  (uu____7519, args))
                in
             (match uu____7388 with
              | (head_doc,args1) ->
                  let uu____7540 =
                    let uu____7541 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____7541 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____7540))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____7563 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____7563)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____7582 =
               let uu____7583 = p_quident lid  in
               let uu____7584 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____7583 uu____7584  in
             FStar_Pprint.group uu____7582
         | hd1::tl1 ->
             let uu____7601 =
               let uu____7602 =
                 let uu____7603 =
                   let uu____7604 = p_quident lid  in
                   let uu____7605 = p_argTerm hd1  in
                   prefix2 uu____7604 uu____7605  in
                 FStar_Pprint.group uu____7603  in
               let uu____7606 =
                 let uu____7607 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____7607  in
               FStar_Pprint.op_Hat_Hat uu____7602 uu____7606  in
             FStar_Pprint.group uu____7601)
    | uu____7612 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____7623 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____7623 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____7627 = str "#"  in
        let uu____7629 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____7627 uu____7629
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____7632 = str "#["  in
        let uu____7634 =
          let uu____7635 = p_indexingTerm t  in
          let uu____7636 =
            let uu____7637 = str "]"  in
            let uu____7639 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____7637 uu____7639  in
          FStar_Pprint.op_Hat_Hat uu____7635 uu____7636  in
        FStar_Pprint.op_Hat_Hat uu____7632 uu____7634
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____7641  ->
    match uu____7641 with | (e,uu____7647) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____7652;_},e1::e2::[])
          ->
          let uu____7658 =
            let uu____7659 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7660 =
              let uu____7661 =
                let uu____7662 = p_term false false e2  in
                soft_parens_with_nesting uu____7662  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7661  in
            FStar_Pprint.op_Hat_Hat uu____7659 uu____7660  in
          FStar_Pprint.group uu____7658
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____7665;_},e1::e2::[])
          ->
          let uu____7671 =
            let uu____7672 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7673 =
              let uu____7674 =
                let uu____7675 = p_term false false e2  in
                soft_brackets_with_nesting uu____7675  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7674  in
            FStar_Pprint.op_Hat_Hat uu____7672 uu____7673  in
          FStar_Pprint.group uu____7671
      | uu____7678 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____7683 = p_quident lid  in
        let uu____7684 =
          let uu____7685 =
            let uu____7686 = p_term false false e1  in
            soft_parens_with_nesting uu____7686  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7685  in
        FStar_Pprint.op_Hat_Hat uu____7683 uu____7684
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7694 =
          let uu____7695 = FStar_Ident.text_of_id op  in str uu____7695  in
        let uu____7697 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____7694 uu____7697
    | uu____7698 -> p_atomicTermNotQUident e

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
         | uu____7709 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7718 =
          let uu____7719 = FStar_Ident.text_of_id op  in str uu____7719  in
        let uu____7721 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____7718 uu____7721
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____7725 =
          let uu____7726 =
            let uu____7727 =
              let uu____7728 = FStar_Ident.text_of_id op  in str uu____7728
               in
            let uu____7730 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____7727 uu____7730  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7726  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7725
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____7745 = all_explicit args  in
        if uu____7745
        then
          let uu____7748 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____7749 =
            let uu____7750 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____7751 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____7750 p_tmEq uu____7751  in
          let uu____7758 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____7748 uu____7749 uu____7758
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____7780 =
                 let uu____7781 = p_quident lid  in
                 let uu____7782 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7781 uu____7782  in
               FStar_Pprint.group uu____7780
           | hd1::tl1 ->
               let uu____7799 =
                 let uu____7800 =
                   let uu____7801 =
                     let uu____7802 = p_quident lid  in
                     let uu____7803 = p_argTerm hd1  in
                     prefix2 uu____7802 uu____7803  in
                   FStar_Pprint.group uu____7801  in
                 let uu____7804 =
                   let uu____7805 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____7805  in
                 FStar_Pprint.op_Hat_Hat uu____7800 uu____7804  in
               FStar_Pprint.group uu____7799)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____7812 =
          let uu____7813 = p_atomicTermNotQUident e1  in
          let uu____7814 =
            let uu____7815 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7815  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____7813 uu____7814
           in
        FStar_Pprint.group uu____7812
    | uu____7818 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____7823 = p_quident constr_lid  in
        let uu____7824 =
          let uu____7825 =
            let uu____7826 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7826  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7825  in
        FStar_Pprint.op_Hat_Hat uu____7823 uu____7824
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____7828 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____7828 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____7830 = p_term false false e1  in
        soft_parens_with_nesting uu____7830
    | uu____7833 when is_array e ->
        let es = extract_from_list e  in
        let uu____7837 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____7838 =
          let uu____7839 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____7839
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____7844 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7837 uu____7838 uu____7844
    | uu____7847 when is_list e ->
        let uu____7848 =
          let uu____7849 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7850 = extract_from_list e  in
          separate_map_or_flow_last uu____7849
            (fun ps  -> p_noSeqTerm ps false) uu____7850
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____7848 FStar_Pprint.rbracket
    | uu____7859 when is_lex_list e ->
        let uu____7860 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____7861 =
          let uu____7862 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7863 = extract_from_list e  in
          separate_map_or_flow_last uu____7862
            (fun ps  -> p_noSeqTerm ps false) uu____7863
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7860 uu____7861 FStar_Pprint.rbracket
    | uu____7872 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____7876 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____7877 =
          let uu____7878 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____7878 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7876 uu____7877 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____7888 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____7891 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____7888 uu____7891
    | FStar_Parser_AST.Op (op,args) when
        let uu____7900 = handleable_op op args  in
        Prims.op_Negation uu____7900 ->
        let uu____7902 =
          let uu____7904 =
            let uu____7906 = FStar_Ident.text_of_id op  in
            let uu____7908 =
              let uu____7910 =
                let uu____7912 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____7912
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____7910  in
            Prims.strcat uu____7906 uu____7908  in
          Prims.strcat "Operation " uu____7904  in
        failwith uu____7902
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7918 = str "u#"  in
        let uu____7920 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____7918 uu____7920
    | FStar_Parser_AST.Wild  ->
        let uu____7921 = p_term false false e  in
        soft_parens_with_nesting uu____7921
    | FStar_Parser_AST.Const uu____7924 ->
        let uu____7925 = p_term false false e  in
        soft_parens_with_nesting uu____7925
    | FStar_Parser_AST.Op uu____7928 ->
        let uu____7935 = p_term false false e  in
        soft_parens_with_nesting uu____7935
    | FStar_Parser_AST.Tvar uu____7938 ->
        let uu____7939 = p_term false false e  in
        soft_parens_with_nesting uu____7939
    | FStar_Parser_AST.Var uu____7942 ->
        let uu____7943 = p_term false false e  in
        soft_parens_with_nesting uu____7943
    | FStar_Parser_AST.Name uu____7946 ->
        let uu____7947 = p_term false false e  in
        soft_parens_with_nesting uu____7947
    | FStar_Parser_AST.Construct uu____7950 ->
        let uu____7961 = p_term false false e  in
        soft_parens_with_nesting uu____7961
    | FStar_Parser_AST.Abs uu____7964 ->
        let uu____7971 = p_term false false e  in
        soft_parens_with_nesting uu____7971
    | FStar_Parser_AST.App uu____7974 ->
        let uu____7981 = p_term false false e  in
        soft_parens_with_nesting uu____7981
    | FStar_Parser_AST.Let uu____7984 ->
        let uu____8005 = p_term false false e  in
        soft_parens_with_nesting uu____8005
    | FStar_Parser_AST.LetOpen uu____8008 ->
        let uu____8013 = p_term false false e  in
        soft_parens_with_nesting uu____8013
    | FStar_Parser_AST.Seq uu____8016 ->
        let uu____8021 = p_term false false e  in
        soft_parens_with_nesting uu____8021
    | FStar_Parser_AST.Bind uu____8024 ->
        let uu____8031 = p_term false false e  in
        soft_parens_with_nesting uu____8031
    | FStar_Parser_AST.If uu____8034 ->
        let uu____8041 = p_term false false e  in
        soft_parens_with_nesting uu____8041
    | FStar_Parser_AST.Match uu____8044 ->
        let uu____8059 = p_term false false e  in
        soft_parens_with_nesting uu____8059
    | FStar_Parser_AST.TryWith uu____8062 ->
        let uu____8077 = p_term false false e  in
        soft_parens_with_nesting uu____8077
    | FStar_Parser_AST.Ascribed uu____8080 ->
        let uu____8089 = p_term false false e  in
        soft_parens_with_nesting uu____8089
    | FStar_Parser_AST.Record uu____8092 ->
        let uu____8105 = p_term false false e  in
        soft_parens_with_nesting uu____8105
    | FStar_Parser_AST.Project uu____8108 ->
        let uu____8113 = p_term false false e  in
        soft_parens_with_nesting uu____8113
    | FStar_Parser_AST.Product uu____8116 ->
        let uu____8123 = p_term false false e  in
        soft_parens_with_nesting uu____8123
    | FStar_Parser_AST.Sum uu____8126 ->
        let uu____8137 = p_term false false e  in
        soft_parens_with_nesting uu____8137
    | FStar_Parser_AST.QForall uu____8140 ->
        let uu____8153 = p_term false false e  in
        soft_parens_with_nesting uu____8153
    | FStar_Parser_AST.QExists uu____8156 ->
        let uu____8169 = p_term false false e  in
        soft_parens_with_nesting uu____8169
    | FStar_Parser_AST.Refine uu____8172 ->
        let uu____8177 = p_term false false e  in
        soft_parens_with_nesting uu____8177
    | FStar_Parser_AST.NamedTyp uu____8180 ->
        let uu____8185 = p_term false false e  in
        soft_parens_with_nesting uu____8185
    | FStar_Parser_AST.Requires uu____8188 ->
        let uu____8196 = p_term false false e  in
        soft_parens_with_nesting uu____8196
    | FStar_Parser_AST.Ensures uu____8199 ->
        let uu____8207 = p_term false false e  in
        soft_parens_with_nesting uu____8207
    | FStar_Parser_AST.Attributes uu____8210 ->
        let uu____8213 = p_term false false e  in
        soft_parens_with_nesting uu____8213
    | FStar_Parser_AST.Quote uu____8216 ->
        let uu____8221 = p_term false false e  in
        soft_parens_with_nesting uu____8221
    | FStar_Parser_AST.VQuote uu____8224 ->
        let uu____8225 = p_term false false e  in
        soft_parens_with_nesting uu____8225
    | FStar_Parser_AST.Antiquote uu____8228 ->
        let uu____8229 = p_term false false e  in
        soft_parens_with_nesting uu____8229

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___141_8232  ->
    match uu___141_8232 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____8241) ->
        let uu____8244 = str s  in FStar_Pprint.dquotes uu____8244
    | FStar_Const.Const_bytearray (bytes,uu____8246) ->
        let uu____8251 =
          let uu____8252 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____8252  in
        let uu____8253 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____8251 uu____8253
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___139_8276 =
          match uu___139_8276 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___140_8283 =
          match uu___140_8283 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____8298  ->
               match uu____8298 with
               | (s,w) ->
                   let uu____8305 = signedness s  in
                   let uu____8306 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____8305 uu____8306)
            sign_width_opt
           in
        let uu____8307 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____8307 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____8311 = FStar_Range.string_of_range r  in str uu____8311
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____8315 = p_quident lid  in
        let uu____8316 =
          let uu____8317 =
            let uu____8318 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____8318  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____8317  in
        FStar_Pprint.op_Hat_Hat uu____8315 uu____8316

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____8321 = str "u#"  in
    let uu____8323 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____8321 uu____8323

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____8325;_},u1::u2::[])
        ->
        let uu____8331 =
          let uu____8332 = p_universeFrom u1  in
          let uu____8333 =
            let uu____8334 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____8334  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8332 uu____8333  in
        FStar_Pprint.group uu____8331
    | FStar_Parser_AST.App uu____8335 ->
        let uu____8342 = head_and_args u  in
        (match uu____8342 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____8368 =
                    let uu____8369 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____8370 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____8378  ->
                           match uu____8378 with
                           | (u1,uu____8384) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____8369 uu____8370  in
                  FStar_Pprint.group uu____8368
              | uu____8385 ->
                  let uu____8386 =
                    let uu____8388 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____8388
                     in
                  failwith uu____8386))
    | uu____8391 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____8417 = FStar_Ident.text_of_id id1  in str uu____8417
    | FStar_Parser_AST.Paren u1 ->
        let uu____8420 = p_universeFrom u1  in
        soft_parens_with_nesting uu____8420
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____8421;_},uu____8422::uu____8423::[])
        ->
        let uu____8427 = p_universeFrom u  in
        soft_parens_with_nesting uu____8427
    | FStar_Parser_AST.App uu____8428 ->
        let uu____8435 = p_universeFrom u  in
        soft_parens_with_nesting uu____8435
    | uu____8436 ->
        let uu____8437 =
          let uu____8439 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____8439
           in
        failwith uu____8437

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
       | FStar_Parser_AST.Module (uu____8528,decls) ->
           let uu____8534 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____8534
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____8543,decls,uu____8545) ->
           let uu____8552 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____8552
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____8612  ->
         match uu____8612 with | (comment,range) -> str comment) comments
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____8663,decls) -> decls
        | FStar_Parser_AST.Interface (uu____8669,decls,uu____8671) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____8723 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____8736;
                 FStar_Parser_AST.doc = uu____8737;
                 FStar_Parser_AST.quals = uu____8738;
                 FStar_Parser_AST.attrs = uu____8739;_}::uu____8740 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____8746 =
                   let uu____8749 =
                     let uu____8752 = FStar_List.tl ds  in d :: uu____8752
                      in
                   d0 :: uu____8749  in
                 (uu____8746, (d0.FStar_Parser_AST.drange))
             | uu____8757 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____8723 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____8820 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____8820 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____8927 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____8927, comments1))))))
  