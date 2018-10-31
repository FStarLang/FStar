open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let map_rev : 'a 'b . ('a -> 'b) -> 'a Prims.list -> 'b Prims.list =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____99 = let uu____102 = f x  in uu____102 :: acc  in
            aux xs uu____99
         in
      aux l []
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.bool)
  =
  fun args  ->
    FStar_Util.for_all
      (fun uu___110_146  ->
         match uu___110_146 with
         | (uu____152,FStar_Parser_AST.Nothing ) -> true
         | uu____154 -> false) args
  
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____188 'Auu____189 .
    Prims.bool -> ('Auu____188 -> 'Auu____189) -> 'Auu____188 -> 'Auu____189
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
  'Auu____299 'Auu____300 .
    'Auu____299 ->
      ('Auu____300 -> 'Auu____299) ->
        'Auu____300 FStar_Pervasives_Native.option -> 'Auu____299
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
  'Auu____413 .
    FStar_Pprint.document ->
      ('Auu____413 -> FStar_Pprint.document) ->
        'Auu____413 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____438 =
          let uu____439 =
            let uu____440 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____440  in
          FStar_Pprint.separate_map uu____439 f l  in
        FStar_Pprint.group uu____438
  
let precede_break_separate_map :
  'Auu____452 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____452 -> FStar_Pprint.document) ->
          'Auu____452 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____482 =
            let uu____483 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____484 =
              let uu____485 = FStar_List.hd l  in
              FStar_All.pipe_right uu____485 f  in
            FStar_Pprint.precede uu____483 uu____484  in
          let uu____486 =
            let uu____487 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____493 =
                   let uu____494 =
                     let uu____495 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____495  in
                   FStar_Pprint.op_Hat_Hat sep uu____494  in
                 FStar_Pprint.op_Hat_Hat break1 uu____493) uu____487
             in
          FStar_Pprint.op_Hat_Hat uu____482 uu____486
  
let concat_break_map :
  'Auu____503 .
    ('Auu____503 -> FStar_Pprint.document) ->
      'Auu____503 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____523 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____527 = f x  in FStar_Pprint.op_Hat_Hat uu____527 break1)
          l
         in
      FStar_Pprint.group uu____523
  
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
    let uu____590 = str "begin"  in
    let uu____592 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____590 contents uu____592
  
let separate_map_last :
  'Auu____605 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____605 -> FStar_Pprint.document) ->
        'Auu____605 Prims.list -> FStar_Pprint.document
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
  'Auu____663 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____663 -> FStar_Pprint.document) ->
        'Auu____663 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____695 =
          let uu____696 =
            let uu____697 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____697  in
          separate_map_last uu____696 f l  in
        FStar_Pprint.group uu____695
  
let separate_map_or_flow :
  'Auu____707 .
    FStar_Pprint.document ->
      ('Auu____707 -> FStar_Pprint.document) ->
        'Auu____707 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____745 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____745 -> FStar_Pprint.document) ->
        'Auu____745 Prims.list -> FStar_Pprint.document
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
  'Auu____803 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____803 -> FStar_Pprint.document) ->
        'Auu____803 Prims.list -> FStar_Pprint.document
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
              let uu____885 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____885
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____907 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____907 -> FStar_Pprint.document) ->
                  'Auu____907 Prims.list -> FStar_Pprint.document
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
                    (let uu____966 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____966
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____986 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____986 -> FStar_Pprint.document) ->
                  'Auu____986 Prims.list -> FStar_Pprint.document
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
                    (let uu____1045 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1045
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____1064  ->
    match uu____1064 with
    | (comment,keywords) ->
        let uu____1098 =
          let uu____1099 =
            let uu____1102 = str comment  in
            let uu____1103 =
              let uu____1106 =
                let uu____1109 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1120  ->
                       match uu____1120 with
                       | (k,v1) ->
                           let uu____1133 =
                             let uu____1136 = str k  in
                             let uu____1137 =
                               let uu____1140 =
                                 let uu____1143 = str v1  in [uu____1143]  in
                               FStar_Pprint.rarrow :: uu____1140  in
                             uu____1136 :: uu____1137  in
                           FStar_Pprint.concat uu____1133) keywords
                   in
                [uu____1109]  in
              FStar_Pprint.space :: uu____1106  in
            uu____1102 :: uu____1103  in
          FStar_Pprint.concat uu____1099  in
        FStar_Pprint.group uu____1098
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1153 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1169 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1169
      | uu____1172 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1223::(e2,uu____1225)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1248 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1272,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1283,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1304 = extract_from_list e2  in e1 :: uu____1304
    | uu____1307 ->
        let uu____1308 =
          let uu____1310 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1310  in
        failwith uu____1308
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1324;
           FStar_Parser_AST.level = uu____1325;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1327 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1339;
           FStar_Parser_AST.level = uu____1340;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1342;
                                                         FStar_Parser_AST.level
                                                           = uu____1343;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1345;
                                                    FStar_Parser_AST.level =
                                                      uu____1346;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1348;
                FStar_Parser_AST.level = uu____1349;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1351;
           FStar_Parser_AST.level = uu____1352;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1354 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1366 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1367;
           FStar_Parser_AST.range = uu____1368;
           FStar_Parser_AST.level = uu____1369;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1370;
                                                         FStar_Parser_AST.range
                                                           = uu____1371;
                                                         FStar_Parser_AST.level
                                                           = uu____1372;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1374;
                                                    FStar_Parser_AST.level =
                                                      uu____1375;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1376;
                FStar_Parser_AST.range = uu____1377;
                FStar_Parser_AST.level = uu____1378;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1380;
           FStar_Parser_AST.level = uu____1381;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1383 = extract_from_ref_set e1  in
        let uu____1386 = extract_from_ref_set e2  in
        FStar_List.append uu____1383 uu____1386
    | uu____1389 ->
        let uu____1390 =
          let uu____1392 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1392  in
        failwith uu____1390
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1404 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1404
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1413 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1413
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1424 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1424 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1434 = FStar_Ident.text_of_id op  in uu____1434 <> "~"))
  
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
      | uu____1504 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1524 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1535 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1546 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___111_1572  ->
    match uu___111_1572 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___112_1607  ->
      match uu___112_1607 with
      | FStar_Util.Inl c ->
          let uu____1620 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1620 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1636 .
    Prims.string ->
      ('Auu____1636,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1660  ->
      match uu____1660 with
      | (assoc_levels,tokens) ->
          let uu____1692 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1692 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___113_1864 =
    match uu___113_1864 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1914  ->
         match uu____1914 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1989 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1989 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2041) ->
          assoc_levels
      | uu____2079 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____2112 .
    ('Auu____2112,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2161 =
        FStar_List.tryFind
          (fun uu____2197  ->
             match uu____2197 with
             | (uu____2214,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2161 with
      | FStar_Pervasives_Native.Some ((uu____2243,l1,uu____2245),uu____2246)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2296 =
            let uu____2298 =
              let uu____2300 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2300  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2298
             in
          failwith uu____2296
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2335 = assign_levels level_associativity_spec op  in
    match uu____2335 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2394 =
      let uu____2397 =
        let uu____2403 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2403  in
      FStar_List.tryFind uu____2397 operatorInfix0ad12  in
    uu____2394 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2470 =
      let uu____2485 =
        let uu____2503 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2503  in
      FStar_List.tryFind uu____2485 opinfix34  in
    uu____2470 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2569 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2569
    then (Prims.parse_int "1")
    else
      (let uu____2582 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2582
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2628 . FStar_Ident.ident -> 'Auu____2628 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2646 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2646 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2655 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2655
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2677 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2677 [".()<-"; ".[]<-"]
      | uu____2685 -> false
  
type annotation_style =
  | Binders of (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 
  | Arrows of (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2725 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2769 -> false
  
let (__proj__Arrows__item___0 :
  annotation_style -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2812 -> true
      | uu____2818 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2851 = FStar_List.for_all is_binder_annot bs  in
          if uu____2851
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____2866 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____2871 = all_binders e (Prims.parse_int "0")  in
    match uu____2871 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____2910 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____2910
  
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
  'Auu____3074 'Auu____3075 .
    ('Auu____3074 -> FStar_Pprint.document) ->
      'Auu____3074 ->
        FStar_Range.range -> 'Auu____3075 -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____3122 = FStar_ST.op_Bang comment_stack  in
            match uu____3122 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment =
                  if FStar_Util.starts_with c "//"
                  then
                    let uu____3195 = str c  in
                    FStar_Pprint.op_Hat_Hat uu____3195 FStar_Pprint.hardline
                  else
                    (let uu____3198 = str c  in
                     FStar_Pprint.op_Hat_Hat uu____3198 FStar_Pprint.hardline)
                   in
                let uu____3199 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____3199
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____3241 = FStar_Pprint.op_Hat_Hat acc comment  in
                    comments_before_pos uu____3241 print_pos lookahead_pos))
                else
                  (let uu____3244 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____3244))
             in
          let uu____3247 =
            let uu____3253 =
              let uu____3254 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____3254  in
            let uu____3255 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____3253 uu____3255  in
          match uu____3247 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____3264 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____3264
                else comments  in
              if comments1 = FStar_Pprint.empty
              then printed_e
              else
                (let uu____3276 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                    in
                 FStar_Pprint.group uu____3276)
  
let with_comment_sep :
  'Auu____3292 'Auu____3293 'Auu____3294 .
    ('Auu____3292 -> 'Auu____3293) ->
      'Auu____3292 ->
        FStar_Range.range ->
          'Auu____3294 ->
            (FStar_Pprint.document,'Auu____3293)
              FStar_Pervasives_Native.tuple2
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____3345 = FStar_ST.op_Bang comment_stack  in
            match uu____3345 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment = str c  in
                let uu____3416 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____3416
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____3458 =
                      if acc = FStar_Pprint.empty
                      then comment
                      else
                        (let uu____3462 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             comment
                            in
                         FStar_Pprint.op_Hat_Hat acc uu____3462)
                       in
                    comments_before_pos uu____3458 print_pos lookahead_pos))
                else
                  (let uu____3465 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____3465))
             in
          let uu____3468 =
            let uu____3474 =
              let uu____3475 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____3475  in
            let uu____3476 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____3474 uu____3476  in
          match uu____3468 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____3489 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____3489
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
                let uu____3542 = FStar_ST.op_Bang comment_stack  in
                match uu____3542 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3636 =
                          let uu____3638 =
                            let uu____3640 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3640  in
                          uu____3638 - lbegin  in
                        max k uu____3636  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3645 =
                          let uu____3646 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3647 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3646 uu____3647  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3645  in
                      let uu____3648 =
                        let uu____3650 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3650  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3648 pos meta_decl doc2 true init1))
                | uu____3653 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3666 = FStar_Range.line_of_pos pos  in
                         uu____3666 - lbegin  in
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
                       let uu____3708 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3708)
  
let separate_map_with_comments :
  'Auu____3722 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3722 -> FStar_Pprint.document) ->
          'Auu____3722 Prims.list ->
            ('Auu____3722 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3781 x =
              match uu____3781 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3800 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3800 meta_decl doc1 false false
                     in
                  let uu____3804 =
                    let uu____3806 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3806  in
                  let uu____3807 =
                    let uu____3808 =
                      let uu____3809 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3809  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3808  in
                  (uu____3804, uu____3807)
               in
            let uu____3811 =
              let uu____3818 = FStar_List.hd xs  in
              let uu____3819 = FStar_List.tl xs  in (uu____3818, uu____3819)
               in
            match uu____3811 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3837 =
                    let uu____3839 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3839  in
                  let uu____3840 =
                    let uu____3841 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3841  in
                  (uu____3837, uu____3840)  in
                let uu____3843 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3843
  
let separate_map_with_comments_kw :
  'Auu____3870 'Auu____3871 .
    'Auu____3870 ->
      'Auu____3870 ->
        ('Auu____3870 -> 'Auu____3871 -> FStar_Pprint.document) ->
          'Auu____3871 Prims.list ->
            ('Auu____3871 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3935 x =
              match uu____3935 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3954 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3954 meta_decl doc1 false false
                     in
                  let uu____3958 =
                    let uu____3960 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3960  in
                  let uu____3961 =
                    let uu____3962 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3962  in
                  (uu____3958, uu____3961)
               in
            let uu____3964 =
              let uu____3971 = FStar_List.hd xs  in
              let uu____3972 = FStar_List.tl xs  in (uu____3971, uu____3972)
               in
            match uu____3964 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3990 =
                    let uu____3992 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3992  in
                  let uu____3993 = f prefix1 x  in (uu____3990, uu____3993)
                   in
                let uu____3995 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3995
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4909)) ->
          let uu____4912 =
            let uu____4914 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4914 FStar_Util.is_upper  in
          if uu____4912
          then
            let uu____4920 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4920 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4923 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4930 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____4933 =
      let uu____4934 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4935 =
        let uu____4936 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4936  in
      FStar_Pprint.op_Hat_Hat uu____4934 uu____4935  in
    FStar_Pprint.op_Hat_Hat uu____4930 uu____4933

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4938 ->
        let uu____4939 =
          let uu____4940 = str "@ "  in
          let uu____4942 =
            let uu____4943 =
              let uu____4944 =
                let uu____4945 =
                  let uu____4946 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4946  in
                FStar_Pprint.op_Hat_Hat uu____4945 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4944  in
            FStar_Pprint.op_Hat_Hat uu____4943 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4940 uu____4942  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4939

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4949  ->
    match uu____4949 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4997 =
                match uu____4997 with
                | (kwd,arg) ->
                    let uu____5010 = str "@"  in
                    let uu____5012 =
                      let uu____5013 = str kwd  in
                      let uu____5014 =
                        let uu____5015 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5015
                         in
                      FStar_Pprint.op_Hat_Hat uu____5013 uu____5014  in
                    FStar_Pprint.op_Hat_Hat uu____5010 uu____5012
                 in
              let uu____5016 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5016 FStar_Pprint.hardline
           in
        let uu____5023 =
          let uu____5024 =
            let uu____5025 =
              let uu____5026 = str doc1  in
              let uu____5027 =
                let uu____5028 =
                  let uu____5029 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5029  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5028  in
              FStar_Pprint.op_Hat_Hat uu____5026 uu____5027  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5025  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5024  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5023

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5033 =
          let uu____5034 = str "val"  in
          let uu____5036 =
            let uu____5037 =
              let uu____5038 = p_lident lid  in
              let uu____5039 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5038 uu____5039  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5037  in
          FStar_Pprint.op_Hat_Hat uu____5034 uu____5036  in
        let uu____5040 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5033 uu____5040
    | FStar_Parser_AST.TopLevelLet (uu____5043,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5068 =
               let uu____5069 = str "let"  in p_letlhs uu____5069 lb  in
             FStar_Pprint.group uu____5068) lbs
    | uu____5071 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_5086 =
          match uu___114_5086 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5094 = f x  in
              let uu____5095 =
                let uu____5096 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5096  in
              FStar_Pprint.op_Hat_Hat uu____5094 uu____5095
           in
        let uu____5097 = str "["  in
        let uu____5099 =
          let uu____5100 = p_list' l  in
          let uu____5101 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5100 uu____5101  in
        FStar_Pprint.op_Hat_Hat uu____5097 uu____5099

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5105 =
          let uu____5106 = str "open"  in
          let uu____5108 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5106 uu____5108  in
        FStar_Pprint.group uu____5105
    | FStar_Parser_AST.Include uid ->
        let uu____5110 =
          let uu____5111 = str "include"  in
          let uu____5113 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5111 uu____5113  in
        FStar_Pprint.group uu____5110
    | FStar_Parser_AST.Friend uid ->
        let uu____5115 =
          let uu____5116 = str "friend"  in
          let uu____5118 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5116 uu____5118  in
        FStar_Pprint.group uu____5115
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5121 =
          let uu____5122 = str "module"  in
          let uu____5124 =
            let uu____5125 =
              let uu____5126 = p_uident uid1  in
              let uu____5127 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5126 uu____5127  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5125  in
          FStar_Pprint.op_Hat_Hat uu____5122 uu____5124  in
        let uu____5128 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5121 uu____5128
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5130 =
          let uu____5131 = str "module"  in
          let uu____5133 =
            let uu____5134 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5134  in
          FStar_Pprint.op_Hat_Hat uu____5131 uu____5133  in
        FStar_Pprint.group uu____5130
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5135,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5172 = str "effect"  in
          let uu____5174 =
            let uu____5175 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5175  in
          FStar_Pprint.op_Hat_Hat uu____5172 uu____5174  in
        let uu____5176 =
          let uu____5177 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5177 FStar_Pprint.equals
           in
        let uu____5180 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5176 uu____5180
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5211 =
          let uu____5212 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5212  in
        let uu____5225 =
          let uu____5226 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5264 =
                    let uu____5265 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5265 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5264)) uu____5226
           in
        FStar_Pprint.op_Hat_Hat uu____5211 uu____5225
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5282 = str "let"  in
          let uu____5284 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5282 uu____5284  in
        let uu____5285 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5285 p_letbinding lbs
          (fun uu____5295  ->
             match uu____5295 with
             | (p,t) ->
                 let uu____5302 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5302;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5308 =
          let uu____5309 = str "val"  in
          let uu____5311 =
            let uu____5312 =
              let uu____5313 = p_lident lid  in
              let uu____5314 =
                let uu____5315 = all_binders_annot t  in
                if uu____5315
                then
                  let uu____5318 =
                    p_typ_top
                      (Binders ((Prims.parse_int "4"), (Prims.parse_int "0")))
                      false false t
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5318
                else
                  (let uu____5327 =
                     let uu____5328 =
                       let uu____5329 =
                         p_typ_top
                           (Arrows
                              ((Prims.parse_int "2"), (Prims.parse_int "2")))
                           false false t
                          in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5329
                        in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5328
                      in
                   FStar_Pprint.group uu____5327)
                 in
              FStar_Pprint.op_Hat_Hat uu____5313 uu____5314  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5312  in
          FStar_Pprint.op_Hat_Hat uu____5309 uu____5311  in
        FStar_All.pipe_left FStar_Pprint.group uu____5308
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5339 =
            let uu____5341 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5341 FStar_Util.is_upper  in
          if uu____5339
          then FStar_Pprint.empty
          else
            (let uu____5349 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5349 FStar_Pprint.space)
           in
        let uu____5351 =
          let uu____5352 = p_ident id1  in
          let uu____5353 =
            let uu____5354 =
              let uu____5355 =
                let uu____5356 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5356  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5355  in
            FStar_Pprint.group uu____5354  in
          FStar_Pprint.op_Hat_Hat uu____5352 uu____5353  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5351
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5365 = str "exception"  in
        let uu____5367 =
          let uu____5368 =
            let uu____5369 = p_uident uid  in
            let uu____5370 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5374 =
                     let uu____5375 = str "of"  in
                     let uu____5377 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5375 uu____5377  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5374) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5369 uu____5370  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5368  in
        FStar_Pprint.op_Hat_Hat uu____5365 uu____5367
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5381 = str "new_effect"  in
        let uu____5383 =
          let uu____5384 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5384  in
        FStar_Pprint.op_Hat_Hat uu____5381 uu____5383
    | FStar_Parser_AST.SubEffect se ->
        let uu____5386 = str "sub_effect"  in
        let uu____5388 =
          let uu____5389 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5389  in
        FStar_Pprint.op_Hat_Hat uu____5386 uu____5388
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5392 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5394,uu____5395) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5423 = str "%splice"  in
        let uu____5425 =
          let uu____5426 =
            let uu____5427 = str ";"  in p_list p_uident uu____5427 ids  in
          let uu____5429 =
            let uu____5430 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5430  in
          FStar_Pprint.op_Hat_Hat uu____5426 uu____5429  in
        FStar_Pprint.op_Hat_Hat uu____5423 uu____5425

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_5433  ->
    match uu___115_5433 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5436 = str "#set-options"  in
        let uu____5438 =
          let uu____5439 =
            let uu____5440 = str s  in FStar_Pprint.dquotes uu____5440  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5439  in
        FStar_Pprint.op_Hat_Hat uu____5436 uu____5438
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5445 = str "#reset-options"  in
        let uu____5447 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5453 =
                 let uu____5454 = str s  in FStar_Pprint.dquotes uu____5454
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5453) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5445 uu____5447
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5459 = str "#push-options"  in
        let uu____5461 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5467 =
                 let uu____5468 = str s  in FStar_Pprint.dquotes uu____5468
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5467) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5459 uu____5461
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
    fun uu____5499  ->
      match uu____5499 with
      | (typedecl,fsdoc_opt) ->
          let uu____5512 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5512 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5537 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5537
               else
                 (let uu____5540 =
                    let uu____5541 =
                      let uu____5542 =
                        let uu____5543 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5543 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5542  in
                    let uu____5544 =
                      let uu____5545 =
                        let uu____5546 =
                          let uu____5547 =
                            let uu____5548 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5548  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5547
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5546
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5545  in
                    FStar_Pprint.ifflat uu____5541 uu____5544  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5540))

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
    fun uu___116_5551  ->
      match uu___116_5551 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5580 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5580, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5597 = p_typ_sep false false t  in
          (match uu____5597 with
           | (comm,doc1) ->
               let uu____5617 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5617, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5673 =
            match uu____5673 with
            | (lid1,t,doc_opt) ->
                let uu____5690 =
                  let uu____5695 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5695 "!1"
                   in
                (match uu____5690 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5715 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5715  in
          let uu____5724 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5724, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5791 =
            match uu____5791 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5820 =
                    let uu____5821 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5821  in
                  FStar_Range.extend_to_end_of_line uu____5820  in
                let uu____5826 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range "!2"
                   in
                (match uu____5826 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5867 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5867, datacon_doc, jump2)

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
  fun uu____5872  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____5872 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____5907 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____5907  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____5909 =
                        let uu____5912 =
                          let uu____5915 = p_fsdoc fsdoc  in
                          let uu____5916 =
                            let uu____5919 = cont lid_doc  in [uu____5919]
                             in
                          uu____5915 :: uu____5916  in
                        kw :: uu____5912  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____5909
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____5926 =
                        let uu____5927 =
                          let uu____5928 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5928 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5927
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5926
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5948 =
                          let uu____5949 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5949  in
                        prefix2 uu____5948 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5951  ->
      match uu____5951 with
      | (lid,t,doc_opt) ->
          let uu____5968 =
            let uu____5969 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5970 =
              let uu____5971 = p_lident lid  in
              let uu____5972 =
                let uu____5973 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5973  in
              FStar_Pprint.op_Hat_Hat uu____5971 uu____5972  in
            FStar_Pprint.op_Hat_Hat uu____5969 uu____5970  in
          FStar_Pprint.group uu____5968

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____5975  ->
    match uu____5975 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6009 =
            let uu____6010 =
              let uu____6011 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6011  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6010  in
          FStar_Pprint.group uu____6009  in
        let uu____6012 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6013 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6017 =
                 let uu____6018 =
                   let uu____6019 =
                     let uu____6020 =
                       let uu____6021 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6021
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6020  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6019  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6018  in
               FStar_Pprint.group uu____6017) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6012 uu____6013

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6025  ->
      match uu____6025 with
      | (pat,uu____6031) ->
          let uu____6032 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____6051 =
                  let uu____6052 =
                    let uu____6053 =
                      let uu____6054 =
                        p_tmArrow
                          (Arrows
                             ((Prims.parse_int "2"), (Prims.parse_int "2")))
                          p_tmNoEq t
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6054
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6053  in
                  FStar_Pprint.group uu____6052  in
                (pat1, uu____6051)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____6070 =
                  let uu____6071 =
                    let uu____6072 =
                      let uu____6073 =
                        let uu____6074 =
                          p_tmArrow
                            (Arrows
                               ((Prims.parse_int "2"), (Prims.parse_int "2")))
                            p_tmNoEq t
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6074
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6073
                       in
                    FStar_Pprint.group uu____6072  in
                  let uu____6079 =
                    let uu____6080 =
                      let uu____6081 = str "by"  in
                      let uu____6083 =
                        let uu____6084 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6084
                         in
                      FStar_Pprint.op_Hat_Hat uu____6081 uu____6083  in
                    FStar_Pprint.group uu____6080  in
                  FStar_Pprint.op_Hat_Hat uu____6071 uu____6079  in
                (pat1, uu____6070)
            | uu____6085 -> (pat, FStar_Pprint.empty)  in
          (match uu____6032 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____6089);
                       FStar_Parser_AST.prange = uu____6090;_},pats)
                    ->
                    let uu____6100 =
                      let uu____6101 =
                        let uu____6102 =
                          let uu____6103 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____6103  in
                        FStar_Pprint.group uu____6102  in
                      let uu____6104 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____6101 uu____6104  in
                    prefix2_nonempty uu____6100 ascr_doc
                | uu____6105 ->
                    let uu____6106 =
                      let uu____6107 =
                        let uu____6108 =
                          let uu____6109 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____6109  in
                        FStar_Pprint.group uu____6108  in
                      FStar_Pprint.op_Hat_Hat uu____6107 ascr_doc  in
                    FStar_Pprint.group uu____6106))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6111  ->
      match uu____6111 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let uu____6119 = p_term_sep false false e  in
          (match uu____6119 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6129 =
                 let uu____6130 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6130  in
               let uu____6131 =
                 let uu____6132 =
                   let uu____6133 =
                     let uu____6134 =
                       let uu____6135 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6135
                        in
                     FStar_Pprint.group uu____6134  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6133  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6132  in
               FStar_Pprint.ifflat uu____6129 uu____6131)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_6136  ->
    match uu___117_6136 with
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
        let uu____6161 = p_uident uid  in
        let uu____6162 = p_binders true bs  in
        let uu____6164 =
          let uu____6165 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6165  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6161 uu____6162 uu____6164

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
          let uu____6180 =
            let uu____6181 =
              let uu____6182 =
                let uu____6183 = p_uident uid  in
                let uu____6184 = p_binders true bs  in
                let uu____6186 =
                  let uu____6187 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6187  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6183 uu____6184 uu____6186
                 in
              FStar_Pprint.group uu____6182  in
            let uu____6192 =
              let uu____6193 = str "with"  in
              let uu____6195 =
                let uu____6196 =
                  let uu____6197 =
                    let uu____6198 =
                      let uu____6199 =
                        let uu____6200 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6200
                         in
                      separate_map_last uu____6199 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6198  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6197  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6196  in
              FStar_Pprint.op_Hat_Hat uu____6193 uu____6195  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6181 uu____6192  in
          braces_with_nesting uu____6180

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6204,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6237 =
            let uu____6238 = p_lident lid  in
            let uu____6239 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6238 uu____6239  in
          let uu____6240 = p_simpleTerm ps false e  in
          prefix2 uu____6237 uu____6240
      | uu____6242 ->
          let uu____6243 =
            let uu____6245 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6245
             in
          failwith uu____6243

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6328 =
        match uu____6328 with
        | (kwd,t) ->
            let uu____6339 =
              let uu____6340 = str kwd  in
              let uu____6341 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6340 uu____6341  in
            let uu____6342 = p_simpleTerm ps false t  in
            prefix2 uu____6339 uu____6342
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6349 =
      let uu____6350 =
        let uu____6351 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6352 =
          let uu____6353 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6353  in
        FStar_Pprint.op_Hat_Hat uu____6351 uu____6352  in
      let uu____6355 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6350 uu____6355  in
    let uu____6356 =
      let uu____6357 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6357  in
    FStar_Pprint.op_Hat_Hat uu____6349 uu____6356

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_6358  ->
    match uu___118_6358 with
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
        let uu____6378 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6378 FStar_Pprint.hardline
    | uu____6379 ->
        let uu____6380 =
          let uu____6381 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6381  in
        FStar_Pprint.op_Hat_Hat uu____6380 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_6384  ->
    match uu___119_6384 with
    | FStar_Parser_AST.Rec  ->
        let uu____6385 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6385
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_6387  ->
    match uu___120_6387 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____6391,e) ->
             let uu____6397 = str "#["  in
             let uu____6399 =
               let uu____6400 = p_term false false e  in
               let uu____6403 =
                 let uu____6404 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____6404 break1  in
               FStar_Pprint.op_Hat_Hat uu____6400 uu____6403  in
             FStar_Pprint.op_Hat_Hat uu____6397 uu____6399
         | uu____6406 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6412 =
          let uu____6413 =
            let uu____6414 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6414  in
          FStar_Pprint.separate_map uu____6413 p_tuplePattern pats  in
        FStar_Pprint.group uu____6412
    | uu____6415 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6424 =
          let uu____6425 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6425 p_constructorPattern pats  in
        FStar_Pprint.group uu____6424
    | uu____6426 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6429;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6434 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6435 = p_constructorPattern hd1  in
        let uu____6436 = p_constructorPattern tl1  in
        infix0 uu____6434 uu____6435 uu____6436
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6438;_},pats)
        ->
        let uu____6444 = p_quident uid  in
        let uu____6445 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6444 uu____6445
    | uu____6446 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6462;
               FStar_Parser_AST.blevel = uu____6463;
               FStar_Parser_AST.aqual = uu____6464;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6473 =
               let uu____6474 = p_ident lid  in
               p_refinement aqual uu____6474 t1 phi  in
             soft_parens_with_nesting uu____6473
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6477;
               FStar_Parser_AST.blevel = uu____6478;
               FStar_Parser_AST.aqual = uu____6479;_},phi))
             ->
             let uu____6485 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6485
         | uu____6486 ->
             let uu____6491 =
               let uu____6492 = p_tuplePattern pat  in
               let uu____6493 =
                 let uu____6494 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6494
                  in
               FStar_Pprint.op_Hat_Hat uu____6492 uu____6493  in
             soft_parens_with_nesting uu____6491)
    | FStar_Parser_AST.PatList pats ->
        let uu____6498 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6498 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6517 =
          match uu____6517 with
          | (lid,pat) ->
              let uu____6524 = p_qlident lid  in
              let uu____6525 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6524 uu____6525
           in
        let uu____6526 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6526
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6538 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6539 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6538 uu____6539 uu____6540
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6551 =
          let uu____6552 =
            let uu____6553 =
              let uu____6554 = FStar_Ident.text_of_id op  in str uu____6554
               in
            let uu____6556 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6553 uu____6556  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6552  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6551
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6560 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6560 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6568 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6569 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6568 uu____6569
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6571 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6575;
           FStar_Parser_AST.prange = uu____6576;_},uu____6577)
        ->
        let uu____6582 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6582
    | FStar_Parser_AST.PatTuple (uu____6583,false ) ->
        let uu____6590 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6590
    | uu____6591 ->
        let uu____6592 =
          let uu____6594 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6594  in
        failwith uu____6592

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6599;_},uu____6600)
        -> true
    | uu____6607 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6613) -> true
    | uu____6615 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6622 = p_binder' is_atomic b  in
      match uu____6622 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document,FStar_Pprint.document
                               FStar_Pervasives_Native.option,catf)
        FStar_Pervasives_Native.tuple3)
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6661 =
            let uu____6662 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6663 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6662 uu____6663  in
          (uu____6661, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6669 = p_lident lid  in
          (uu____6669, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6676 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6687;
                   FStar_Parser_AST.blevel = uu____6688;
                   FStar_Parser_AST.aqual = uu____6689;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6694 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6694 t1 phi
            | uu____6695 ->
                let t' =
                  let uu____6697 = is_typ_tuple t  in
                  if uu____6697
                  then
                    let uu____6700 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6700
                  else p_tmFormula t  in
                let uu____6703 =
                  let uu____6704 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6705 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6704 uu____6705  in
                (uu____6703, t')
             in
          (match uu____6676 with
           | (b',t') ->
               let catf =
                 let uu____6723 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6723
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6730 =
                         let uu____6731 =
                           let uu____6732 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6732
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6731
                          in
                       FStar_Pprint.group uu____6730
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6737 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6737)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____6746 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6774;
                  FStar_Parser_AST.blevel = uu____6775;
                  FStar_Parser_AST.aqual = uu____6776;_},phi)
               ->
               let uu____6780 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6780 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6801 ->
               if is_atomic
               then
                 let uu____6813 = p_atomicTerm t  in
                 (uu____6813, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6820 = p_appTerm t  in
                  (uu____6820, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6831 = p_refinement' aqual_opt binder t phi  in
          match uu____6831 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document,FStar_Pprint.document)
            FStar_Pervasives_Native.tuple2)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____6847 -> false
            | FStar_Parser_AST.App uu____6859 -> false
            | FStar_Parser_AST.Op uu____6867 -> false
            | uu____6875 -> true  in
          let uu____6877 = p_noSeqTerm false false phi  in
          match uu____6877 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6894 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6894)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____6903 =
                let uu____6904 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6904 binder  in
              let uu____6905 =
                let uu____6906 = p_appTerm t  in
                let uu____6907 =
                  let uu____6908 =
                    let uu____6909 =
                      let uu____6910 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6911 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6910 uu____6911  in
                    FStar_Pprint.group uu____6909  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____6908
                   in
                FStar_Pprint.op_Hat_Hat uu____6906 uu____6907  in
              (uu____6903, uu____6905)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6925 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6925

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6929 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6932 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6932)
       in
    if uu____6929
    then FStar_Pprint.underscore
    else (let uu____6937 = FStar_Ident.text_of_id lid  in str uu____6937)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6940 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6943 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6943)
       in
    if uu____6940
    then FStar_Pprint.underscore
    else (let uu____6948 = FStar_Ident.text_of_lid lid  in str uu____6948)

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
          let uu____6969 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____6969
        else
          (let uu____6972 =
             let uu____6973 =
               let uu____6974 =
                 let uu____6975 =
                   let uu____6976 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6976  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____6975  in
               FStar_Pprint.group uu____6974  in
             let uu____6977 =
               let uu____6978 =
                 let uu____6979 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6979  in
               FStar_Pprint.op_Hat_Hat comm uu____6978  in
             FStar_Pprint.ifflat uu____6973 uu____6977  in
           FStar_All.pipe_left FStar_Pprint.group uu____6972)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6987 = p_noSeqTerm true false e1  in
            (match uu____6987 with
             | (comm,t1) ->
                 let uu____6996 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6997 =
                   let uu____6998 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6998
                    in
                 FStar_Pprint.op_Hat_Hat uu____6996 uu____6997)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7002 =
              let uu____7003 =
                let uu____7004 =
                  let uu____7005 = p_lident x  in
                  let uu____7006 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7005 uu____7006  in
                let uu____7007 =
                  let uu____7008 = p_noSeqTermAndComment true false e1  in
                  let uu____7011 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7008 uu____7011  in
                op_Hat_Slash_Plus_Hat uu____7004 uu____7007  in
              FStar_Pprint.group uu____7003  in
            let uu____7012 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7002 uu____7012
        | uu____7013 ->
            let uu____7014 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7014

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
            let uu____7026 = p_noSeqTerm true false e1  in
            (match uu____7026 with
             | (comm,t1) ->
                 let uu____7039 =
                   let uu____7040 =
                     let uu____7041 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7041  in
                   let uu____7042 =
                     let uu____7043 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7043
                      in
                   FStar_Pprint.op_Hat_Hat uu____7040 uu____7042  in
                 (comm, uu____7039))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7047 =
              let uu____7048 =
                let uu____7049 =
                  let uu____7050 =
                    let uu____7051 = p_lident x  in
                    let uu____7052 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7051 uu____7052  in
                  let uu____7053 =
                    let uu____7054 = p_noSeqTermAndComment true false e1  in
                    let uu____7057 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7054 uu____7057  in
                  op_Hat_Slash_Plus_Hat uu____7050 uu____7053  in
                FStar_Pprint.group uu____7049  in
              let uu____7058 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7048 uu____7058  in
            (FStar_Pprint.empty, uu____7047)
        | uu____7059 -> p_noSeqTerm ps pb e

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
            let uu____7083 =
              let uu____7084 = p_tmIff e1  in
              let uu____7085 =
                let uu____7086 =
                  let uu____7087 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7087
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7086  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7084 uu____7085  in
            FStar_Pprint.group uu____7083
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7093 =
              let uu____7094 = p_tmIff e1  in
              let uu____7095 =
                let uu____7096 =
                  let uu____7097 =
                    let uu____7098 = p_typ false false t  in
                    let uu____7101 =
                      let uu____7102 = str "by"  in
                      let uu____7104 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7102 uu____7104  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7098 uu____7101  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7097
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7096  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7094 uu____7095  in
            FStar_Pprint.group uu____7093
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7105;_},e1::e2::e3::[])
            ->
            let uu____7112 =
              let uu____7113 =
                let uu____7114 =
                  let uu____7115 = p_atomicTermNotQUident e1  in
                  let uu____7116 =
                    let uu____7117 =
                      let uu____7118 =
                        let uu____7119 = p_term false false e2  in
                        soft_parens_with_nesting uu____7119  in
                      let uu____7122 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7118 uu____7122  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7117  in
                  FStar_Pprint.op_Hat_Hat uu____7115 uu____7116  in
                FStar_Pprint.group uu____7114  in
              let uu____7123 =
                let uu____7124 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7124  in
              FStar_Pprint.op_Hat_Hat uu____7113 uu____7123  in
            FStar_Pprint.group uu____7112
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7125;_},e1::e2::e3::[])
            ->
            let uu____7132 =
              let uu____7133 =
                let uu____7134 =
                  let uu____7135 = p_atomicTermNotQUident e1  in
                  let uu____7136 =
                    let uu____7137 =
                      let uu____7138 =
                        let uu____7139 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7139  in
                      let uu____7142 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7138 uu____7142  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7137  in
                  FStar_Pprint.op_Hat_Hat uu____7135 uu____7136  in
                FStar_Pprint.group uu____7134  in
              let uu____7143 =
                let uu____7144 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7144  in
              FStar_Pprint.op_Hat_Hat uu____7133 uu____7143  in
            FStar_Pprint.group uu____7132
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7154 =
              let uu____7155 = str "requires"  in
              let uu____7157 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7155 uu____7157  in
            FStar_Pprint.group uu____7154
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7167 =
              let uu____7168 = str "ensures"  in
              let uu____7170 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7168 uu____7170  in
            FStar_Pprint.group uu____7167
        | FStar_Parser_AST.Attributes es ->
            let uu____7174 =
              let uu____7175 = str "attributes"  in
              let uu____7177 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7175 uu____7177  in
            FStar_Pprint.group uu____7174
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7182 =
                let uu____7183 =
                  let uu____7184 = str "if"  in
                  let uu____7186 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7184 uu____7186  in
                let uu____7189 =
                  let uu____7190 = str "then"  in
                  let uu____7192 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7190 uu____7192  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7183 uu____7189  in
              FStar_Pprint.group uu____7182
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7196,uu____7197,e31) when
                     is_unit e31 ->
                     let uu____7199 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7199
                 | uu____7202 -> p_noSeqTermAndComment false false e2  in
               let uu____7205 =
                 let uu____7206 =
                   let uu____7207 = str "if"  in
                   let uu____7209 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7207 uu____7209  in
                 let uu____7212 =
                   let uu____7213 =
                     let uu____7214 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7214 e2_doc  in
                   let uu____7216 =
                     let uu____7217 = str "else"  in
                     let uu____7219 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7217 uu____7219  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7213 uu____7216  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7206 uu____7212  in
               FStar_Pprint.group uu____7205)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7242 =
              let uu____7243 =
                let uu____7244 =
                  let uu____7245 = str "try"  in
                  let uu____7247 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7245 uu____7247  in
                let uu____7250 =
                  let uu____7251 = str "with"  in
                  let uu____7253 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7251 uu____7253  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7244 uu____7250  in
              FStar_Pprint.group uu____7243  in
            let uu____7262 = paren_if (ps || pb)  in uu____7262 uu____7242
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7289 =
              let uu____7290 =
                let uu____7291 =
                  let uu____7292 = str "match"  in
                  let uu____7294 = p_noSeqTermAndComment false false e1  in
                  let uu____7297 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7292 uu____7294 uu____7297
                   in
                let uu____7301 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7291 uu____7301  in
              FStar_Pprint.group uu____7290  in
            let uu____7310 = paren_if (ps || pb)  in uu____7310 uu____7289
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7317 =
              let uu____7318 =
                let uu____7319 =
                  let uu____7320 = str "let open"  in
                  let uu____7322 = p_quident uid  in
                  let uu____7323 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7320 uu____7322 uu____7323
                   in
                let uu____7327 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7319 uu____7327  in
              FStar_Pprint.group uu____7318  in
            let uu____7329 = paren_if ps  in uu____7329 uu____7317
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7394 is_last =
              match uu____7394 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7428 =
                          let uu____7429 = str "let"  in
                          let uu____7431 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7429 uu____7431
                           in
                        FStar_Pprint.group uu____7428
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7434 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let uu____7439 = p_term_sep false false e2  in
                  (match uu____7439 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7449 =
                         if is_last
                         then
                           let uu____7451 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7452 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7451 doc_expr1
                             uu____7452
                         else
                           (let uu____7458 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7458)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7449)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7509 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7509
                     else
                       (let uu____7520 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7520)) lbs
               in
            let lbs_doc =
              let uu____7530 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7530  in
            let uu____7531 =
              let uu____7532 =
                let uu____7533 =
                  let uu____7534 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7534
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7533  in
              FStar_Pprint.group uu____7532  in
            let uu____7536 = paren_if ps  in uu____7536 uu____7531
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7543;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7546;
                                                             FStar_Parser_AST.level
                                                               = uu____7547;_})
            when matches_var maybe_x x ->
            let uu____7574 =
              let uu____7575 =
                let uu____7576 = str "function"  in
                let uu____7578 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7576 uu____7578  in
              FStar_Pprint.group uu____7575  in
            let uu____7587 = paren_if (ps || pb)  in uu____7587 uu____7574
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7593 =
              let uu____7594 = str "quote"  in
              let uu____7596 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7594 uu____7596  in
            FStar_Pprint.group uu____7593
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7598 =
              let uu____7599 = str "`"  in
              let uu____7601 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7599 uu____7601  in
            FStar_Pprint.group uu____7598
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7603 =
              let uu____7604 = str "`%"  in
              let uu____7606 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7604 uu____7606  in
            FStar_Pprint.group uu____7603
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7608;
              FStar_Parser_AST.level = uu____7609;_}
            ->
            let uu____7610 =
              let uu____7611 = str "`@"  in
              let uu____7613 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7611 uu____7613  in
            FStar_Pprint.group uu____7610
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7615 =
              let uu____7616 = str "`#"  in
              let uu____7618 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7616 uu____7618  in
            FStar_Pprint.group uu____7615
        | uu____7619 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_7620  ->
    match uu___121_7620 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7632 =
          let uu____7633 = str "[@"  in
          let uu____7635 =
            let uu____7636 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7637 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7636 uu____7637  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7633 uu____7635  in
        FStar_Pprint.group uu____7632

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
                 let uu____7678 =
                   let uu____7679 =
                     let uu____7680 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7680 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____7679 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____7678 term_doc
             | pats ->
                 let uu____7688 =
                   let uu____7689 =
                     let uu____7690 =
                       let uu____7691 =
                         let uu____7692 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7692
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____7691 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7695 = p_trigger trigger  in
                     prefix2 uu____7690 uu____7695  in
                   FStar_Pprint.group uu____7689  in
                 prefix2 uu____7688 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7716 =
                   let uu____7717 =
                     let uu____7718 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7718 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____7717 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____7716 term_doc
             | pats ->
                 let uu____7726 =
                   let uu____7727 =
                     let uu____7728 =
                       let uu____7729 =
                         let uu____7730 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7730
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____7729 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7733 = p_trigger trigger  in
                     prefix2 uu____7728 uu____7733  in
                   FStar_Pprint.group uu____7727  in
                 prefix2 uu____7726 term_doc)
        | uu____7734 -> p_simpleTerm ps pb e

and (p_typ_top :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  ->
      fun pb  ->
        fun e  ->
          with_comment (p_typ_top' style ps pb) e e.FStar_Parser_AST.range
            "!41"

and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  -> fun ps  -> fun pb  -> fun e  -> p_tmArrow style p_tmFormula e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____7750 -> str "forall"
    | FStar_Parser_AST.QExists uu____7764 -> str "exists"
    | uu____7778 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_7780  ->
    match uu___122_7780 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____7792 =
          let uu____7793 =
            let uu____7794 =
              let uu____7795 = str "pattern"  in
              let uu____7797 =
                let uu____7798 =
                  let uu____7799 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____7799
                   in
                FStar_Pprint.op_Hat_Hat uu____7798 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7795 uu____7797  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7794  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7793  in
        FStar_Pprint.group uu____7792

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____7807 = str "\\/"  in
    FStar_Pprint.separate_map uu____7807 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____7814 =
      let uu____7815 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____7815 p_appTerm pats  in
    FStar_Pprint.group uu____7814

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____7827 = p_term_sep false pb e1  in
            (match uu____7827 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____7836 = str "fun"  in
                   let uu____7838 =
                     let uu____7839 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____7839
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____7836 uu____7838  in
                 let uu____7840 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____7842 =
                       let uu____7843 =
                         let uu____7844 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____7844  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____7843
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____7842
                   else
                     (let uu____7847 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____7847)
                    in
                 let uu____7848 = paren_if ps  in uu____7848 uu____7840)
        | uu____7853 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____7861  ->
      match uu____7861 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____7885 =
                    let uu____7886 =
                      let uu____7887 =
                        let uu____7888 = p_tuplePattern p  in
                        let uu____7889 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____7888 uu____7889  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7887
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7886  in
                  FStar_Pprint.group uu____7885
              | FStar_Pervasives_Native.Some f ->
                  let uu____7891 =
                    let uu____7892 =
                      let uu____7893 =
                        let uu____7894 =
                          let uu____7895 =
                            let uu____7896 = p_tuplePattern p  in
                            let uu____7897 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____7896
                              uu____7897
                             in
                          FStar_Pprint.group uu____7895  in
                        let uu____7899 =
                          let uu____7900 =
                            let uu____7903 = p_tmFormula f  in
                            [uu____7903; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____7900  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____7894 uu____7899
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7893
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7892  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____7891
               in
            let uu____7905 = p_term_sep false pb e  in
            match uu____7905 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____7915 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____7915
                   else
                     (let uu____7918 =
                        let uu____7919 =
                          let uu____7920 =
                            let uu____7921 =
                              let uu____7922 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____7922  in
                            op_Hat_Slash_Plus_Hat branch uu____7921  in
                          FStar_Pprint.group uu____7920  in
                        let uu____7923 =
                          let uu____7924 =
                            let uu____7925 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____7925  in
                          FStar_Pprint.op_Hat_Hat branch uu____7924  in
                        FStar_Pprint.ifflat uu____7919 uu____7923  in
                      FStar_Pprint.group uu____7918))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____7929 =
                       let uu____7930 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____7930  in
                     op_Hat_Slash_Plus_Hat branch uu____7929)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____7941 =
                      let uu____7942 =
                        let uu____7943 =
                          let uu____7944 =
                            let uu____7945 =
                              let uu____7946 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____7946  in
                            FStar_Pprint.separate_map uu____7945
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7944
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7943
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7942  in
                    FStar_Pprint.group uu____7941
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____7948 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____7950;_},e1::e2::[])
        ->
        let uu____7956 = str "<==>"  in
        let uu____7958 = p_tmImplies e1  in
        let uu____7959 = p_tmIff e2  in
        infix0 uu____7956 uu____7958 uu____7959
    | uu____7960 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____7962;_},e1::e2::[])
        ->
        let uu____7968 = str "==>"  in
        let uu____7970 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            p_tmFormula e1
           in
        let uu____7975 = p_tmImplies e2  in
        infix0 uu____7968 uu____7970 uu____7975
    | uu____7976 ->
        p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
          p_tmFormula e

and (p_tmArrow :
  annotation_style ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun p_Tm  ->
      fun e  ->
        let terms =
          match style with
          | Arrows uu____7991 -> p_tmArrow' p_Tm e
          | Binders uu____7998 -> collapse_binders p_Tm e  in
        let uu____8005 =
          FStar_List.splitAt
            ((FStar_List.length terms) - (Prims.parse_int "1")) terms
           in
        match uu____8005 with
        | (terms',last1) ->
            let uu____8025 =
              match style with
              | Arrows (n1,ln) ->
                  let uu____8060 =
                    let uu____8061 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8061  in
                  let uu____8062 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                      FStar_Pprint.space
                     in
                  (n1, ln, terms', uu____8060, uu____8062)
              | Binders (n1,ln) ->
                  let uu____8073 =
                    FStar_List.map soft_parens_with_nesting terms'  in
                  let uu____8076 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                      FStar_Pprint.space
                     in
                  (n1, ln, uu____8073, break1, uu____8076)
               in
            (match uu____8025 with
             | (n1,last_n,terms'1,sep,last_op) ->
                 let last_op1 =
                   if (FStar_List.length terms) > (Prims.parse_int "1")
                   then last_op
                   else FStar_Pprint.empty  in
                 let single_line_arg_indent =
                   FStar_Pprint.repeat n1 FStar_Pprint.space  in
                 (match FStar_List.length terms with
                  | _0_5 when _0_5 = (Prims.parse_int "1") ->
                      FStar_List.hd terms
                  | uu____8100 ->
                      let uu____8101 =
                        let uu____8102 =
                          let uu____8103 = FStar_Pprint.separate sep terms'1
                             in
                          let uu____8104 =
                            let uu____8105 =
                              let uu____8106 = FStar_List.hd last1  in
                              FStar_Pprint.op_Hat_Hat last_op1 uu____8106  in
                            FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                              uu____8105
                             in
                          FStar_Pprint.op_Hat_Hat uu____8103 uu____8104  in
                        let uu____8107 =
                          let uu____8108 =
                            let uu____8109 =
                              let uu____8110 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8111 =
                                let uu____8112 =
                                  let uu____8113 =
                                    let uu____8114 =
                                      FStar_Pprint.op_Hat_Hat sep
                                        single_line_arg_indent
                                       in
                                    let uu____8115 =
                                      FStar_List.map
                                        (fun x  ->
                                           let uu____8121 =
                                             FStar_Pprint.hang
                                               (Prims.parse_int "2") x
                                              in
                                           FStar_Pprint.align uu____8121)
                                        terms'1
                                       in
                                    FStar_Pprint.separate uu____8114
                                      uu____8115
                                     in
                                  FStar_Pprint.op_Hat_Hat
                                    single_line_arg_indent uu____8113
                                   in
                                jump2 uu____8112  in
                              FStar_Pprint.ifflat uu____8110 uu____8111  in
                            FStar_Pprint.group uu____8109  in
                          let uu____8123 =
                            let uu____8124 =
                              let uu____8125 =
                                let uu____8126 = FStar_List.hd last1  in
                                FStar_Pprint.op_Hat_Hat last_op1 uu____8126
                                 in
                              FStar_Pprint.hang last_n uu____8125  in
                            FStar_Pprint.align uu____8124  in
                          FStar_Pprint.prefix n1 (Prims.parse_int "1")
                            uu____8108 uu____8123
                           in
                        FStar_Pprint.ifflat uu____8102 uu____8107  in
                      FStar_Pprint.group uu____8101))

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8140 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8146 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8140 uu____8146
      | uu____8149 -> let uu____8150 = p_Tm e  in [uu____8150]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8203 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8229 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8203 uu____8229
        | uu____8252 ->
            let uu____8253 =
              let uu____8264 = p_Tm1 e1  in
              (uu____8264, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8253]
         in
      let fold_fun bs x =
        let uu____8362 = x  in
        match uu____8362 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____8498 = hd1  in
                 (match uu____8498 with
                  | (b2s,t2,uu____8527) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____8637 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____8698 = cb  in
        match uu____8698 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____8727 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____8740 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____8746 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____8746) hd1 tl1
                         in
                      f uu____8740 typ))
         in
      let binders =
        let uu____8764 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____8764  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____8827 =
        let uu____8828 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____8828 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8827  in
    let disj =
      let uu____8831 =
        let uu____8832 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____8832 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8831  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____8852;_},e1::e2::[])
        ->
        let uu____8858 = p_tmDisjunction e1  in
        let uu____8863 = let uu____8868 = p_tmConjunction e2  in [uu____8868]
           in
        FStar_List.append uu____8858 uu____8863
    | uu____8877 -> let uu____8878 = p_tmConjunction e  in [uu____8878]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____8888;_},e1::e2::[])
        ->
        let uu____8894 = p_tmConjunction e1  in
        let uu____8897 = let uu____8900 = p_tmTuple e2  in [uu____8900]  in
        FStar_List.append uu____8894 uu____8897
    | uu____8901 -> let uu____8902 = p_tmTuple e  in [uu____8902]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range "!5"

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____8921 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____8921
          (fun uu____8929  ->
             match uu____8929 with | (e1,uu____8935) -> p_tmEq e1) args
    | uu____8936 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____8945 =
             let uu____8946 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____8946  in
           FStar_Pprint.group uu____8945)

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
               (let uu____8965 = FStar_Ident.text_of_id op  in
                uu____8965 = "="))
              ||
              (let uu____8970 = FStar_Ident.text_of_id op  in
               uu____8970 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____8976 = levels op1  in
            (match uu____8976 with
             | (left1,mine,right1) ->
                 let uu____8995 =
                   let uu____8996 = FStar_All.pipe_left str op1  in
                   let uu____8998 = p_tmEqWith' p_X left1 e1  in
                   let uu____8999 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____8996 uu____8998 uu____8999  in
                 paren_if_gt curr mine uu____8995)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9000;_},e1::e2::[])
            ->
            let uu____9006 =
              let uu____9007 = p_tmEqWith p_X e1  in
              let uu____9008 =
                let uu____9009 =
                  let uu____9010 =
                    let uu____9011 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9011  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9010  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9009  in
              FStar_Pprint.op_Hat_Hat uu____9007 uu____9008  in
            FStar_Pprint.group uu____9006
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9012;_},e1::[])
            ->
            let uu____9017 = levels "-"  in
            (match uu____9017 with
             | (left1,mine,right1) ->
                 let uu____9037 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9037)
        | uu____9038 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9086)::(e2,uu____9088)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9108 = is_list e  in Prims.op_Negation uu____9108)
              ->
              let op = "::"  in
              let uu____9113 = levels op  in
              (match uu____9113 with
               | (left1,mine,right1) ->
                   let uu____9132 =
                     let uu____9133 = str op  in
                     let uu____9134 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9136 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9133 uu____9134 uu____9136  in
                   paren_if_gt curr mine uu____9132)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9155 = levels op  in
              (match uu____9155 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9189 = p_binder false b  in
                         let uu____9191 =
                           let uu____9192 =
                             let uu____9193 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9193 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9192
                            in
                         FStar_Pprint.op_Hat_Hat uu____9189 uu____9191
                     | FStar_Util.Inr t ->
                         let uu____9195 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____9197 =
                           let uu____9198 =
                             let uu____9199 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9199 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9198
                            in
                         FStar_Pprint.op_Hat_Hat uu____9195 uu____9197
                      in
                   let uu____9200 =
                     let uu____9201 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9206 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____9201 uu____9206  in
                   paren_if_gt curr mine uu____9200)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____9208;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____9238 = levels op  in
              (match uu____9238 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____9258 = str op  in
                     let uu____9259 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____9261 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____9258 uu____9259 uu____9261
                   else
                     (let uu____9265 =
                        let uu____9266 = str op  in
                        let uu____9267 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____9269 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____9266 uu____9267 uu____9269  in
                      paren_if_gt curr mine uu____9265))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9278 = levels op1  in
              (match uu____9278 with
               | (left1,mine,right1) ->
                   let uu____9297 =
                     let uu____9298 = str op1  in
                     let uu____9299 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9301 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9298 uu____9299 uu____9301  in
                   paren_if_gt curr mine uu____9297)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9321 =
                let uu____9322 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9323 =
                  let uu____9324 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9324 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9322 uu____9323  in
              braces_with_nesting uu____9321
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____9329;_},e1::[])
              ->
              let uu____9334 =
                let uu____9335 = str "~"  in
                let uu____9337 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9335 uu____9337  in
              FStar_Pprint.group uu____9334
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____9339;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____9348 = levels op  in
                   (match uu____9348 with
                    | (left1,mine,right1) ->
                        let uu____9367 =
                          let uu____9368 = str op  in
                          let uu____9369 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____9371 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____9368 uu____9369 uu____9371  in
                        paren_if_gt curr mine uu____9367)
               | uu____9373 -> p_X e)
          | uu____9374 -> p_X e

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
        let uu____9381 =
          let uu____9382 = p_lident lid  in
          let uu____9383 =
            let uu____9384 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9384  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9382 uu____9383  in
        FStar_Pprint.group uu____9381
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9387 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9389 = p_appTerm e  in
    let uu____9390 =
      let uu____9391 =
        let uu____9392 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9392 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9391  in
    FStar_Pprint.op_Hat_Hat uu____9389 uu____9390

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9398 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9398 t phi
      | FStar_Parser_AST.TAnnotated uu____9399 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9405 ->
          let uu____9406 =
            let uu____9408 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9408
             in
          failwith uu____9406
      | FStar_Parser_AST.TVariable uu____9411 ->
          let uu____9412 =
            let uu____9414 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9414
             in
          failwith uu____9412
      | FStar_Parser_AST.NoName uu____9417 ->
          let uu____9418 =
            let uu____9420 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9420
             in
          failwith uu____9418

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9424  ->
      match uu____9424 with
      | (lid,e) ->
          let uu____9432 =
            let uu____9433 = p_qlident lid  in
            let uu____9434 =
              let uu____9435 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9435
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9433 uu____9434  in
          FStar_Pprint.group uu____9432

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9438 when is_general_application e ->
        let uu____9445 = head_and_args e  in
        (match uu____9445 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9492 = p_argTerm e1  in
                  let uu____9493 =
                    let uu____9494 =
                      let uu____9495 =
                        let uu____9496 = str "`"  in
                        let uu____9498 =
                          let uu____9499 = p_indexingTerm head1  in
                          let uu____9500 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9499 uu____9500  in
                        FStar_Pprint.op_Hat_Hat uu____9496 uu____9498  in
                      FStar_Pprint.group uu____9495  in
                    let uu____9502 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9494 uu____9502  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9492 uu____9493
              | uu____9503 ->
                  let uu____9510 =
                    let uu____9521 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9521
                    then
                      let uu____9555 =
                        FStar_Util.take
                          (fun uu____9579  ->
                             match uu____9579 with
                             | (uu____9585,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9555 with
                      | (fs_typ_args,args1) ->
                          let uu____9623 =
                            let uu____9624 = p_indexingTerm head1  in
                            let uu____9625 =
                              let uu____9626 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____9626
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____9624 uu____9625  in
                          (uu____9623, args1)
                    else
                      (let uu____9641 = p_indexingTerm head1  in
                       (uu____9641, args))
                     in
                  (match uu____9510 with
                   | (head_doc,args1) ->
                       let uu____9662 =
                         let uu____9663 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____9663 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____9662)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____9685 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____9685)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____9704 =
               let uu____9705 = p_quident lid  in
               let uu____9706 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____9705 uu____9706  in
             FStar_Pprint.group uu____9704
         | hd1::tl1 ->
             let uu____9723 =
               let uu____9724 =
                 let uu____9725 =
                   let uu____9726 = p_quident lid  in
                   let uu____9727 = p_argTerm hd1  in
                   prefix2 uu____9726 uu____9727  in
                 FStar_Pprint.group uu____9725  in
               let uu____9728 =
                 let uu____9729 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____9729  in
               FStar_Pprint.op_Hat_Hat uu____9724 uu____9728  in
             FStar_Pprint.group uu____9723)
    | uu____9734 -> p_indexingTerm e

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
         (let uu____9745 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____9745 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____9749 = str "#"  in
        let uu____9751 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____9749 uu____9751
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____9754 = str "#["  in
        let uu____9756 =
          let uu____9757 = p_indexingTerm t  in
          let uu____9758 =
            let uu____9759 = str "]"  in
            let uu____9761 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____9759 uu____9761  in
          FStar_Pprint.op_Hat_Hat uu____9757 uu____9758  in
        FStar_Pprint.op_Hat_Hat uu____9754 uu____9756
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____9764  ->
    match uu____9764 with | (e,uu____9770) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____9775;_},e1::e2::[])
          ->
          let uu____9781 =
            let uu____9782 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____9783 =
              let uu____9784 =
                let uu____9785 = p_term false false e2  in
                soft_parens_with_nesting uu____9785  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9784  in
            FStar_Pprint.op_Hat_Hat uu____9782 uu____9783  in
          FStar_Pprint.group uu____9781
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____9788;_},e1::e2::[])
          ->
          let uu____9794 =
            let uu____9795 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____9796 =
              let uu____9797 =
                let uu____9798 = p_term false false e2  in
                soft_brackets_with_nesting uu____9798  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9797  in
            FStar_Pprint.op_Hat_Hat uu____9795 uu____9796  in
          FStar_Pprint.group uu____9794
      | uu____9801 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____9806 = p_quident lid  in
        let uu____9807 =
          let uu____9808 =
            let uu____9809 = p_term false false e1  in
            soft_parens_with_nesting uu____9809  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9808  in
        FStar_Pprint.op_Hat_Hat uu____9806 uu____9807
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____9817 =
          let uu____9818 = FStar_Ident.text_of_id op  in str uu____9818  in
        let uu____9820 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____9817 uu____9820
    | uu____9821 -> p_atomicTermNotQUident e

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
         | uu____9834 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____9843 =
          let uu____9844 = FStar_Ident.text_of_id op  in str uu____9844  in
        let uu____9846 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____9843 uu____9846
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____9850 =
          let uu____9851 =
            let uu____9852 =
              let uu____9853 = FStar_Ident.text_of_id op  in str uu____9853
               in
            let uu____9855 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____9852 uu____9855  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9851  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9850
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____9870 = all_explicit args  in
        if uu____9870
        then
          let uu____9873 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____9874 =
            let uu____9875 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____9876 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____9875 p_tmEq uu____9876  in
          let uu____9883 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____9873 uu____9874 uu____9883
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____9905 =
                 let uu____9906 = p_quident lid  in
                 let uu____9907 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____9906 uu____9907  in
               FStar_Pprint.group uu____9905
           | hd1::tl1 ->
               let uu____9924 =
                 let uu____9925 =
                   let uu____9926 =
                     let uu____9927 = p_quident lid  in
                     let uu____9928 = p_argTerm hd1  in
                     prefix2 uu____9927 uu____9928  in
                   FStar_Pprint.group uu____9926  in
                 let uu____9929 =
                   let uu____9930 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____9930  in
                 FStar_Pprint.op_Hat_Hat uu____9925 uu____9929  in
               FStar_Pprint.group uu____9924)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____9937 =
          let uu____9938 = p_atomicTermNotQUident e1  in
          let uu____9939 =
            let uu____9940 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9940  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____9938 uu____9939
           in
        FStar_Pprint.group uu____9937
    | uu____9943 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____9948 = p_quident constr_lid  in
        let uu____9949 =
          let uu____9950 =
            let uu____9951 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9951  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____9950  in
        FStar_Pprint.op_Hat_Hat uu____9948 uu____9949
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____9953 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____9953 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____9955 = p_term_sep false false e1  in
        (match uu____9955 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____9968 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____9968))
    | uu____9969 when is_array e ->
        let es = extract_from_list e  in
        let uu____9973 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____9974 =
          let uu____9975 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____9975
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____9980 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____9973 uu____9974 uu____9980
    | uu____9983 when is_list e ->
        let uu____9984 =
          let uu____9985 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____9986 = extract_from_list e  in
          separate_map_or_flow_last uu____9985
            (fun ps  -> p_noSeqTermAndComment ps false) uu____9986
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____9984 FStar_Pprint.rbracket
    | uu____9995 when is_lex_list e ->
        let uu____9996 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____9997 =
          let uu____9998 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____9999 = extract_from_list e  in
          separate_map_or_flow_last uu____9998
            (fun ps  -> p_noSeqTermAndComment ps false) uu____9999
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____9996 uu____9997 FStar_Pprint.rbracket
    | uu____10008 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10012 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10013 =
          let uu____10014 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10014 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10012 uu____10013 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10024 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____10027 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10024 uu____10027
    | FStar_Parser_AST.Op (op,args) when
        let uu____10036 = handleable_op op args  in
        Prims.op_Negation uu____10036 ->
        let uu____10038 =
          let uu____10040 =
            let uu____10042 = FStar_Ident.text_of_id op  in
            let uu____10044 =
              let uu____10046 =
                let uu____10048 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____10048
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____10046  in
            Prims.strcat uu____10042 uu____10044  in
          Prims.strcat "Operation " uu____10040  in
        failwith uu____10038
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10054 = str "u#"  in
        let uu____10056 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____10054 uu____10056
    | FStar_Parser_AST.Wild  ->
        let uu____10057 = p_term false false e  in
        soft_parens_with_nesting uu____10057
    | FStar_Parser_AST.Const uu____10060 ->
        let uu____10061 = p_term false false e  in
        soft_parens_with_nesting uu____10061
    | FStar_Parser_AST.Op uu____10064 ->
        let uu____10071 = p_term false false e  in
        soft_parens_with_nesting uu____10071
    | FStar_Parser_AST.Tvar uu____10074 ->
        let uu____10075 = p_term false false e  in
        soft_parens_with_nesting uu____10075
    | FStar_Parser_AST.Var uu____10078 ->
        let uu____10079 = p_term false false e  in
        soft_parens_with_nesting uu____10079
    | FStar_Parser_AST.Name uu____10082 ->
        let uu____10083 = p_term false false e  in
        soft_parens_with_nesting uu____10083
    | FStar_Parser_AST.Construct uu____10086 ->
        let uu____10097 = p_term false false e  in
        soft_parens_with_nesting uu____10097
    | FStar_Parser_AST.Abs uu____10100 ->
        let uu____10107 = p_term false false e  in
        soft_parens_with_nesting uu____10107
    | FStar_Parser_AST.App uu____10110 ->
        let uu____10117 = p_term false false e  in
        soft_parens_with_nesting uu____10117
    | FStar_Parser_AST.Let uu____10120 ->
        let uu____10141 = p_term false false e  in
        soft_parens_with_nesting uu____10141
    | FStar_Parser_AST.LetOpen uu____10144 ->
        let uu____10149 = p_term false false e  in
        soft_parens_with_nesting uu____10149
    | FStar_Parser_AST.Seq uu____10152 ->
        let uu____10157 = p_term false false e  in
        soft_parens_with_nesting uu____10157
    | FStar_Parser_AST.Bind uu____10160 ->
        let uu____10167 = p_term false false e  in
        soft_parens_with_nesting uu____10167
    | FStar_Parser_AST.If uu____10170 ->
        let uu____10177 = p_term false false e  in
        soft_parens_with_nesting uu____10177
    | FStar_Parser_AST.Match uu____10180 ->
        let uu____10195 = p_term false false e  in
        soft_parens_with_nesting uu____10195
    | FStar_Parser_AST.TryWith uu____10198 ->
        let uu____10213 = p_term false false e  in
        soft_parens_with_nesting uu____10213
    | FStar_Parser_AST.Ascribed uu____10216 ->
        let uu____10225 = p_term false false e  in
        soft_parens_with_nesting uu____10225
    | FStar_Parser_AST.Record uu____10228 ->
        let uu____10241 = p_term false false e  in
        soft_parens_with_nesting uu____10241
    | FStar_Parser_AST.Project uu____10244 ->
        let uu____10249 = p_term false false e  in
        soft_parens_with_nesting uu____10249
    | FStar_Parser_AST.Product uu____10252 ->
        let uu____10259 = p_term false false e  in
        soft_parens_with_nesting uu____10259
    | FStar_Parser_AST.Sum uu____10262 ->
        let uu____10273 = p_term false false e  in
        soft_parens_with_nesting uu____10273
    | FStar_Parser_AST.QForall uu____10276 ->
        let uu____10289 = p_term false false e  in
        soft_parens_with_nesting uu____10289
    | FStar_Parser_AST.QExists uu____10292 ->
        let uu____10305 = p_term false false e  in
        soft_parens_with_nesting uu____10305
    | FStar_Parser_AST.Refine uu____10308 ->
        let uu____10313 = p_term false false e  in
        soft_parens_with_nesting uu____10313
    | FStar_Parser_AST.NamedTyp uu____10316 ->
        let uu____10321 = p_term false false e  in
        soft_parens_with_nesting uu____10321
    | FStar_Parser_AST.Requires uu____10324 ->
        let uu____10332 = p_term false false e  in
        soft_parens_with_nesting uu____10332
    | FStar_Parser_AST.Ensures uu____10335 ->
        let uu____10343 = p_term false false e  in
        soft_parens_with_nesting uu____10343
    | FStar_Parser_AST.Attributes uu____10346 ->
        let uu____10349 = p_term false false e  in
        soft_parens_with_nesting uu____10349
    | FStar_Parser_AST.Quote uu____10352 ->
        let uu____10357 = p_term false false e  in
        soft_parens_with_nesting uu____10357
    | FStar_Parser_AST.VQuote uu____10360 ->
        let uu____10361 = p_term false false e  in
        soft_parens_with_nesting uu____10361
    | FStar_Parser_AST.Antiquote uu____10364 ->
        let uu____10365 = p_term false false e  in
        soft_parens_with_nesting uu____10365

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_10368  ->
    match uu___125_10368 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10377) ->
        let uu____10380 = str s  in FStar_Pprint.dquotes uu____10380
    | FStar_Const.Const_bytearray (bytes,uu____10382) ->
        let uu____10387 =
          let uu____10388 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10388  in
        let uu____10389 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10387 uu____10389
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_10412 =
          match uu___123_10412 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_10419 =
          match uu___124_10419 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10434  ->
               match uu____10434 with
               | (s,w) ->
                   let uu____10441 = signedness s  in
                   let uu____10442 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10441 uu____10442)
            sign_width_opt
           in
        let uu____10443 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10443 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10447 = FStar_Range.string_of_range r  in str uu____10447
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10451 = p_quident lid  in
        let uu____10452 =
          let uu____10453 =
            let uu____10454 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10454  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10453  in
        FStar_Pprint.op_Hat_Hat uu____10451 uu____10452

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10457 = str "u#"  in
    let uu____10459 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10457 uu____10459

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10461;_},u1::u2::[])
        ->
        let uu____10467 =
          let uu____10468 = p_universeFrom u1  in
          let uu____10469 =
            let uu____10470 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10470  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10468 uu____10469  in
        FStar_Pprint.group uu____10467
    | FStar_Parser_AST.App uu____10471 ->
        let uu____10478 = head_and_args u  in
        (match uu____10478 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10504 =
                    let uu____10505 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10506 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10514  ->
                           match uu____10514 with
                           | (u1,uu____10520) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10505 uu____10506  in
                  FStar_Pprint.group uu____10504
              | uu____10521 ->
                  let uu____10522 =
                    let uu____10524 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10524
                     in
                  failwith uu____10522))
    | uu____10527 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10553 = FStar_Ident.text_of_id id1  in str uu____10553
    | FStar_Parser_AST.Paren u1 ->
        let uu____10556 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10556
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10557;_},uu____10558::uu____10559::[])
        ->
        let uu____10563 = p_universeFrom u  in
        soft_parens_with_nesting uu____10563
    | FStar_Parser_AST.App uu____10564 ->
        let uu____10571 = p_universeFrom u  in
        soft_parens_with_nesting uu____10571
    | uu____10572 ->
        let uu____10573 =
          let uu____10575 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10575
           in
        failwith uu____10573

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
       | FStar_Parser_AST.Module (uu____10664,decls) ->
           let uu____10670 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____10670
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____10679,decls,uu____10681) ->
           let uu____10688 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____10688
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____10748  ->
         match uu____10748 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____10770)) -> false
      | ([],uu____10774) -> false
      | uu____10778 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____10788 -> true
         | uu____10790 -> false)
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
        | FStar_Parser_AST.Module (uu____10833,decls) -> decls
        | FStar_Parser_AST.Interface (uu____10839,decls,uu____10841) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____10893 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____10906;
                 FStar_Parser_AST.doc = uu____10907;
                 FStar_Parser_AST.quals = uu____10908;
                 FStar_Parser_AST.attrs = uu____10909;_}::uu____10910 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____10916 =
                   let uu____10919 =
                     let uu____10922 = FStar_List.tl ds  in d :: uu____10922
                      in
                   d0 :: uu____10919  in
                 (uu____10916, (d0.FStar_Parser_AST.drange))
             | uu____10927 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____10893 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____10984 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____10984 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11093 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11093, comments1))))))
  