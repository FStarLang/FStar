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
            let uu____103 = let uu____106 = f x  in uu____106 :: acc  in
            aux xs uu____103
         in
      aux l []
  
let rec map_if_all :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b Prims.list FStar_Pervasives_Native.option
  =
  fun f  ->
    fun l  ->
      let rec aux l1 acc =
        match l1 with
        | [] -> acc
        | x::xs ->
            let uu____173 = f x  in
            (match uu____173 with
             | FStar_Pervasives_Native.Some r -> aux xs (r :: acc)
             | FStar_Pervasives_Native.None  -> [])
         in
      let r = aux l []  in
      if (FStar_List.length l) = (FStar_List.length r)
      then FStar_Pervasives_Native.Some r
      else FStar_Pervasives_Native.None
  
let rec all : 'a . ('a -> Prims.bool) -> 'a Prims.list -> Prims.bool =
  fun f  ->
    fun l  ->
      match l with
      | [] -> true
      | x::xs ->
          let uu____229 = f x  in if uu____229 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___0_262  ->
         match uu___0_262 with
         | (uu____268,FStar_Parser_AST.Nothing ) -> true
         | uu____270 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____299 'Auu____300 .
    Prims.bool -> ('Auu____299 -> 'Auu____300) -> 'Auu____299 -> 'Auu____300
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
  'Auu____410 'Auu____411 .
    'Auu____410 ->
      ('Auu____411 -> 'Auu____410) ->
        'Auu____411 FStar_Pervasives_Native.option -> 'Auu____410
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
  'Auu____524 .
    FStar_Pprint.document ->
      ('Auu____524 -> FStar_Pprint.document) ->
        'Auu____524 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____549 =
          let uu____550 =
            let uu____551 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____551  in
          FStar_Pprint.separate_map uu____550 f l  in
        FStar_Pprint.group uu____549
  
let precede_break_separate_map :
  'Auu____563 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____563 -> FStar_Pprint.document) ->
          'Auu____563 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____593 =
            let uu____594 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____595 =
              let uu____596 = FStar_List.hd l  in
              FStar_All.pipe_right uu____596 f  in
            FStar_Pprint.precede uu____594 uu____595  in
          let uu____597 =
            let uu____598 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____604 =
                   let uu____605 =
                     let uu____606 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____606  in
                   FStar_Pprint.op_Hat_Hat sep uu____605  in
                 FStar_Pprint.op_Hat_Hat break1 uu____604) uu____598
             in
          FStar_Pprint.op_Hat_Hat uu____593 uu____597
  
let concat_break_map :
  'Auu____614 .
    ('Auu____614 -> FStar_Pprint.document) ->
      'Auu____614 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____634 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____638 = f x  in FStar_Pprint.op_Hat_Hat uu____638 break1)
          l
         in
      FStar_Pprint.group uu____634
  
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
    let uu____701 = str "begin"  in
    let uu____703 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____701 contents uu____703
  
let separate_map_last :
  'Auu____716 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____716 -> FStar_Pprint.document) ->
        'Auu____716 Prims.list -> FStar_Pprint.document
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
  'Auu____768 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____768 -> FStar_Pprint.document) ->
        'Auu____768 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____800 =
          let uu____801 =
            let uu____802 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____802  in
          separate_map_last uu____801 f l  in
        FStar_Pprint.group uu____800
  
let separate_map_or_flow :
  'Auu____812 .
    FStar_Pprint.document ->
      ('Auu____812 -> FStar_Pprint.document) ->
        'Auu____812 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____850 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____850 -> FStar_Pprint.document) ->
        'Auu____850 Prims.list -> FStar_Pprint.document
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
  'Auu____902 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____902 -> FStar_Pprint.document) ->
        'Auu____902 Prims.list -> FStar_Pprint.document
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
              let uu____984 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____984
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1006 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1006 -> FStar_Pprint.document) ->
                  'Auu____1006 Prims.list -> FStar_Pprint.document
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
                    (let uu____1065 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1065
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1085 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1085 -> FStar_Pprint.document) ->
                  'Auu____1085 Prims.list -> FStar_Pprint.document
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
                    (let uu____1144 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1144
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1163  ->
    match uu____1163 with
    | (comment,keywords) ->
        let uu____1197 =
          let uu____1198 =
            let uu____1201 = str comment  in
            let uu____1202 =
              let uu____1205 =
                let uu____1208 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1219  ->
                       match uu____1219 with
                       | (k,v1) ->
                           let uu____1232 =
                             let uu____1235 = str k  in
                             let uu____1236 =
                               let uu____1239 =
                                 let uu____1242 = str v1  in [uu____1242]  in
                               FStar_Pprint.rarrow :: uu____1239  in
                             uu____1235 :: uu____1236  in
                           FStar_Pprint.concat uu____1232) keywords
                   in
                [uu____1208]  in
              FStar_Pprint.space :: uu____1205  in
            uu____1201 :: uu____1202  in
          FStar_Pprint.concat uu____1198  in
        FStar_Pprint.group uu____1197
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1252 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1268 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1268
      | uu____1271 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1322::(e2,uu____1324)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1347 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1371,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1382,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1403 = extract_from_list e2  in e1 :: uu____1403
    | uu____1406 ->
        let uu____1407 =
          let uu____1409 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1409  in
        failwith uu____1407
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1423;
           FStar_Parser_AST.level = uu____1424;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1426 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1438;
           FStar_Parser_AST.level = uu____1439;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1441;
                                                         FStar_Parser_AST.level
                                                           = uu____1442;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1444;
                                                    FStar_Parser_AST.level =
                                                      uu____1445;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1447;
                FStar_Parser_AST.level = uu____1448;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1450;
           FStar_Parser_AST.level = uu____1451;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1453 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1465 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1466;
           FStar_Parser_AST.range = uu____1467;
           FStar_Parser_AST.level = uu____1468;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1469;
                                                         FStar_Parser_AST.range
                                                           = uu____1470;
                                                         FStar_Parser_AST.level
                                                           = uu____1471;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1473;
                                                    FStar_Parser_AST.level =
                                                      uu____1474;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1475;
                FStar_Parser_AST.range = uu____1476;
                FStar_Parser_AST.level = uu____1477;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1479;
           FStar_Parser_AST.level = uu____1480;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1482 = extract_from_ref_set e1  in
        let uu____1485 = extract_from_ref_set e2  in
        FStar_List.append uu____1482 uu____1485
    | uu____1488 ->
        let uu____1489 =
          let uu____1491 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1491  in
        failwith uu____1489
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1503 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1503
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1512 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1512
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1523 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1523 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1533 = FStar_Ident.text_of_id op  in uu____1533 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1603 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1623 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1634 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1645 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1671  ->
    match uu___1_1671 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1706  ->
      match uu___2_1706 with
      | FStar_Util.Inl c ->
          let uu____1719 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1719 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1735 .
    Prims.string ->
      ('Auu____1735 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1759  ->
      match uu____1759 with
      | (assoc_levels,tokens) ->
          let uu____1791 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1791 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_1963 =
    match uu___3_1963 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2013  ->
         match uu____2013 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2088 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2088 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2140) ->
          assoc_levels
      | uu____2178 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2211 . ('Auu____2211 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2260 =
        FStar_List.tryFind
          (fun uu____2296  ->
             match uu____2296 with
             | (uu____2313,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2260 with
      | FStar_Pervasives_Native.Some ((uu____2342,l1,uu____2344),uu____2345)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2395 =
            let uu____2397 =
              let uu____2399 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2399  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2397
             in
          failwith uu____2395
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2434 = assign_levels level_associativity_spec op  in
    match uu____2434 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2493 =
      let uu____2496 =
        let uu____2502 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2502  in
      FStar_List.tryFind uu____2496 operatorInfix0ad12  in
    uu____2493 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2569 =
      let uu____2584 =
        let uu____2602 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2602  in
      FStar_List.tryFind uu____2584 opinfix34  in
    uu____2569 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2668 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2668
    then (Prims.parse_int "1")
    else
      (let uu____2681 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2681
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2727 . FStar_Ident.ident -> 'Auu____2727 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2743 when _2743 = (Prims.parse_int "0") -> true
      | _2745 when _2745 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2747 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2747 ["-"; "~"])
      | _2755 when _2755 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2757 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2757
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2779 when _2779 = (Prims.parse_int "3") ->
          let uu____2780 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2780 [".()<-"; ".[]<-"]
      | uu____2788 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2834 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2886 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2928 -> true
      | uu____2934 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2967 = FStar_List.for_all is_binder_annot bs  in
          if uu____2967
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____2982 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____2987 = all_binders e (Prims.parse_int "0")  in
    match uu____2987 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3026 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3026
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
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
  'Auu____3175 .
    ('Auu____3175 -> FStar_Pprint.document) ->
      'Auu____3175 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3217 = FStar_ST.op_Bang comment_stack  in
          match uu____3217 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3288 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3288 FStar_Pprint.hardline  in
              let uu____3289 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3289
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3331 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3331 print_pos lookahead_pos))
              else
                (let uu____3334 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3334))
           in
        let uu____3337 =
          let uu____3343 =
            let uu____3344 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3344  in
          let uu____3345 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3343 uu____3345  in
        match uu____3337 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3354 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3354
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3366 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3366)
  
let with_comment_sep :
  'Auu____3378 'Auu____3379 .
    ('Auu____3378 -> 'Auu____3379) ->
      'Auu____3378 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3379)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3425 = FStar_ST.op_Bang comment_stack  in
          match uu____3425 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3496 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3496
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3538 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3542 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3542)
                     in
                  comments_before_pos uu____3538 print_pos lookahead_pos))
              else
                (let uu____3545 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3545))
           in
        let uu____3548 =
          let uu____3554 =
            let uu____3555 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3555  in
          let uu____3556 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3554 uu____3556  in
        match uu____3548 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3569 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3569
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
                let uu____3622 = FStar_ST.op_Bang comment_stack  in
                match uu____3622 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3716 =
                          let uu____3718 =
                            let uu____3720 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3720  in
                          uu____3718 - lbegin  in
                        max k uu____3716  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3725 =
                          let uu____3726 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3727 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3726 uu____3727  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3725  in
                      let uu____3728 =
                        let uu____3730 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3730  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3728 pos meta_decl doc2 true init1))
                | uu____3733 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3746 = FStar_Range.line_of_pos pos  in
                         uu____3746 - lbegin  in
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
                       let uu____3788 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3788)
  
let separate_map_with_comments :
  'Auu____3802 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3802 -> FStar_Pprint.document) ->
          'Auu____3802 Prims.list ->
            ('Auu____3802 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3861 x =
              match uu____3861 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3880 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3880 meta_decl doc1 false false
                     in
                  let uu____3884 =
                    let uu____3886 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3886  in
                  let uu____3887 =
                    let uu____3888 =
                      let uu____3889 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3889  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3888  in
                  (uu____3884, uu____3887)
               in
            let uu____3891 =
              let uu____3898 = FStar_List.hd xs  in
              let uu____3899 = FStar_List.tl xs  in (uu____3898, uu____3899)
               in
            match uu____3891 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3917 =
                    let uu____3919 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3919  in
                  let uu____3920 =
                    let uu____3921 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3921  in
                  (uu____3917, uu____3920)  in
                let uu____3923 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3923
  
let separate_map_with_comments_kw :
  'Auu____3950 'Auu____3951 .
    'Auu____3950 ->
      'Auu____3950 ->
        ('Auu____3950 -> 'Auu____3951 -> FStar_Pprint.document) ->
          'Auu____3951 Prims.list ->
            ('Auu____3951 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4015 x =
              match uu____4015 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4034 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4034 meta_decl doc1 false false
                     in
                  let uu____4038 =
                    let uu____4040 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4040  in
                  let uu____4041 =
                    let uu____4042 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4042  in
                  (uu____4038, uu____4041)
               in
            let uu____4044 =
              let uu____4051 = FStar_List.hd xs  in
              let uu____4052 = FStar_List.tl xs  in (uu____4051, uu____4052)
               in
            match uu____4044 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4070 =
                    let uu____4072 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4072  in
                  let uu____4073 = f prefix1 x  in (uu____4070, uu____4073)
                   in
                let uu____4075 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4075
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5061)) ->
          let uu____5064 =
            let uu____5066 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5066 FStar_Util.is_upper  in
          if uu____5064
          then
            let uu____5072 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5072 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5075 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5082 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5085 =
      let uu____5086 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5087 =
        let uu____5088 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5088  in
      FStar_Pprint.op_Hat_Hat uu____5086 uu____5087  in
    FStar_Pprint.op_Hat_Hat uu____5082 uu____5085

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5090 ->
        let uu____5091 =
          let uu____5092 = str "@ "  in
          let uu____5094 =
            let uu____5095 =
              let uu____5096 =
                let uu____5097 =
                  let uu____5098 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5098  in
                FStar_Pprint.op_Hat_Hat uu____5097 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5096  in
            FStar_Pprint.op_Hat_Hat uu____5095 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5092 uu____5094  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5091

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5101  ->
    match uu____5101 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5149 =
                match uu____5149 with
                | (kwd,arg) ->
                    let uu____5162 = str "@"  in
                    let uu____5164 =
                      let uu____5165 = str kwd  in
                      let uu____5166 =
                        let uu____5167 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5167
                         in
                      FStar_Pprint.op_Hat_Hat uu____5165 uu____5166  in
                    FStar_Pprint.op_Hat_Hat uu____5162 uu____5164
                 in
              let uu____5168 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5168 FStar_Pprint.hardline
           in
        let uu____5175 =
          let uu____5176 =
            let uu____5177 =
              let uu____5178 = str doc1  in
              let uu____5179 =
                let uu____5180 =
                  let uu____5181 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5181  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5180  in
              FStar_Pprint.op_Hat_Hat uu____5178 uu____5179  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5177  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5176  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5175

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5185 =
          let uu____5186 = str "val"  in
          let uu____5188 =
            let uu____5189 =
              let uu____5190 = p_lident lid  in
              let uu____5191 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5190 uu____5191  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5189  in
          FStar_Pprint.op_Hat_Hat uu____5186 uu____5188  in
        let uu____5192 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5185 uu____5192
    | FStar_Parser_AST.TopLevelLet (uu____5195,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5220 =
               let uu____5221 = str "let"  in p_letlhs uu____5221 lb false
                in
             FStar_Pprint.group uu____5220) lbs
    | uu____5224 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_5239 =
          match uu___4_5239 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5247 = f x  in
              let uu____5248 =
                let uu____5249 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5249  in
              FStar_Pprint.op_Hat_Hat uu____5247 uu____5248
           in
        let uu____5250 = str "["  in
        let uu____5252 =
          let uu____5253 = p_list' l  in
          let uu____5254 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5253 uu____5254  in
        FStar_Pprint.op_Hat_Hat uu____5250 uu____5252

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5258 =
          let uu____5259 = str "open"  in
          let uu____5261 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5259 uu____5261  in
        FStar_Pprint.group uu____5258
    | FStar_Parser_AST.Include uid ->
        let uu____5263 =
          let uu____5264 = str "include"  in
          let uu____5266 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5266  in
        FStar_Pprint.group uu____5263
    | FStar_Parser_AST.Friend uid ->
        let uu____5268 =
          let uu____5269 = str "friend"  in
          let uu____5271 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5269 uu____5271  in
        FStar_Pprint.group uu____5268
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5274 =
          let uu____5275 = str "module"  in
          let uu____5277 =
            let uu____5278 =
              let uu____5279 = p_uident uid1  in
              let uu____5280 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5279 uu____5280  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5278  in
          FStar_Pprint.op_Hat_Hat uu____5275 uu____5277  in
        let uu____5281 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5274 uu____5281
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5283 =
          let uu____5284 = str "module"  in
          let uu____5286 =
            let uu____5287 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5287  in
          FStar_Pprint.op_Hat_Hat uu____5284 uu____5286  in
        FStar_Pprint.group uu____5283
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5288,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5325 = str "effect"  in
          let uu____5327 =
            let uu____5328 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5328  in
          FStar_Pprint.op_Hat_Hat uu____5325 uu____5327  in
        let uu____5329 =
          let uu____5330 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5330 FStar_Pprint.equals
           in
        let uu____5333 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5329 uu____5333
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5364 =
          let uu____5365 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5365  in
        let uu____5378 =
          let uu____5379 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5417 =
                    let uu____5418 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5418 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5417)) uu____5379
           in
        FStar_Pprint.op_Hat_Hat uu____5364 uu____5378
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5435 = str "let"  in
          let uu____5437 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5435 uu____5437  in
        let uu____5438 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5438 p_letbinding lbs
          (fun uu____5448  ->
             match uu____5448 with
             | (p,t) ->
                 let uu____5455 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5455;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5461 =
          let uu____5462 = str "val"  in
          let uu____5464 =
            let uu____5465 =
              let uu____5466 = p_lident lid  in
              let uu____5467 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5466 uu____5467  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5465  in
          FStar_Pprint.op_Hat_Hat uu____5462 uu____5464  in
        FStar_All.pipe_left FStar_Pprint.group uu____5461
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5472 =
            let uu____5474 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5474 FStar_Util.is_upper  in
          if uu____5472
          then FStar_Pprint.empty
          else
            (let uu____5482 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5482 FStar_Pprint.space)
           in
        let uu____5484 =
          let uu____5485 = p_ident id1  in
          let uu____5486 =
            let uu____5487 =
              let uu____5488 =
                let uu____5489 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5489  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5488  in
            FStar_Pprint.group uu____5487  in
          FStar_Pprint.op_Hat_Hat uu____5485 uu____5486  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5484
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5498 = str "exception"  in
        let uu____5500 =
          let uu____5501 =
            let uu____5502 = p_uident uid  in
            let uu____5503 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5507 =
                     let uu____5508 = str "of"  in
                     let uu____5510 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5508 uu____5510  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5507) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5502 uu____5503  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5501  in
        FStar_Pprint.op_Hat_Hat uu____5498 uu____5500
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5514 = str "new_effect"  in
        let uu____5516 =
          let uu____5517 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5517  in
        FStar_Pprint.op_Hat_Hat uu____5514 uu____5516
    | FStar_Parser_AST.SubEffect se ->
        let uu____5519 = str "sub_effect"  in
        let uu____5521 =
          let uu____5522 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5522  in
        FStar_Pprint.op_Hat_Hat uu____5519 uu____5521
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5525 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5527,uu____5528) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5556 = str "%splice"  in
        let uu____5558 =
          let uu____5559 =
            let uu____5560 = str ";"  in p_list p_uident uu____5560 ids  in
          let uu____5562 =
            let uu____5563 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5563  in
          FStar_Pprint.op_Hat_Hat uu____5559 uu____5562  in
        FStar_Pprint.op_Hat_Hat uu____5556 uu____5558

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5566  ->
    match uu___5_5566 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5569 = str "#set-options"  in
        let uu____5571 =
          let uu____5572 =
            let uu____5573 = str s  in FStar_Pprint.dquotes uu____5573  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5572  in
        FStar_Pprint.op_Hat_Hat uu____5569 uu____5571
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5578 = str "#reset-options"  in
        let uu____5580 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5586 =
                 let uu____5587 = str s  in FStar_Pprint.dquotes uu____5587
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5586) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5578 uu____5580
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5592 = str "#push-options"  in
        let uu____5594 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5600 =
                 let uu____5601 = str s  in FStar_Pprint.dquotes uu____5601
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5600) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5592 uu____5594
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
    fun uu____5632  ->
      match uu____5632 with
      | (typedecl,fsdoc_opt) ->
          let uu____5645 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5645 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5670 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5670
               else
                 (let uu____5673 =
                    let uu____5674 =
                      let uu____5675 =
                        let uu____5676 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5676 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5675  in
                    let uu____5677 =
                      let uu____5678 =
                        let uu____5679 =
                          let uu____5680 =
                            let uu____5681 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5681  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5680
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5679
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5678  in
                    FStar_Pprint.ifflat uu____5674 uu____5677  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5673))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5684  ->
      match uu___6_5684 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5713 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5713, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5730 = p_typ_sep false false t  in
          (match uu____5730 with
           | (comm,doc1) ->
               let uu____5750 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5750, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5806 =
            match uu____5806 with
            | (lid1,t,doc_opt) ->
                let uu____5823 =
                  let uu____5828 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5828
                   in
                (match uu____5823 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5846 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5846  in
          let uu____5855 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5855, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5922 =
            match uu____5922 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5951 =
                    let uu____5952 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5952  in
                  FStar_Range.extend_to_end_of_line uu____5951  in
                let uu____5957 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5957 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5996 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5996, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6001  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6001 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6036 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6036  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6038 =
                        let uu____6041 =
                          let uu____6044 = p_fsdoc fsdoc  in
                          let uu____6045 =
                            let uu____6048 = cont lid_doc  in [uu____6048]
                             in
                          uu____6044 :: uu____6045  in
                        kw :: uu____6041  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6038
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6055 =
                        let uu____6056 =
                          let uu____6057 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6057 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6056
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6055
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6077 =
                          let uu____6078 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6078  in
                        prefix2 uu____6077 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6080  ->
      match uu____6080 with
      | (lid,t,doc_opt) ->
          let uu____6097 =
            let uu____6098 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6099 =
              let uu____6100 = p_lident lid  in
              let uu____6101 =
                let uu____6102 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6102  in
              FStar_Pprint.op_Hat_Hat uu____6100 uu____6101  in
            FStar_Pprint.op_Hat_Hat uu____6098 uu____6099  in
          FStar_Pprint.group uu____6097

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6104  ->
    match uu____6104 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6138 =
            let uu____6139 =
              let uu____6140 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6140  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6139  in
          FStar_Pprint.group uu____6138  in
        let uu____6141 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6142 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6146 =
                 let uu____6147 =
                   let uu____6148 =
                     let uu____6149 =
                       let uu____6150 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6150
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6149  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6148  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6147  in
               FStar_Pprint.group uu____6146) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6141 uu____6142

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6154  ->
      fun inner_let  ->
        match uu____6154 with
        | (pat,uu____6162) ->
            let uu____6163 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6215 =
                    let uu____6222 =
                      let uu____6227 =
                        let uu____6228 =
                          let uu____6229 =
                            let uu____6230 = str "by"  in
                            let uu____6232 =
                              let uu____6233 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6233
                               in
                            FStar_Pprint.op_Hat_Hat uu____6230 uu____6232  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6229
                           in
                        FStar_Pprint.group uu____6228  in
                      (t, uu____6227)  in
                    FStar_Pervasives_Native.Some uu____6222  in
                  (pat1, uu____6215)
              | uu____6244 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6163 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6270);
                         FStar_Parser_AST.prange = uu____6271;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6288 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6288 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6294 =
                        if inner_let
                        then
                          let uu____6308 = pats_as_binders_if_possible pats
                             in
                          match uu____6308 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6331 = pats_as_binders_if_possible pats
                              in
                           match uu____6331 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6294 with
                       | (terms,style) ->
                           let uu____6358 =
                             let uu____6359 =
                               let uu____6360 =
                                 let uu____6361 = p_lident lid  in
                                 let uu____6362 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6361
                                   uu____6362
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6360
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6359  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6358)
                  | uu____6365 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6373 =
                              let uu____6374 =
                                let uu____6375 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6375
                                 in
                              FStar_Pprint.group uu____6374  in
                            FStar_Pprint.op_Hat_Hat uu____6373 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6386 =
                        let uu____6387 =
                          let uu____6388 =
                            let uu____6389 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6389  in
                          FStar_Pprint.group uu____6388  in
                        FStar_Pprint.op_Hat_Hat uu____6387 ascr_doc  in
                      FStar_Pprint.group uu____6386))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6391  ->
      match uu____6391 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6400 = p_term_sep false false e  in
          (match uu____6400 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6410 =
                 let uu____6411 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6411  in
               let uu____6412 =
                 let uu____6413 =
                   let uu____6414 =
                     let uu____6415 =
                       let uu____6416 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6416
                        in
                     FStar_Pprint.group uu____6415  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6414  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6413  in
               FStar_Pprint.ifflat uu____6410 uu____6412)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_6417  ->
    match uu___7_6417 with
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
        let uu____6442 = p_uident uid  in
        let uu____6443 = p_binders true bs  in
        let uu____6445 =
          let uu____6446 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6446  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6442 uu____6443 uu____6445

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
          let uu____6461 =
            let uu____6462 =
              let uu____6463 =
                let uu____6464 = p_uident uid  in
                let uu____6465 = p_binders true bs  in
                let uu____6467 =
                  let uu____6468 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6468  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6464 uu____6465 uu____6467
                 in
              FStar_Pprint.group uu____6463  in
            let uu____6473 =
              let uu____6474 = str "with"  in
              let uu____6476 =
                let uu____6477 =
                  let uu____6478 =
                    let uu____6479 =
                      let uu____6480 =
                        let uu____6481 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6481
                         in
                      separate_map_last uu____6480 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6479  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6478  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6477  in
              FStar_Pprint.op_Hat_Hat uu____6474 uu____6476  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6462 uu____6473  in
          braces_with_nesting uu____6461

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6485,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6518 =
            let uu____6519 = p_lident lid  in
            let uu____6520 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6519 uu____6520  in
          let uu____6521 = p_simpleTerm ps false e  in
          prefix2 uu____6518 uu____6521
      | uu____6523 ->
          let uu____6524 =
            let uu____6526 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6526
             in
          failwith uu____6524

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6609 =
        match uu____6609 with
        | (kwd,t) ->
            let uu____6620 =
              let uu____6621 = str kwd  in
              let uu____6622 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6621 uu____6622  in
            let uu____6623 = p_simpleTerm ps false t  in
            prefix2 uu____6620 uu____6623
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6630 =
      let uu____6631 =
        let uu____6632 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6633 =
          let uu____6634 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6634  in
        FStar_Pprint.op_Hat_Hat uu____6632 uu____6633  in
      let uu____6636 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6631 uu____6636  in
    let uu____6637 =
      let uu____6638 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6638  in
    FStar_Pprint.op_Hat_Hat uu____6630 uu____6637

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6639  ->
    match uu___8_6639 with
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
        let uu____6659 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6659 FStar_Pprint.hardline
    | uu____6660 ->
        let uu____6661 =
          let uu____6662 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6662  in
        FStar_Pprint.op_Hat_Hat uu____6661 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6665  ->
    match uu___9_6665 with
    | FStar_Parser_AST.Rec  ->
        let uu____6666 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6666
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6668  ->
    match uu___10_6668 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6673,e) -> e
          | uu____6679 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6680 = str "#["  in
        let uu____6682 =
          let uu____6683 = p_term false false t1  in
          let uu____6686 =
            let uu____6687 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6687 break1  in
          FStar_Pprint.op_Hat_Hat uu____6683 uu____6686  in
        FStar_Pprint.op_Hat_Hat uu____6680 uu____6682

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6693 =
          let uu____6694 =
            let uu____6695 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6695  in
          FStar_Pprint.separate_map uu____6694 p_tuplePattern pats  in
        FStar_Pprint.group uu____6693
    | uu____6696 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6705 =
          let uu____6706 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6706 p_constructorPattern pats  in
        FStar_Pprint.group uu____6705
    | uu____6707 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6710;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6715 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6716 = p_constructorPattern hd1  in
        let uu____6717 = p_constructorPattern tl1  in
        infix0 uu____6715 uu____6716 uu____6717
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6719;_},pats)
        ->
        let uu____6725 = p_quident uid  in
        let uu____6726 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6725 uu____6726
    | uu____6727 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6743;
               FStar_Parser_AST.blevel = uu____6744;
               FStar_Parser_AST.aqual = uu____6745;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6754 =
               let uu____6755 = p_ident lid  in
               p_refinement aqual uu____6755 t1 phi  in
             soft_parens_with_nesting uu____6754
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6758;
               FStar_Parser_AST.blevel = uu____6759;
               FStar_Parser_AST.aqual = uu____6760;_},phi))
             ->
             let uu____6766 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6766
         | uu____6767 ->
             let uu____6772 =
               let uu____6773 = p_tuplePattern pat  in
               let uu____6774 =
                 let uu____6775 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6775
                  in
               FStar_Pprint.op_Hat_Hat uu____6773 uu____6774  in
             soft_parens_with_nesting uu____6772)
    | FStar_Parser_AST.PatList pats ->
        let uu____6779 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6779 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6798 =
          match uu____6798 with
          | (lid,pat) ->
              let uu____6805 = p_qlident lid  in
              let uu____6806 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6805 uu____6806
           in
        let uu____6807 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6807
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6819 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6820 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6821 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6819 uu____6820 uu____6821
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6832 =
          let uu____6833 =
            let uu____6834 =
              let uu____6835 = FStar_Ident.text_of_id op  in str uu____6835
               in
            let uu____6837 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6834 uu____6837  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6833  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6832
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6841 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6841 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6849 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6850 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6849 uu____6850
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6852 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6856;
           FStar_Parser_AST.prange = uu____6857;_},uu____6858)
        ->
        let uu____6863 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6863
    | FStar_Parser_AST.PatTuple (uu____6864,false ) ->
        let uu____6871 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6871
    | uu____6872 ->
        let uu____6873 =
          let uu____6875 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6875  in
        failwith uu____6873

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6880;_},uu____6881)
        -> true
    | uu____6888 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6894) -> true
    | uu____6896 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6903 = p_binder' is_atomic b  in
      match uu____6903 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document * FStar_Pprint.document
        FStar_Pervasives_Native.option * catf))
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____6940 =
            let uu____6941 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6942 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6941 uu____6942  in
          (uu____6940, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6948 = p_lident lid  in
          (uu____6948, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6955 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6966;
                   FStar_Parser_AST.blevel = uu____6967;
                   FStar_Parser_AST.aqual = uu____6968;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6973 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6973 t1 phi
            | uu____6974 ->
                let t' =
                  let uu____6976 = is_typ_tuple t  in
                  if uu____6976
                  then
                    let uu____6979 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6979
                  else p_tmFormula t  in
                let uu____6982 =
                  let uu____6983 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6984 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6983 uu____6984  in
                (uu____6982, t')
             in
          (match uu____6955 with
           | (b',t') ->
               let catf =
                 let uu____7002 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7002
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7009 =
                         let uu____7010 =
                           let uu____7011 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7011
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7010
                          in
                       FStar_Pprint.group uu____7009
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7016 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7016)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7021 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7049;
                  FStar_Parser_AST.blevel = uu____7050;
                  FStar_Parser_AST.aqual = uu____7051;_},phi)
               ->
               let uu____7055 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7055 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7076 ->
               if is_atomic
               then
                 let uu____7088 = p_atomicTerm t  in
                 (uu____7088, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7095 = p_appTerm t  in
                  (uu____7095, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7106 = p_refinement' aqual_opt binder t phi  in
          match uu____7106 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____7122 -> false
            | FStar_Parser_AST.App uu____7134 -> false
            | FStar_Parser_AST.Op uu____7142 -> false
            | uu____7150 -> true  in
          let uu____7152 = p_noSeqTerm false false phi  in
          match uu____7152 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7169 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7169)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7178 =
                let uu____7179 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7179 binder  in
              let uu____7180 =
                let uu____7181 = p_appTerm t  in
                let uu____7182 =
                  let uu____7183 =
                    let uu____7184 =
                      let uu____7185 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7186 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7185 uu____7186  in
                    FStar_Pprint.group uu____7184  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7183
                   in
                FStar_Pprint.op_Hat_Hat uu____7181 uu____7182  in
              (uu____7178, uu____7180)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7200 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7200

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7204 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7207 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7207)
       in
    if uu____7204
    then FStar_Pprint.underscore
    else (let uu____7212 = FStar_Ident.text_of_id lid  in str uu____7212)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7215 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7218 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7218)
       in
    if uu____7215
    then FStar_Pprint.underscore
    else (let uu____7223 = FStar_Ident.text_of_lid lid  in str uu____7223)

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
          let uu____7244 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7244
        else
          (let uu____7247 =
             let uu____7248 =
               let uu____7249 =
                 let uu____7250 =
                   let uu____7251 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7251  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7250  in
               FStar_Pprint.group uu____7249  in
             let uu____7252 =
               let uu____7253 =
                 let uu____7254 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7254  in
               FStar_Pprint.op_Hat_Hat comm uu____7253  in
             FStar_Pprint.ifflat uu____7248 uu____7252  in
           FStar_All.pipe_left FStar_Pprint.group uu____7247)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7262 = p_noSeqTerm true false e1  in
            (match uu____7262 with
             | (comm,t1) ->
                 let uu____7271 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7272 =
                   let uu____7273 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7273
                    in
                 FStar_Pprint.op_Hat_Hat uu____7271 uu____7272)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7277 =
              let uu____7278 =
                let uu____7279 =
                  let uu____7280 = p_lident x  in
                  let uu____7281 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7280 uu____7281  in
                let uu____7282 =
                  let uu____7283 = p_noSeqTermAndComment true false e1  in
                  let uu____7286 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7283 uu____7286  in
                op_Hat_Slash_Plus_Hat uu____7279 uu____7282  in
              FStar_Pprint.group uu____7278  in
            let uu____7287 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7277 uu____7287
        | uu____7288 ->
            let uu____7289 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7289

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7301 = p_noSeqTerm true false e1  in
            (match uu____7301 with
             | (comm,t1) ->
                 let uu____7314 =
                   let uu____7315 =
                     let uu____7316 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7316  in
                   let uu____7317 =
                     let uu____7318 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7318
                      in
                   FStar_Pprint.op_Hat_Hat uu____7315 uu____7317  in
                 (comm, uu____7314))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7322 =
              let uu____7323 =
                let uu____7324 =
                  let uu____7325 =
                    let uu____7326 = p_lident x  in
                    let uu____7327 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7326 uu____7327  in
                  let uu____7328 =
                    let uu____7329 = p_noSeqTermAndComment true false e1  in
                    let uu____7332 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7329 uu____7332  in
                  op_Hat_Slash_Plus_Hat uu____7325 uu____7328  in
                FStar_Pprint.group uu____7324  in
              let uu____7333 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7323 uu____7333  in
            (FStar_Pprint.empty, uu____7322)
        | uu____7334 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and (p_noSeqTermAndComment :
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
            let uu____7354 =
              let uu____7355 = p_tmIff e1  in
              let uu____7356 =
                let uu____7357 =
                  let uu____7358 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7358
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7357  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7355 uu____7356  in
            FStar_Pprint.group uu____7354
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7364 =
              let uu____7365 = p_tmIff e1  in
              let uu____7366 =
                let uu____7367 =
                  let uu____7368 =
                    let uu____7369 = p_typ false false t  in
                    let uu____7372 =
                      let uu____7373 = str "by"  in
                      let uu____7375 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7373 uu____7375  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7369 uu____7372  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7368
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7367  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7365 uu____7366  in
            FStar_Pprint.group uu____7364
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7376;_},e1::e2::e3::[])
            ->
            let uu____7383 =
              let uu____7384 =
                let uu____7385 =
                  let uu____7386 = p_atomicTermNotQUident e1  in
                  let uu____7387 =
                    let uu____7388 =
                      let uu____7389 =
                        let uu____7390 = p_term false false e2  in
                        soft_parens_with_nesting uu____7390  in
                      let uu____7393 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7389 uu____7393  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7388  in
                  FStar_Pprint.op_Hat_Hat uu____7386 uu____7387  in
                FStar_Pprint.group uu____7385  in
              let uu____7394 =
                let uu____7395 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7395  in
              FStar_Pprint.op_Hat_Hat uu____7384 uu____7394  in
            FStar_Pprint.group uu____7383
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7396;_},e1::e2::e3::[])
            ->
            let uu____7403 =
              let uu____7404 =
                let uu____7405 =
                  let uu____7406 = p_atomicTermNotQUident e1  in
                  let uu____7407 =
                    let uu____7408 =
                      let uu____7409 =
                        let uu____7410 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7410  in
                      let uu____7413 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7409 uu____7413  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7408  in
                  FStar_Pprint.op_Hat_Hat uu____7406 uu____7407  in
                FStar_Pprint.group uu____7405  in
              let uu____7414 =
                let uu____7415 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7415  in
              FStar_Pprint.op_Hat_Hat uu____7404 uu____7414  in
            FStar_Pprint.group uu____7403
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7425 =
              let uu____7426 = str "requires"  in
              let uu____7428 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7426 uu____7428  in
            FStar_Pprint.group uu____7425
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7438 =
              let uu____7439 = str "ensures"  in
              let uu____7441 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7439 uu____7441  in
            FStar_Pprint.group uu____7438
        | FStar_Parser_AST.Attributes es ->
            let uu____7445 =
              let uu____7446 = str "attributes"  in
              let uu____7448 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7446 uu____7448  in
            FStar_Pprint.group uu____7445
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7453 =
                let uu____7454 =
                  let uu____7455 = str "if"  in
                  let uu____7457 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7455 uu____7457  in
                let uu____7460 =
                  let uu____7461 = str "then"  in
                  let uu____7463 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7461 uu____7463  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7454 uu____7460  in
              FStar_Pprint.group uu____7453
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7467,uu____7468,e31) when
                     is_unit e31 ->
                     let uu____7470 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7470
                 | uu____7473 -> p_noSeqTermAndComment false false e2  in
               let uu____7476 =
                 let uu____7477 =
                   let uu____7478 = str "if"  in
                   let uu____7480 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7478 uu____7480  in
                 let uu____7483 =
                   let uu____7484 =
                     let uu____7485 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7485 e2_doc  in
                   let uu____7487 =
                     let uu____7488 = str "else"  in
                     let uu____7490 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7488 uu____7490  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7484 uu____7487  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7477 uu____7483  in
               FStar_Pprint.group uu____7476)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7513 =
              let uu____7514 =
                let uu____7515 =
                  let uu____7516 = str "try"  in
                  let uu____7518 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7516 uu____7518  in
                let uu____7521 =
                  let uu____7522 = str "with"  in
                  let uu____7524 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7522 uu____7524  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7515 uu____7521  in
              FStar_Pprint.group uu____7514  in
            let uu____7533 = paren_if (ps || pb)  in uu____7533 uu____7513
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7560 =
              let uu____7561 =
                let uu____7562 =
                  let uu____7563 = str "match"  in
                  let uu____7565 = p_noSeqTermAndComment false false e1  in
                  let uu____7568 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7563 uu____7565 uu____7568
                   in
                let uu____7572 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7562 uu____7572  in
              FStar_Pprint.group uu____7561  in
            let uu____7581 = paren_if (ps || pb)  in uu____7581 uu____7560
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7588 =
              let uu____7589 =
                let uu____7590 =
                  let uu____7591 = str "let open"  in
                  let uu____7593 = p_quident uid  in
                  let uu____7594 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7591 uu____7593 uu____7594
                   in
                let uu____7598 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7590 uu____7598  in
              FStar_Pprint.group uu____7589  in
            let uu____7600 = paren_if ps  in uu____7600 uu____7588
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7665 is_last =
              match uu____7665 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7699 =
                          let uu____7700 = str "let"  in
                          let uu____7702 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7700 uu____7702
                           in
                        FStar_Pprint.group uu____7699
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7705 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7711 = p_term_sep false false e2  in
                  (match uu____7711 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7721 =
                         if is_last
                         then
                           let uu____7723 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7724 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7723 doc_expr1
                             uu____7724
                         else
                           (let uu____7730 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7730)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7721)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7781 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7781
                     else
                       (let uu____7786 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7786)) lbs
               in
            let lbs_doc =
              let uu____7790 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7790  in
            let uu____7791 =
              let uu____7792 =
                let uu____7793 =
                  let uu____7794 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7794
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7793  in
              FStar_Pprint.group uu____7792  in
            let uu____7796 = paren_if ps  in uu____7796 uu____7791
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7803;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7806;
                                                             FStar_Parser_AST.level
                                                               = uu____7807;_})
            when matches_var maybe_x x ->
            let uu____7834 =
              let uu____7835 =
                let uu____7836 = str "function"  in
                let uu____7838 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7836 uu____7838  in
              FStar_Pprint.group uu____7835  in
            let uu____7847 = paren_if (ps || pb)  in uu____7847 uu____7834
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7853 =
              let uu____7854 = str "quote"  in
              let uu____7856 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7854 uu____7856  in
            FStar_Pprint.group uu____7853
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7858 =
              let uu____7859 = str "`"  in
              let uu____7861 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7859 uu____7861  in
            FStar_Pprint.group uu____7858
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7863 =
              let uu____7864 = str "`%"  in
              let uu____7866 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7864 uu____7866  in
            FStar_Pprint.group uu____7863
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7868;
              FStar_Parser_AST.level = uu____7869;_}
            ->
            let uu____7870 =
              let uu____7871 = str "`@"  in
              let uu____7873 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7871 uu____7873  in
            FStar_Pprint.group uu____7870
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7875 =
              let uu____7876 = str "`#"  in
              let uu____7878 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7876 uu____7878  in
            FStar_Pprint.group uu____7875
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7887 = str "calc"  in
              let uu____7889 =
                let uu____7890 =
                  let uu____7891 = p_noSeqTermAndComment false false rel  in
                  let uu____7894 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7891 uu____7894  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7890  in
              FStar_Pprint.op_Hat_Hat uu____7887 uu____7889  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7896 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7897 =
              let uu____7898 =
                let uu____7899 =
                  let uu____7900 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7903 =
                    let uu____7904 = str ";"  in
                    let uu____7906 =
                      let uu____7907 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7907
                       in
                    FStar_Pprint.op_Hat_Hat uu____7904 uu____7906  in
                  FStar_Pprint.op_Hat_Hat uu____7900 uu____7903  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7899  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7898
               in
            FStar_Pprint.enclose head1 uu____7896 uu____7897
        | uu____7909 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7910  ->
    fun uu____7911  ->
      match uu____7911 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7916 =
            let uu____7917 = p_noSeqTermAndComment false false rel  in
            let uu____7920 =
              let uu____7921 =
                let uu____7922 =
                  let uu____7923 =
                    let uu____7924 = p_noSeqTermAndComment false false just
                       in
                    let uu____7927 =
                      let uu____7928 =
                        let uu____7929 =
                          let uu____7930 =
                            let uu____7931 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7934 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7931 uu____7934  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7930
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7929
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7928
                       in
                    FStar_Pprint.op_Hat_Hat uu____7924 uu____7927  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7923  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7922  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7921  in
            FStar_Pprint.op_Hat_Hat uu____7917 uu____7920  in
          FStar_Pprint.group uu____7916

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7936  ->
    match uu___11_7936 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7948 =
          let uu____7949 = str "[@"  in
          let uu____7951 =
            let uu____7952 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7953 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7952 uu____7953  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7949 uu____7951  in
        FStar_Pprint.group uu____7948

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document * FStar_Pprint.document))
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,(uu____7971,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8005 =
                   let uu____8006 =
                     let uu____8007 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8007 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8006 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8005 term_doc
             | pats ->
                 let uu____8015 =
                   let uu____8016 =
                     let uu____8017 =
                       let uu____8018 =
                         let uu____8019 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8019
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8018 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8022 = p_trigger trigger  in
                     prefix2 uu____8017 uu____8022  in
                   FStar_Pprint.group uu____8016  in
                 prefix2 uu____8015 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____8024,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8058 =
                   let uu____8059 =
                     let uu____8060 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8060 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8059 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8058 term_doc
             | pats ->
                 let uu____8068 =
                   let uu____8069 =
                     let uu____8070 =
                       let uu____8071 =
                         let uu____8072 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8072
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8071 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8075 = p_trigger trigger  in
                     prefix2 uu____8070 uu____8075  in
                   FStar_Pprint.group uu____8069  in
                 prefix2 uu____8068 term_doc)
        | uu____8076 -> p_simpleTerm ps pb e

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

and (p_typ_top' :
  annotation_style ->
    Prims.bool ->
      Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun ps  -> fun pb  -> fun e  -> p_tmArrow style true p_tmFormula e

and (sig_as_binders_if_possible :
  FStar_Parser_AST.term -> Prims.bool -> FStar_Pprint.document) =
  fun t  ->
    fun extra_space  ->
      let s = if extra_space then FStar_Pprint.space else FStar_Pprint.empty
         in
      let uu____8097 = all_binders_annot t  in
      if uu____8097
      then
        let uu____8100 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8100
      else
        (let uu____8111 =
           let uu____8112 =
             let uu____8113 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8113  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8112  in
         FStar_Pprint.group uu____8111)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8172 = x  in
      match uu____8172 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8237 = hd1  in
               (match uu____8237 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8309 = cb  in
      match uu____8309 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8328 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8334 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8334) hd1 tl1
                  in
               cat_with_colon uu____8328 typ)
       in
    let binders = FStar_List.fold_left fold_fun [] (FStar_List.rev pats)  in
    map_rev p_collapsed_binder binders

and (pats_as_binders_if_possible :
  FStar_Parser_AST.pattern Prims.list ->
    (FStar_Pprint.document Prims.list * annotation_style))
  =
  fun pats  ->
    let all_binders p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None ))
          ->
          (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
           | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
              ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                 FStar_Parser_AST.brange = uu____8413;
                 FStar_Parser_AST.blevel = uu____8414;
                 FStar_Parser_AST.aqual = uu____8415;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8424 =
                 let uu____8429 = p_ident lid  in
                 p_refinement' aqual uu____8429 t1 phi  in
               FStar_Pervasives_Native.Some uu____8424
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8436) ->
               let uu____8441 =
                 let uu____8446 =
                   let uu____8447 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8448 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8447 uu____8448  in
                 let uu____8449 = p_tmEqNoRefinement t  in
                 (uu____8446, uu____8449)  in
               FStar_Pervasives_Native.Some uu____8441
           | uu____8454 -> FStar_Pervasives_Native.None)
      | uu____8463 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8476 -> false
      | uu____8488 -> true  in
    let uu____8490 = map_if_all all_binders pats  in
    match uu____8490 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8522 = collapse_pats bs  in
        (uu____8522,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8539 = FStar_List.map p_atomicPattern pats  in
        (uu____8539,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8551 -> str "forall"
    | FStar_Parser_AST.QExists uu____8571 -> str "exists"
    | uu____8591 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8593  ->
    match uu___12_8593 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8605 =
          let uu____8606 =
            let uu____8607 =
              let uu____8608 = str "pattern"  in
              let uu____8610 =
                let uu____8611 =
                  let uu____8612 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8612
                   in
                FStar_Pprint.op_Hat_Hat uu____8611 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8608 uu____8610  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8607  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8606  in
        FStar_Pprint.group uu____8605

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8620 = str "\\/"  in
    FStar_Pprint.separate_map uu____8620 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8627 =
      let uu____8628 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8628 p_appTerm pats  in
    FStar_Pprint.group uu____8627

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8640 = p_term_sep false pb e1  in
            (match uu____8640 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8649 = str "fun"  in
                   let uu____8651 =
                     let uu____8652 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8652
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8649 uu____8651  in
                 let uu____8653 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8655 =
                       let uu____8656 =
                         let uu____8657 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8657  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8656
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8655
                   else
                     (let uu____8660 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8660)
                    in
                 let uu____8661 = paren_if ps  in uu____8661 uu____8653)
        | uu____8666 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8674  ->
      match uu____8674 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8698 =
                    let uu____8699 =
                      let uu____8700 =
                        let uu____8701 = p_tuplePattern p  in
                        let uu____8702 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8701 uu____8702  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8700
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8699  in
                  FStar_Pprint.group uu____8698
              | FStar_Pervasives_Native.Some f ->
                  let uu____8704 =
                    let uu____8705 =
                      let uu____8706 =
                        let uu____8707 =
                          let uu____8708 =
                            let uu____8709 = p_tuplePattern p  in
                            let uu____8710 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8709
                              uu____8710
                             in
                          FStar_Pprint.group uu____8708  in
                        let uu____8712 =
                          let uu____8713 =
                            let uu____8716 = p_tmFormula f  in
                            [uu____8716; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8713  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8707 uu____8712
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8706
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8705  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8704
               in
            let uu____8718 = p_term_sep false pb e  in
            match uu____8718 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8728 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8728
                   else
                     (let uu____8731 =
                        let uu____8732 =
                          let uu____8733 =
                            let uu____8734 =
                              let uu____8735 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8735  in
                            op_Hat_Slash_Plus_Hat branch uu____8734  in
                          FStar_Pprint.group uu____8733  in
                        let uu____8736 =
                          let uu____8737 =
                            let uu____8738 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8738  in
                          FStar_Pprint.op_Hat_Hat branch uu____8737  in
                        FStar_Pprint.ifflat uu____8732 uu____8736  in
                      FStar_Pprint.group uu____8731))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8742 =
                       let uu____8743 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8743  in
                     op_Hat_Slash_Plus_Hat branch uu____8742)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8754 =
                      let uu____8755 =
                        let uu____8756 =
                          let uu____8757 =
                            let uu____8758 =
                              let uu____8759 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8759  in
                            FStar_Pprint.separate_map uu____8758
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8757
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8756
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8755  in
                    FStar_Pprint.group uu____8754
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8761 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8763;_},e1::e2::[])
        ->
        let uu____8769 = str "<==>"  in
        let uu____8771 = p_tmImplies e1  in
        let uu____8772 = p_tmIff e2  in
        infix0 uu____8769 uu____8771 uu____8772
    | uu____8773 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8775;_},e1::e2::[])
        ->
        let uu____8781 = str "==>"  in
        let uu____8783 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8789 = p_tmImplies e2  in
        infix0 uu____8781 uu____8783 uu____8789
    | uu____8790 ->
        p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
          false p_tmFormula e

and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style  ->
    fun terms  ->
      fun no_last_op  ->
        fun flat_space  ->
          let uu____8804 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8804 with
          | (terms',last1) ->
              let uu____8824 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8859 =
                      let uu____8860 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8860
                       in
                    let uu____8861 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8859, uu____8861)
                | Binders (n1,ln,parens1) ->
                    let uu____8875 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8883 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8875, break1, uu____8883)
                 in
              (match uu____8824 with
               | (n1,last_n,terms'1,sep,last_op) ->
                   let last2 = FStar_List.hd last1  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > (Prims.parse_int "1")) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty  in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last2 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n1 FStar_Pprint.space  in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   (match FStar_List.length terms with
                    | _8916 when _8916 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____8917 ->
                        let uu____8918 =
                          let uu____8919 =
                            let uu____8920 =
                              let uu____8921 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8922 =
                                let uu____8923 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8923
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8921 uu____8922
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8920  in
                          let uu____8924 =
                            let uu____8925 =
                              let uu____8926 =
                                let uu____8927 =
                                  let uu____8928 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8928  in
                                let uu____8929 =
                                  let uu____8930 =
                                    let uu____8931 =
                                      let uu____8932 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8933 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8939 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8939)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8932
                                        uu____8933
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8931
                                     in
                                  jump2 uu____8930  in
                                FStar_Pprint.ifflat uu____8927 uu____8929  in
                              FStar_Pprint.group uu____8926  in
                            let uu____8941 =
                              let uu____8942 =
                                let uu____8943 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8943  in
                              FStar_Pprint.align uu____8942  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8925 uu____8941
                             in
                          FStar_Pprint.ifflat uu____8919 uu____8924  in
                        FStar_Pprint.group uu____8918))

and (p_tmArrow :
  annotation_style ->
    Prims.bool ->
      (FStar_Parser_AST.term -> FStar_Pprint.document) ->
        FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun style  ->
    fun flat_space  ->
      fun p_Tm  ->
        fun e  ->
          let terms =
            match style with
            | Arrows uu____8957 -> p_tmArrow' p_Tm e
            | Binders uu____8964 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8987 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8993 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8987 uu____8993
      | uu____8996 -> let uu____8997 = p_Tm e  in [uu____8997]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9050 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9076 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9050 uu____9076
        | uu____9099 ->
            let uu____9100 =
              let uu____9111 = p_Tm1 e1  in
              (uu____9111, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9100]
         in
      let fold_fun bs x =
        let uu____9209 = x  in
        match uu____9209 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9341 = hd1  in
                 (match uu____9341 with
                  | (b2s,t2,uu____9370) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9472 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9529 = cb  in
        match uu____9529 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9558 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9569 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9575 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9575) hd1 tl1
                         in
                      f uu____9569 typ))
         in
      let binders =
        let uu____9591 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9591  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9654 =
        let uu____9655 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9655 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9654  in
    let disj =
      let uu____9658 =
        let uu____9659 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9659 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9658  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9679;_},e1::e2::[])
        ->
        let uu____9685 = p_tmDisjunction e1  in
        let uu____9690 = let uu____9695 = p_tmConjunction e2  in [uu____9695]
           in
        FStar_List.append uu____9685 uu____9690
    | uu____9704 -> let uu____9705 = p_tmConjunction e  in [uu____9705]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9715;_},e1::e2::[])
        ->
        let uu____9721 = p_tmConjunction e1  in
        let uu____9724 = let uu____9727 = p_tmTuple e2  in [uu____9727]  in
        FStar_List.append uu____9721 uu____9724
    | uu____9728 -> let uu____9729 = p_tmTuple e  in [uu____9729]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9746 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9746
          (fun uu____9754  ->
             match uu____9754 with | (e1,uu____9760) -> p_tmEq e1) args
    | uu____9761 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9770 =
             let uu____9771 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9771  in
           FStar_Pprint.group uu____9770)

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
               (let uu____9790 = FStar_Ident.text_of_id op  in
                uu____9790 = "="))
              ||
              (let uu____9795 = FStar_Ident.text_of_id op  in
               uu____9795 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9801 = levels op1  in
            (match uu____9801 with
             | (left1,mine,right1) ->
                 let uu____9820 =
                   let uu____9821 = FStar_All.pipe_left str op1  in
                   let uu____9823 = p_tmEqWith' p_X left1 e1  in
                   let uu____9824 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9821 uu____9823 uu____9824  in
                 paren_if_gt curr mine uu____9820)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9825;_},e1::e2::[])
            ->
            let uu____9831 =
              let uu____9832 = p_tmEqWith p_X e1  in
              let uu____9833 =
                let uu____9834 =
                  let uu____9835 =
                    let uu____9836 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9836  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9835  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9834  in
              FStar_Pprint.op_Hat_Hat uu____9832 uu____9833  in
            FStar_Pprint.group uu____9831
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9837;_},e1::[])
            ->
            let uu____9842 = levels "-"  in
            (match uu____9842 with
             | (left1,mine,right1) ->
                 let uu____9862 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9862)
        | uu____9863 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9911)::(e2,uu____9913)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9933 = is_list e  in Prims.op_Negation uu____9933)
              ->
              let op = "::"  in
              let uu____9938 = levels op  in
              (match uu____9938 with
               | (left1,mine,right1) ->
                   let uu____9957 =
                     let uu____9958 = str op  in
                     let uu____9959 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9961 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9958 uu____9959 uu____9961  in
                   paren_if_gt curr mine uu____9957)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9980 = levels op  in
              (match uu____9980 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10014 = p_binder false b  in
                         let uu____10016 =
                           let uu____10017 =
                             let uu____10018 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10018 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10017
                            in
                         FStar_Pprint.op_Hat_Hat uu____10014 uu____10016
                     | FStar_Util.Inr t ->
                         let uu____10020 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10022 =
                           let uu____10023 =
                             let uu____10024 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10024 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10023
                            in
                         FStar_Pprint.op_Hat_Hat uu____10020 uu____10022
                      in
                   let uu____10025 =
                     let uu____10026 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10031 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10026 uu____10031  in
                   paren_if_gt curr mine uu____10025)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10033;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10063 = levels op  in
              (match uu____10063 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10083 = str op  in
                     let uu____10084 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10086 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10083 uu____10084 uu____10086
                   else
                     (let uu____10090 =
                        let uu____10091 = str op  in
                        let uu____10092 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10094 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10091 uu____10092 uu____10094  in
                      paren_if_gt curr mine uu____10090))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10103 = levels op1  in
              (match uu____10103 with
               | (left1,mine,right1) ->
                   let uu____10122 =
                     let uu____10123 = str op1  in
                     let uu____10124 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10126 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10123 uu____10124 uu____10126  in
                   paren_if_gt curr mine uu____10122)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10146 =
                let uu____10147 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10148 =
                  let uu____10149 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10149 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10147 uu____10148  in
              braces_with_nesting uu____10146
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10154;_},e1::[])
              ->
              let uu____10159 =
                let uu____10160 = str "~"  in
                let uu____10162 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10160 uu____10162  in
              FStar_Pprint.group uu____10159
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10164;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10173 = levels op  in
                   (match uu____10173 with
                    | (left1,mine,right1) ->
                        let uu____10192 =
                          let uu____10193 = str op  in
                          let uu____10194 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10196 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10193 uu____10194 uu____10196  in
                        paren_if_gt curr mine uu____10192)
               | uu____10198 -> p_X e)
          | uu____10199 -> p_X e

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
        let uu____10206 =
          let uu____10207 = p_lident lid  in
          let uu____10208 =
            let uu____10209 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10209  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10207 uu____10208  in
        FStar_Pprint.group uu____10206
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10212 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10214 = p_appTerm e  in
    let uu____10215 =
      let uu____10216 =
        let uu____10217 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10217 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10216  in
    FStar_Pprint.op_Hat_Hat uu____10214 uu____10215

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10223 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10223 t phi
      | FStar_Parser_AST.TAnnotated uu____10224 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10230 ->
          let uu____10231 =
            let uu____10233 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10233
             in
          failwith uu____10231
      | FStar_Parser_AST.TVariable uu____10236 ->
          let uu____10237 =
            let uu____10239 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10239
             in
          failwith uu____10237
      | FStar_Parser_AST.NoName uu____10242 ->
          let uu____10243 =
            let uu____10245 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10245
             in
          failwith uu____10243

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10249  ->
      match uu____10249 with
      | (lid,e) ->
          let uu____10257 =
            let uu____10258 = p_qlident lid  in
            let uu____10259 =
              let uu____10260 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10260
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10258 uu____10259  in
          FStar_Pprint.group uu____10257

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10263 when is_general_application e ->
        let uu____10270 = head_and_args e  in
        (match uu____10270 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10317 = p_argTerm e1  in
                  let uu____10318 =
                    let uu____10319 =
                      let uu____10320 =
                        let uu____10321 = str "`"  in
                        let uu____10323 =
                          let uu____10324 = p_indexingTerm head1  in
                          let uu____10325 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10324 uu____10325  in
                        FStar_Pprint.op_Hat_Hat uu____10321 uu____10323  in
                      FStar_Pprint.group uu____10320  in
                    let uu____10327 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10319 uu____10327  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10317 uu____10318
              | uu____10328 ->
                  let uu____10335 =
                    let uu____10346 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10346
                    then
                      let uu____10380 =
                        FStar_Util.take
                          (fun uu____10404  ->
                             match uu____10404 with
                             | (uu____10410,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10380 with
                      | (fs_typ_args,args1) ->
                          let uu____10448 =
                            let uu____10449 = p_indexingTerm head1  in
                            let uu____10450 =
                              let uu____10451 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10451
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10449 uu____10450
                             in
                          (uu____10448, args1)
                    else
                      (let uu____10466 = p_indexingTerm head1  in
                       (uu____10466, args))
                     in
                  (match uu____10335 with
                   | (head_doc,args1) ->
                       let uu____10487 =
                         let uu____10488 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10488 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10487)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10510 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10510)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10529 =
               let uu____10530 = p_quident lid  in
               let uu____10531 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10530 uu____10531  in
             FStar_Pprint.group uu____10529
         | hd1::tl1 ->
             let uu____10548 =
               let uu____10549 =
                 let uu____10550 =
                   let uu____10551 = p_quident lid  in
                   let uu____10552 = p_argTerm hd1  in
                   prefix2 uu____10551 uu____10552  in
                 FStar_Pprint.group uu____10550  in
               let uu____10553 =
                 let uu____10554 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10554  in
               FStar_Pprint.op_Hat_Hat uu____10549 uu____10553  in
             FStar_Pprint.group uu____10548)
    | uu____10559 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10570 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10570 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10574 = str "#"  in
        let uu____10576 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10574 uu____10576
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10579 = str "#["  in
        let uu____10581 =
          let uu____10582 = p_indexingTerm t  in
          let uu____10583 =
            let uu____10584 = str "]"  in
            let uu____10586 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10584 uu____10586  in
          FStar_Pprint.op_Hat_Hat uu____10582 uu____10583  in
        FStar_Pprint.op_Hat_Hat uu____10579 uu____10581
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10589  ->
    match uu____10589 with | (e,uu____10595) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10600;_},e1::e2::[])
          ->
          let uu____10606 =
            let uu____10607 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10608 =
              let uu____10609 =
                let uu____10610 = p_term false false e2  in
                soft_parens_with_nesting uu____10610  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10609  in
            FStar_Pprint.op_Hat_Hat uu____10607 uu____10608  in
          FStar_Pprint.group uu____10606
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10613;_},e1::e2::[])
          ->
          let uu____10619 =
            let uu____10620 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10621 =
              let uu____10622 =
                let uu____10623 = p_term false false e2  in
                soft_brackets_with_nesting uu____10623  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10622  in
            FStar_Pprint.op_Hat_Hat uu____10620 uu____10621  in
          FStar_Pprint.group uu____10619
      | uu____10626 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10631 = p_quident lid  in
        let uu____10632 =
          let uu____10633 =
            let uu____10634 = p_term false false e1  in
            soft_parens_with_nesting uu____10634  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10633  in
        FStar_Pprint.op_Hat_Hat uu____10631 uu____10632
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10642 =
          let uu____10643 = FStar_Ident.text_of_id op  in str uu____10643  in
        let uu____10645 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10642 uu____10645
    | uu____10646 -> p_atomicTermNotQUident e

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
         | uu____10659 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10668 =
          let uu____10669 = FStar_Ident.text_of_id op  in str uu____10669  in
        let uu____10671 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10668 uu____10671
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10675 =
          let uu____10676 =
            let uu____10677 =
              let uu____10678 = FStar_Ident.text_of_id op  in str uu____10678
               in
            let uu____10680 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10677 uu____10680  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10676  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10675
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10695 = all_explicit args  in
        if uu____10695
        then
          let uu____10698 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10699 =
            let uu____10700 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10701 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10700 p_tmEq uu____10701  in
          let uu____10708 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10698 uu____10699 uu____10708
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10730 =
                 let uu____10731 = p_quident lid  in
                 let uu____10732 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10731 uu____10732  in
               FStar_Pprint.group uu____10730
           | hd1::tl1 ->
               let uu____10749 =
                 let uu____10750 =
                   let uu____10751 =
                     let uu____10752 = p_quident lid  in
                     let uu____10753 = p_argTerm hd1  in
                     prefix2 uu____10752 uu____10753  in
                   FStar_Pprint.group uu____10751  in
                 let uu____10754 =
                   let uu____10755 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10755  in
                 FStar_Pprint.op_Hat_Hat uu____10750 uu____10754  in
               FStar_Pprint.group uu____10749)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10762 =
          let uu____10763 = p_atomicTermNotQUident e1  in
          let uu____10764 =
            let uu____10765 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10765  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10763 uu____10764
           in
        FStar_Pprint.group uu____10762
    | uu____10768 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10773 = p_quident constr_lid  in
        let uu____10774 =
          let uu____10775 =
            let uu____10776 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10776  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10775  in
        FStar_Pprint.op_Hat_Hat uu____10773 uu____10774
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10778 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10778 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10780 = p_term_sep false false e1  in
        (match uu____10780 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10793 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10793))
    | uu____10794 when is_array e ->
        let es = extract_from_list e  in
        let uu____10798 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10799 =
          let uu____10800 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10800
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10805 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10798 uu____10799 uu____10805
    | uu____10808 when is_list e ->
        let uu____10809 =
          let uu____10810 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10811 = extract_from_list e  in
          separate_map_or_flow_last uu____10810
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10811
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10809 FStar_Pprint.rbracket
    | uu____10820 when is_lex_list e ->
        let uu____10821 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10822 =
          let uu____10823 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10824 = extract_from_list e  in
          separate_map_or_flow_last uu____10823
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10824
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10821 uu____10822 FStar_Pprint.rbracket
    | uu____10833 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10837 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10838 =
          let uu____10839 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10839 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10837 uu____10838 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10849 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10852 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10849 uu____10852
    | FStar_Parser_AST.Op (op,args) when
        let uu____10861 = handleable_op op args  in
        Prims.op_Negation uu____10861 ->
        let uu____10863 =
          let uu____10865 =
            let uu____10867 = FStar_Ident.text_of_id op  in
            let uu____10869 =
              let uu____10871 =
                let uu____10873 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10873
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10871  in
            Prims.op_Hat uu____10867 uu____10869  in
          Prims.op_Hat "Operation " uu____10865  in
        failwith uu____10863
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10880 = p_term false false e  in
        soft_parens_with_nesting uu____10880
    | FStar_Parser_AST.Const uu____10883 ->
        let uu____10884 = p_term false false e  in
        soft_parens_with_nesting uu____10884
    | FStar_Parser_AST.Op uu____10887 ->
        let uu____10894 = p_term false false e  in
        soft_parens_with_nesting uu____10894
    | FStar_Parser_AST.Tvar uu____10897 ->
        let uu____10898 = p_term false false e  in
        soft_parens_with_nesting uu____10898
    | FStar_Parser_AST.Var uu____10901 ->
        let uu____10902 = p_term false false e  in
        soft_parens_with_nesting uu____10902
    | FStar_Parser_AST.Name uu____10905 ->
        let uu____10906 = p_term false false e  in
        soft_parens_with_nesting uu____10906
    | FStar_Parser_AST.Construct uu____10909 ->
        let uu____10920 = p_term false false e  in
        soft_parens_with_nesting uu____10920
    | FStar_Parser_AST.Abs uu____10923 ->
        let uu____10930 = p_term false false e  in
        soft_parens_with_nesting uu____10930
    | FStar_Parser_AST.App uu____10933 ->
        let uu____10940 = p_term false false e  in
        soft_parens_with_nesting uu____10940
    | FStar_Parser_AST.Let uu____10943 ->
        let uu____10964 = p_term false false e  in
        soft_parens_with_nesting uu____10964
    | FStar_Parser_AST.LetOpen uu____10967 ->
        let uu____10972 = p_term false false e  in
        soft_parens_with_nesting uu____10972
    | FStar_Parser_AST.Seq uu____10975 ->
        let uu____10980 = p_term false false e  in
        soft_parens_with_nesting uu____10980
    | FStar_Parser_AST.Bind uu____10983 ->
        let uu____10990 = p_term false false e  in
        soft_parens_with_nesting uu____10990
    | FStar_Parser_AST.If uu____10993 ->
        let uu____11000 = p_term false false e  in
        soft_parens_with_nesting uu____11000
    | FStar_Parser_AST.Match uu____11003 ->
        let uu____11018 = p_term false false e  in
        soft_parens_with_nesting uu____11018
    | FStar_Parser_AST.TryWith uu____11021 ->
        let uu____11036 = p_term false false e  in
        soft_parens_with_nesting uu____11036
    | FStar_Parser_AST.Ascribed uu____11039 ->
        let uu____11048 = p_term false false e  in
        soft_parens_with_nesting uu____11048
    | FStar_Parser_AST.Record uu____11051 ->
        let uu____11064 = p_term false false e  in
        soft_parens_with_nesting uu____11064
    | FStar_Parser_AST.Project uu____11067 ->
        let uu____11072 = p_term false false e  in
        soft_parens_with_nesting uu____11072
    | FStar_Parser_AST.Product uu____11075 ->
        let uu____11082 = p_term false false e  in
        soft_parens_with_nesting uu____11082
    | FStar_Parser_AST.Sum uu____11085 ->
        let uu____11096 = p_term false false e  in
        soft_parens_with_nesting uu____11096
    | FStar_Parser_AST.QForall uu____11099 ->
        let uu____11118 = p_term false false e  in
        soft_parens_with_nesting uu____11118
    | FStar_Parser_AST.QExists uu____11121 ->
        let uu____11140 = p_term false false e  in
        soft_parens_with_nesting uu____11140
    | FStar_Parser_AST.Refine uu____11143 ->
        let uu____11148 = p_term false false e  in
        soft_parens_with_nesting uu____11148
    | FStar_Parser_AST.NamedTyp uu____11151 ->
        let uu____11156 = p_term false false e  in
        soft_parens_with_nesting uu____11156
    | FStar_Parser_AST.Requires uu____11159 ->
        let uu____11167 = p_term false false e  in
        soft_parens_with_nesting uu____11167
    | FStar_Parser_AST.Ensures uu____11170 ->
        let uu____11178 = p_term false false e  in
        soft_parens_with_nesting uu____11178
    | FStar_Parser_AST.Attributes uu____11181 ->
        let uu____11184 = p_term false false e  in
        soft_parens_with_nesting uu____11184
    | FStar_Parser_AST.Quote uu____11187 ->
        let uu____11192 = p_term false false e  in
        soft_parens_with_nesting uu____11192
    | FStar_Parser_AST.VQuote uu____11195 ->
        let uu____11196 = p_term false false e  in
        soft_parens_with_nesting uu____11196
    | FStar_Parser_AST.Antiquote uu____11199 ->
        let uu____11200 = p_term false false e  in
        soft_parens_with_nesting uu____11200
    | FStar_Parser_AST.CalcProof uu____11203 ->
        let uu____11212 = p_term false false e  in
        soft_parens_with_nesting uu____11212

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11215  ->
    match uu___15_11215 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11227) ->
        let uu____11230 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11230
    | FStar_Const.Const_bytearray (bytes,uu____11232) ->
        let uu____11239 =
          let uu____11240 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11240  in
        let uu____11241 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11239 uu____11241
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_11264 =
          match uu___13_11264 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_11271 =
          match uu___14_11271 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11286  ->
               match uu____11286 with
               | (s,w) ->
                   let uu____11293 = signedness s  in
                   let uu____11294 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11293 uu____11294)
            sign_width_opt
           in
        let uu____11295 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11295 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11299 = FStar_Range.string_of_range r  in str uu____11299
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11303 = p_quident lid  in
        let uu____11304 =
          let uu____11305 =
            let uu____11306 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11306  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11305  in
        FStar_Pprint.op_Hat_Hat uu____11303 uu____11304

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11309 = str "u#"  in
    let uu____11311 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11309 uu____11311

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11313;_},u1::u2::[])
        ->
        let uu____11319 =
          let uu____11320 = p_universeFrom u1  in
          let uu____11321 =
            let uu____11322 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11322  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11320 uu____11321  in
        FStar_Pprint.group uu____11319
    | FStar_Parser_AST.App uu____11323 ->
        let uu____11330 = head_and_args u  in
        (match uu____11330 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11356 =
                    let uu____11357 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11358 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11366  ->
                           match uu____11366 with
                           | (u1,uu____11372) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11357 uu____11358  in
                  FStar_Pprint.group uu____11356
              | uu____11373 ->
                  let uu____11374 =
                    let uu____11376 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11376
                     in
                  failwith uu____11374))
    | uu____11379 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11405 = FStar_Ident.text_of_id id1  in str uu____11405
    | FStar_Parser_AST.Paren u1 ->
        let uu____11408 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11408
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11409;_},uu____11410::uu____11411::[])
        ->
        let uu____11415 = p_universeFrom u  in
        soft_parens_with_nesting uu____11415
    | FStar_Parser_AST.App uu____11416 ->
        let uu____11423 = p_universeFrom u  in
        soft_parens_with_nesting uu____11423
    | uu____11424 ->
        let uu____11425 =
          let uu____11427 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11427
           in
        failwith uu____11425

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
       | FStar_Parser_AST.Module (uu____11516,decls) ->
           let uu____11522 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11522
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11531,decls,uu____11533) ->
           let uu____11540 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11540
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11600  ->
         match uu____11600 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11622)) -> false
      | ([],uu____11626) -> false
      | uu____11630 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11640 -> true
         | uu____11642 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string * FStar_Range.range) Prims.list ->
      (FStar_Pprint.document * (Prims.string * FStar_Range.range) Prims.list))
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____11685,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11691,decls,uu____11693) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11745 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11758;
                 FStar_Parser_AST.doc = uu____11759;
                 FStar_Parser_AST.quals = uu____11760;
                 FStar_Parser_AST.attrs = uu____11761;_}::uu____11762 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11768 =
                   let uu____11771 =
                     let uu____11774 = FStar_List.tl ds  in d :: uu____11774
                      in
                   d0 :: uu____11771  in
                 (uu____11768, (d0.FStar_Parser_AST.drange))
             | uu____11779 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11745 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11836 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11836 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11945 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11945, comments1))))))
  