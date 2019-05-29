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
         (id1,uu____5066)) ->
          let uu____5069 =
            let uu____5071 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5071 FStar_Util.is_upper  in
          if uu____5069
          then
            let uu____5077 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5077 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5080 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5087 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5090 =
      let uu____5091 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5092 =
        let uu____5093 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5093  in
      FStar_Pprint.op_Hat_Hat uu____5091 uu____5092  in
    FStar_Pprint.op_Hat_Hat uu____5087 uu____5090

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5095 ->
        let uu____5096 =
          let uu____5097 = str "@ "  in
          let uu____5099 =
            let uu____5100 =
              let uu____5101 =
                let uu____5102 =
                  let uu____5103 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5103  in
                FStar_Pprint.op_Hat_Hat uu____5102 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5101  in
            FStar_Pprint.op_Hat_Hat uu____5100 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5097 uu____5099  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5096

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5106  ->
    match uu____5106 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5154 =
                match uu____5154 with
                | (kwd,arg) ->
                    let uu____5167 = str "@"  in
                    let uu____5169 =
                      let uu____5170 = str kwd  in
                      let uu____5171 =
                        let uu____5172 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5172
                         in
                      FStar_Pprint.op_Hat_Hat uu____5170 uu____5171  in
                    FStar_Pprint.op_Hat_Hat uu____5167 uu____5169
                 in
              let uu____5173 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5173 FStar_Pprint.hardline
           in
        let uu____5180 =
          let uu____5181 =
            let uu____5182 =
              let uu____5183 = str doc1  in
              let uu____5184 =
                let uu____5185 =
                  let uu____5186 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5186  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5185  in
              FStar_Pprint.op_Hat_Hat uu____5183 uu____5184  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5182  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5181  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5180

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5190 =
          let uu____5191 = str "val"  in
          let uu____5193 =
            let uu____5194 =
              let uu____5195 = p_lident lid  in
              let uu____5196 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5195 uu____5196  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5194  in
          FStar_Pprint.op_Hat_Hat uu____5191 uu____5193  in
        let uu____5197 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5190 uu____5197
    | FStar_Parser_AST.TopLevelLet (uu____5200,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5225 =
               let uu____5226 = str "let"  in p_letlhs uu____5226 lb false
                in
             FStar_Pprint.group uu____5225) lbs
    | uu____5229 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_5244 =
          match uu___4_5244 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5252 = f x  in
              let uu____5253 =
                let uu____5254 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5254  in
              FStar_Pprint.op_Hat_Hat uu____5252 uu____5253
           in
        let uu____5255 = str "["  in
        let uu____5257 =
          let uu____5258 = p_list' l  in
          let uu____5259 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5258 uu____5259  in
        FStar_Pprint.op_Hat_Hat uu____5255 uu____5257

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5263 =
          let uu____5264 = str "open"  in
          let uu____5266 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5266  in
        FStar_Pprint.group uu____5263
    | FStar_Parser_AST.Include uid ->
        let uu____5268 =
          let uu____5269 = str "include"  in
          let uu____5271 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5269 uu____5271  in
        FStar_Pprint.group uu____5268
    | FStar_Parser_AST.Friend uid ->
        let uu____5273 =
          let uu____5274 = str "friend"  in
          let uu____5276 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5274 uu____5276  in
        FStar_Pprint.group uu____5273
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5279 =
          let uu____5280 = str "module"  in
          let uu____5282 =
            let uu____5283 =
              let uu____5284 = p_uident uid1  in
              let uu____5285 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5284 uu____5285  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5283  in
          FStar_Pprint.op_Hat_Hat uu____5280 uu____5282  in
        let uu____5286 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5279 uu____5286
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5288 =
          let uu____5289 = str "module"  in
          let uu____5291 =
            let uu____5292 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5292  in
          FStar_Pprint.op_Hat_Hat uu____5289 uu____5291  in
        FStar_Pprint.group uu____5288
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5293,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5330 = str "effect"  in
          let uu____5332 =
            let uu____5333 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5333  in
          FStar_Pprint.op_Hat_Hat uu____5330 uu____5332  in
        let uu____5334 =
          let uu____5335 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5335 FStar_Pprint.equals
           in
        let uu____5338 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5334 uu____5338
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5369 =
          let uu____5370 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5370  in
        let uu____5383 =
          let uu____5384 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5422 =
                    let uu____5423 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5423 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5422)) uu____5384
           in
        FStar_Pprint.op_Hat_Hat uu____5369 uu____5383
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5440 = str "let"  in
          let uu____5442 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5440 uu____5442  in
        let uu____5443 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5443 p_letbinding lbs
          (fun uu____5453  ->
             match uu____5453 with
             | (p,t) ->
                 let uu____5460 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5460;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5466 =
          let uu____5467 = str "val"  in
          let uu____5469 =
            let uu____5470 =
              let uu____5471 = p_lident lid  in
              let uu____5472 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5471 uu____5472  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5470  in
          FStar_Pprint.op_Hat_Hat uu____5467 uu____5469  in
        FStar_All.pipe_left FStar_Pprint.group uu____5466
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5477 =
            let uu____5479 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5479 FStar_Util.is_upper  in
          if uu____5477
          then FStar_Pprint.empty
          else
            (let uu____5487 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5487 FStar_Pprint.space)
           in
        let uu____5489 =
          let uu____5490 = p_ident id1  in
          let uu____5491 =
            let uu____5492 =
              let uu____5493 =
                let uu____5494 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5494  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5493  in
            FStar_Pprint.group uu____5492  in
          FStar_Pprint.op_Hat_Hat uu____5490 uu____5491  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5489
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5503 = str "exception"  in
        let uu____5505 =
          let uu____5506 =
            let uu____5507 = p_uident uid  in
            let uu____5508 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5512 =
                     let uu____5513 = str "of"  in
                     let uu____5515 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5513 uu____5515  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5512) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5507 uu____5508  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5506  in
        FStar_Pprint.op_Hat_Hat uu____5503 uu____5505
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5519 = str "new_effect"  in
        let uu____5521 =
          let uu____5522 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5522  in
        FStar_Pprint.op_Hat_Hat uu____5519 uu____5521
    | FStar_Parser_AST.SubEffect se ->
        let uu____5524 = str "sub_effect"  in
        let uu____5526 =
          let uu____5527 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5527  in
        FStar_Pprint.op_Hat_Hat uu____5524 uu____5526
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5530 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5532,uu____5533) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5561 = str "%splice"  in
        let uu____5563 =
          let uu____5564 =
            let uu____5565 = str ";"  in p_list p_uident uu____5565 ids  in
          let uu____5567 =
            let uu____5568 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5568  in
          FStar_Pprint.op_Hat_Hat uu____5564 uu____5567  in
        FStar_Pprint.op_Hat_Hat uu____5561 uu____5563

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5571  ->
    match uu___5_5571 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5574 = str "#set-options"  in
        let uu____5576 =
          let uu____5577 =
            let uu____5578 = str s  in FStar_Pprint.dquotes uu____5578  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5577  in
        FStar_Pprint.op_Hat_Hat uu____5574 uu____5576
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5583 = str "#reset-options"  in
        let uu____5585 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5591 =
                 let uu____5592 = str s  in FStar_Pprint.dquotes uu____5592
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5591) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5583 uu____5585
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5597 = str "#push-options"  in
        let uu____5599 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5605 =
                 let uu____5606 = str s  in FStar_Pprint.dquotes uu____5606
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5605) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5597 uu____5599
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
    fun uu____5637  ->
      match uu____5637 with
      | (typedecl,fsdoc_opt) ->
          let uu____5650 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5650 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5675 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5675
               else
                 (let uu____5678 =
                    let uu____5679 =
                      let uu____5680 =
                        let uu____5681 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5681 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5680  in
                    let uu____5682 =
                      let uu____5683 =
                        let uu____5684 =
                          let uu____5685 =
                            let uu____5686 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5686  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5685
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5684
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5683  in
                    FStar_Pprint.ifflat uu____5679 uu____5682  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5678))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5689  ->
      match uu___6_5689 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5718 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5718, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5735 = p_typ_sep false false t  in
          (match uu____5735 with
           | (comm,doc1) ->
               let uu____5755 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5755, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5811 =
            match uu____5811 with
            | (lid1,t,doc_opt) ->
                let uu____5828 =
                  let uu____5833 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5833
                   in
                (match uu____5828 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5851 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5851  in
          let uu____5860 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5860, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5927 =
            match uu____5927 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5956 =
                    let uu____5957 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5957  in
                  FStar_Range.extend_to_end_of_line uu____5956  in
                let uu____5962 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5962 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6001 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6001, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6006  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6006 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6041 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6041  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6043 =
                        let uu____6046 =
                          let uu____6049 = p_fsdoc fsdoc  in
                          let uu____6050 =
                            let uu____6053 = cont lid_doc  in [uu____6053]
                             in
                          uu____6049 :: uu____6050  in
                        kw :: uu____6046  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6043
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6060 =
                        let uu____6061 =
                          let uu____6062 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6062 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6061
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6060
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6082 =
                          let uu____6083 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6083  in
                        prefix2 uu____6082 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6085  ->
      match uu____6085 with
      | (lid,t,doc_opt) ->
          let uu____6102 =
            let uu____6103 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6104 =
              let uu____6105 = p_lident lid  in
              let uu____6106 =
                let uu____6107 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6107  in
              FStar_Pprint.op_Hat_Hat uu____6105 uu____6106  in
            FStar_Pprint.op_Hat_Hat uu____6103 uu____6104  in
          FStar_Pprint.group uu____6102

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6109  ->
    match uu____6109 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6143 =
            let uu____6144 =
              let uu____6145 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6145  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6144  in
          FStar_Pprint.group uu____6143  in
        let uu____6146 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6147 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6151 =
                 let uu____6152 =
                   let uu____6153 =
                     let uu____6154 =
                       let uu____6155 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6155
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6154  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6153  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6152  in
               FStar_Pprint.group uu____6151) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6146 uu____6147

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6159  ->
      fun inner_let  ->
        match uu____6159 with
        | (pat,uu____6167) ->
            let uu____6168 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6220 =
                    let uu____6227 =
                      let uu____6232 =
                        let uu____6233 =
                          let uu____6234 =
                            let uu____6235 = str "by"  in
                            let uu____6237 =
                              let uu____6238 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6238
                               in
                            FStar_Pprint.op_Hat_Hat uu____6235 uu____6237  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6234
                           in
                        FStar_Pprint.group uu____6233  in
                      (t, uu____6232)  in
                    FStar_Pervasives_Native.Some uu____6227  in
                  (pat1, uu____6220)
              | uu____6249 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6168 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6275);
                         FStar_Parser_AST.prange = uu____6276;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6293 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6293 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6299 =
                        if inner_let
                        then
                          let uu____6313 = pats_as_binders_if_possible pats
                             in
                          match uu____6313 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6336 = pats_as_binders_if_possible pats
                              in
                           match uu____6336 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6299 with
                       | (terms,style) ->
                           let uu____6363 =
                             let uu____6364 =
                               let uu____6365 =
                                 let uu____6366 = p_lident lid  in
                                 let uu____6367 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6366
                                   uu____6367
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6365
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6364  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6363)
                  | uu____6370 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6378 =
                              let uu____6379 =
                                let uu____6380 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6380
                                 in
                              FStar_Pprint.group uu____6379  in
                            FStar_Pprint.op_Hat_Hat uu____6378 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6391 =
                        let uu____6392 =
                          let uu____6393 =
                            let uu____6394 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6394  in
                          FStar_Pprint.group uu____6393  in
                        FStar_Pprint.op_Hat_Hat uu____6392 ascr_doc  in
                      FStar_Pprint.group uu____6391))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6396  ->
      match uu____6396 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6405 = p_term_sep false false e  in
          (match uu____6405 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6415 =
                 let uu____6416 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6416  in
               let uu____6417 =
                 let uu____6418 =
                   let uu____6419 =
                     let uu____6420 =
                       let uu____6421 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6421
                        in
                     FStar_Pprint.group uu____6420  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6419  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6418  in
               FStar_Pprint.ifflat uu____6415 uu____6417)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_6422  ->
    match uu___7_6422 with
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
        let uu____6447 = p_uident uid  in
        let uu____6448 = p_binders true bs  in
        let uu____6450 =
          let uu____6451 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6451  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6447 uu____6448 uu____6450

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
          let uu____6466 =
            let uu____6467 =
              let uu____6468 =
                let uu____6469 = p_uident uid  in
                let uu____6470 = p_binders true bs  in
                let uu____6472 =
                  let uu____6473 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6473  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6469 uu____6470 uu____6472
                 in
              FStar_Pprint.group uu____6468  in
            let uu____6478 =
              let uu____6479 = str "with"  in
              let uu____6481 =
                let uu____6482 =
                  let uu____6483 =
                    let uu____6484 =
                      let uu____6485 =
                        let uu____6486 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6486
                         in
                      separate_map_last uu____6485 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6484  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6483  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6482  in
              FStar_Pprint.op_Hat_Hat uu____6479 uu____6481  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6467 uu____6478  in
          braces_with_nesting uu____6466

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6490,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6523 =
            let uu____6524 = p_lident lid  in
            let uu____6525 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6524 uu____6525  in
          let uu____6526 = p_simpleTerm ps false e  in
          prefix2 uu____6523 uu____6526
      | uu____6528 ->
          let uu____6529 =
            let uu____6531 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6531
             in
          failwith uu____6529

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6614 =
        match uu____6614 with
        | (kwd,t) ->
            let uu____6625 =
              let uu____6626 = str kwd  in
              let uu____6627 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6626 uu____6627  in
            let uu____6628 = p_simpleTerm ps false t  in
            prefix2 uu____6625 uu____6628
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6635 =
      let uu____6636 =
        let uu____6637 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6638 =
          let uu____6639 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6639  in
        FStar_Pprint.op_Hat_Hat uu____6637 uu____6638  in
      let uu____6641 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6636 uu____6641  in
    let uu____6642 =
      let uu____6643 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6643  in
    FStar_Pprint.op_Hat_Hat uu____6635 uu____6642

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6644  ->
    match uu___8_6644 with
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
        let uu____6664 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6664 FStar_Pprint.hardline
    | uu____6665 ->
        let uu____6666 =
          let uu____6667 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6667  in
        FStar_Pprint.op_Hat_Hat uu____6666 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6670  ->
    match uu___9_6670 with
    | FStar_Parser_AST.Rec  ->
        let uu____6671 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6671
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6673  ->
    match uu___10_6673 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6678,e) -> e
          | uu____6684 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6685 = str "#["  in
        let uu____6687 =
          let uu____6688 = p_term false false t1  in
          let uu____6691 =
            let uu____6692 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6692 break1  in
          FStar_Pprint.op_Hat_Hat uu____6688 uu____6691  in
        FStar_Pprint.op_Hat_Hat uu____6685 uu____6687

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6698 =
          let uu____6699 =
            let uu____6700 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6700  in
          FStar_Pprint.separate_map uu____6699 p_tuplePattern pats  in
        FStar_Pprint.group uu____6698
    | uu____6701 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6710 =
          let uu____6711 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6711 p_constructorPattern pats  in
        FStar_Pprint.group uu____6710
    | uu____6712 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6715;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6720 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6721 = p_constructorPattern hd1  in
        let uu____6722 = p_constructorPattern tl1  in
        infix0 uu____6720 uu____6721 uu____6722
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6724;_},pats)
        ->
        let uu____6730 = p_quident uid  in
        let uu____6731 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6730 uu____6731
    | uu____6732 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6748;
               FStar_Parser_AST.blevel = uu____6749;
               FStar_Parser_AST.aqual = uu____6750;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6759 =
               let uu____6760 = p_ident lid  in
               p_refinement aqual uu____6760 t1 phi  in
             soft_parens_with_nesting uu____6759
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6763;
               FStar_Parser_AST.blevel = uu____6764;
               FStar_Parser_AST.aqual = uu____6765;_},phi))
             ->
             let uu____6771 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6771
         | uu____6772 ->
             let uu____6777 =
               let uu____6778 = p_tuplePattern pat  in
               let uu____6779 =
                 let uu____6780 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6780
                  in
               FStar_Pprint.op_Hat_Hat uu____6778 uu____6779  in
             soft_parens_with_nesting uu____6777)
    | FStar_Parser_AST.PatList pats ->
        let uu____6784 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6784 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6803 =
          match uu____6803 with
          | (lid,pat) ->
              let uu____6810 = p_qlident lid  in
              let uu____6811 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6810 uu____6811
           in
        let uu____6812 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6812
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6824 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6825 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6826 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6824 uu____6825 uu____6826
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6837 =
          let uu____6838 =
            let uu____6839 =
              let uu____6840 = FStar_Ident.text_of_id op  in str uu____6840
               in
            let uu____6842 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6839 uu____6842  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6838  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6837
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6846 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6846 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6854 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6855 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6854 uu____6855
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6857 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6861;
           FStar_Parser_AST.prange = uu____6862;_},uu____6863)
        ->
        let uu____6868 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6868
    | FStar_Parser_AST.PatTuple (uu____6869,false ) ->
        let uu____6876 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6876
    | uu____6877 ->
        let uu____6878 =
          let uu____6880 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6880  in
        failwith uu____6878

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6885;_},uu____6886)
        -> true
    | uu____6893 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6899) -> true
    | uu____6901 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6908 = p_binder' is_atomic b  in
      match uu____6908 with
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
          let uu____6945 =
            let uu____6946 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6947 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6946 uu____6947  in
          (uu____6945, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6953 = p_lident lid  in
          (uu____6953, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6960 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6971;
                   FStar_Parser_AST.blevel = uu____6972;
                   FStar_Parser_AST.aqual = uu____6973;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6978 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6978 t1 phi
            | uu____6979 ->
                let t' =
                  let uu____6981 = is_typ_tuple t  in
                  if uu____6981
                  then
                    let uu____6984 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6984
                  else p_tmFormula t  in
                let uu____6987 =
                  let uu____6988 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6989 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6988 uu____6989  in
                (uu____6987, t')
             in
          (match uu____6960 with
           | (b',t') ->
               let catf =
                 let uu____7007 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7007
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7014 =
                         let uu____7015 =
                           let uu____7016 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7016
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7015
                          in
                       FStar_Pprint.group uu____7014
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7021 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7021)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7026 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7054;
                  FStar_Parser_AST.blevel = uu____7055;
                  FStar_Parser_AST.aqual = uu____7056;_},phi)
               ->
               let uu____7060 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7060 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7081 ->
               if is_atomic
               then
                 let uu____7093 = p_atomicTerm t  in
                 (uu____7093, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7100 = p_appTerm t  in
                  (uu____7100, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7111 = p_refinement' aqual_opt binder t phi  in
          match uu____7111 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7127 -> false
            | FStar_Parser_AST.App uu____7139 -> false
            | FStar_Parser_AST.Op uu____7147 -> false
            | uu____7155 -> true  in
          let uu____7157 = p_noSeqTerm false false phi  in
          match uu____7157 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7174 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7174)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7183 =
                let uu____7184 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7184 binder  in
              let uu____7185 =
                let uu____7186 = p_appTerm t  in
                let uu____7187 =
                  let uu____7188 =
                    let uu____7189 =
                      let uu____7190 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7191 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7190 uu____7191  in
                    FStar_Pprint.group uu____7189  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7188
                   in
                FStar_Pprint.op_Hat_Hat uu____7186 uu____7187  in
              (uu____7183, uu____7185)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7205 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7205

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7209 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7212 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7212)
       in
    if uu____7209
    then FStar_Pprint.underscore
    else (let uu____7217 = FStar_Ident.text_of_id lid  in str uu____7217)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7220 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7223 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7223)
       in
    if uu____7220
    then FStar_Pprint.underscore
    else (let uu____7228 = FStar_Ident.text_of_lid lid  in str uu____7228)

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
          let uu____7249 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7249
        else
          (let uu____7252 =
             let uu____7253 =
               let uu____7254 =
                 let uu____7255 =
                   let uu____7256 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7256  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7255  in
               FStar_Pprint.group uu____7254  in
             let uu____7257 =
               let uu____7258 =
                 let uu____7259 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7259  in
               FStar_Pprint.op_Hat_Hat comm uu____7258  in
             FStar_Pprint.ifflat uu____7253 uu____7257  in
           FStar_All.pipe_left FStar_Pprint.group uu____7252)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7267 = p_noSeqTerm true false e1  in
            (match uu____7267 with
             | (comm,t1) ->
                 let uu____7276 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7277 =
                   let uu____7278 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7278
                    in
                 FStar_Pprint.op_Hat_Hat uu____7276 uu____7277)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7282 =
              let uu____7283 =
                let uu____7284 =
                  let uu____7285 = p_lident x  in
                  let uu____7286 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7285 uu____7286  in
                let uu____7287 =
                  let uu____7288 = p_noSeqTermAndComment true false e1  in
                  let uu____7291 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7288 uu____7291  in
                op_Hat_Slash_Plus_Hat uu____7284 uu____7287  in
              FStar_Pprint.group uu____7283  in
            let uu____7292 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7282 uu____7292
        | uu____7293 ->
            let uu____7294 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7294

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
            let uu____7306 = p_noSeqTerm true false e1  in
            (match uu____7306 with
             | (comm,t1) ->
                 let uu____7319 =
                   let uu____7320 =
                     let uu____7321 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7321  in
                   let uu____7322 =
                     let uu____7323 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7323
                      in
                   FStar_Pprint.op_Hat_Hat uu____7320 uu____7322  in
                 (comm, uu____7319))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7327 =
              let uu____7328 =
                let uu____7329 =
                  let uu____7330 =
                    let uu____7331 = p_lident x  in
                    let uu____7332 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7331 uu____7332  in
                  let uu____7333 =
                    let uu____7334 = p_noSeqTermAndComment true false e1  in
                    let uu____7337 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7334 uu____7337  in
                  op_Hat_Slash_Plus_Hat uu____7330 uu____7333  in
                FStar_Pprint.group uu____7329  in
              let uu____7338 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7328 uu____7338  in
            (FStar_Pprint.empty, uu____7327)
        | uu____7339 -> p_noSeqTerm ps pb e

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
            let uu____7359 =
              let uu____7360 = p_tmIff e1  in
              let uu____7361 =
                let uu____7362 =
                  let uu____7363 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7363
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7362  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7360 uu____7361  in
            FStar_Pprint.group uu____7359
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7369 =
              let uu____7370 = p_tmIff e1  in
              let uu____7371 =
                let uu____7372 =
                  let uu____7373 =
                    let uu____7374 = p_typ false false t  in
                    let uu____7377 =
                      let uu____7378 = str "by"  in
                      let uu____7380 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7378 uu____7380  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7374 uu____7377  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7373
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7372  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7370 uu____7371  in
            FStar_Pprint.group uu____7369
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7381;_},e1::e2::e3::[])
            ->
            let uu____7388 =
              let uu____7389 =
                let uu____7390 =
                  let uu____7391 = p_atomicTermNotQUident e1  in
                  let uu____7392 =
                    let uu____7393 =
                      let uu____7394 =
                        let uu____7395 = p_term false false e2  in
                        soft_parens_with_nesting uu____7395  in
                      let uu____7398 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7394 uu____7398  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7393  in
                  FStar_Pprint.op_Hat_Hat uu____7391 uu____7392  in
                FStar_Pprint.group uu____7390  in
              let uu____7399 =
                let uu____7400 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7400  in
              FStar_Pprint.op_Hat_Hat uu____7389 uu____7399  in
            FStar_Pprint.group uu____7388
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7401;_},e1::e2::e3::[])
            ->
            let uu____7408 =
              let uu____7409 =
                let uu____7410 =
                  let uu____7411 = p_atomicTermNotQUident e1  in
                  let uu____7412 =
                    let uu____7413 =
                      let uu____7414 =
                        let uu____7415 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7415  in
                      let uu____7418 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7414 uu____7418  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7413  in
                  FStar_Pprint.op_Hat_Hat uu____7411 uu____7412  in
                FStar_Pprint.group uu____7410  in
              let uu____7419 =
                let uu____7420 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7420  in
              FStar_Pprint.op_Hat_Hat uu____7409 uu____7419  in
            FStar_Pprint.group uu____7408
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7430 =
              let uu____7431 = str "requires"  in
              let uu____7433 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7431 uu____7433  in
            FStar_Pprint.group uu____7430
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7443 =
              let uu____7444 = str "ensures"  in
              let uu____7446 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7444 uu____7446  in
            FStar_Pprint.group uu____7443
        | FStar_Parser_AST.Attributes es ->
            let uu____7450 =
              let uu____7451 = str "attributes"  in
              let uu____7453 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7451 uu____7453  in
            FStar_Pprint.group uu____7450
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7458 =
                let uu____7459 =
                  let uu____7460 = str "if"  in
                  let uu____7462 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7460 uu____7462  in
                let uu____7465 =
                  let uu____7466 = str "then"  in
                  let uu____7468 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7466 uu____7468  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7459 uu____7465  in
              FStar_Pprint.group uu____7458
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7472,uu____7473,e31) when
                     is_unit e31 ->
                     let uu____7475 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7475
                 | uu____7478 -> p_noSeqTermAndComment false false e2  in
               let uu____7481 =
                 let uu____7482 =
                   let uu____7483 = str "if"  in
                   let uu____7485 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7483 uu____7485  in
                 let uu____7488 =
                   let uu____7489 =
                     let uu____7490 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7490 e2_doc  in
                   let uu____7492 =
                     let uu____7493 = str "else"  in
                     let uu____7495 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7493 uu____7495  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7489 uu____7492  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7482 uu____7488  in
               FStar_Pprint.group uu____7481)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7518 =
              let uu____7519 =
                let uu____7520 =
                  let uu____7521 = str "try"  in
                  let uu____7523 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7521 uu____7523  in
                let uu____7526 =
                  let uu____7527 = str "with"  in
                  let uu____7529 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7527 uu____7529  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7520 uu____7526  in
              FStar_Pprint.group uu____7519  in
            let uu____7538 = paren_if (ps || pb)  in uu____7538 uu____7518
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7565 =
              let uu____7566 =
                let uu____7567 =
                  let uu____7568 = str "match"  in
                  let uu____7570 = p_noSeqTermAndComment false false e1  in
                  let uu____7573 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7568 uu____7570 uu____7573
                   in
                let uu____7577 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7567 uu____7577  in
              FStar_Pprint.group uu____7566  in
            let uu____7586 = paren_if (ps || pb)  in uu____7586 uu____7565
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7593 =
              let uu____7594 =
                let uu____7595 =
                  let uu____7596 = str "let open"  in
                  let uu____7598 = p_quident uid  in
                  let uu____7599 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7596 uu____7598 uu____7599
                   in
                let uu____7603 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7595 uu____7603  in
              FStar_Pprint.group uu____7594  in
            let uu____7605 = paren_if ps  in uu____7605 uu____7593
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7670 is_last =
              match uu____7670 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7704 =
                          let uu____7705 = str "let"  in
                          let uu____7707 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7705 uu____7707
                           in
                        FStar_Pprint.group uu____7704
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7710 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7716 = p_term_sep false false e2  in
                  (match uu____7716 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7726 =
                         if is_last
                         then
                           let uu____7728 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7729 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7728 doc_expr1
                             uu____7729
                         else
                           (let uu____7735 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7735)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7726)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7786 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7786
                     else
                       (let uu____7791 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7791)) lbs
               in
            let lbs_doc =
              let uu____7795 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7795  in
            let uu____7796 =
              let uu____7797 =
                let uu____7798 =
                  let uu____7799 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7799
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7798  in
              FStar_Pprint.group uu____7797  in
            let uu____7801 = paren_if ps  in uu____7801 uu____7796
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7808;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7811;
                                                             FStar_Parser_AST.level
                                                               = uu____7812;_})
            when matches_var maybe_x x ->
            let uu____7839 =
              let uu____7840 =
                let uu____7841 = str "function"  in
                let uu____7843 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7841 uu____7843  in
              FStar_Pprint.group uu____7840  in
            let uu____7852 = paren_if (ps || pb)  in uu____7852 uu____7839
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7858 =
              let uu____7859 = str "quote"  in
              let uu____7861 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7859 uu____7861  in
            FStar_Pprint.group uu____7858
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7863 =
              let uu____7864 = str "`"  in
              let uu____7866 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7864 uu____7866  in
            FStar_Pprint.group uu____7863
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7868 =
              let uu____7869 = str "`%"  in
              let uu____7871 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7869 uu____7871  in
            FStar_Pprint.group uu____7868
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7873;
              FStar_Parser_AST.level = uu____7874;_}
            ->
            let uu____7875 =
              let uu____7876 = str "`@"  in
              let uu____7878 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7876 uu____7878  in
            FStar_Pprint.group uu____7875
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7880 =
              let uu____7881 = str "`#"  in
              let uu____7883 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7881 uu____7883  in
            FStar_Pprint.group uu____7880
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7892 = str "calc"  in
              let uu____7894 =
                let uu____7895 =
                  let uu____7896 = p_noSeqTermAndComment false false rel  in
                  let uu____7899 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7896 uu____7899  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7895  in
              FStar_Pprint.op_Hat_Hat uu____7892 uu____7894  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7901 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7902 =
              let uu____7903 =
                let uu____7904 =
                  let uu____7905 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7908 =
                    let uu____7909 = str ";"  in
                    let uu____7911 =
                      let uu____7912 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7912
                       in
                    FStar_Pprint.op_Hat_Hat uu____7909 uu____7911  in
                  FStar_Pprint.op_Hat_Hat uu____7905 uu____7908  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7904  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7903
               in
            FStar_Pprint.enclose head1 uu____7901 uu____7902
        | uu____7914 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7915  ->
    fun uu____7916  ->
      match uu____7916 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7921 =
            let uu____7922 = p_noSeqTermAndComment false false rel  in
            let uu____7925 =
              let uu____7926 =
                let uu____7927 =
                  let uu____7928 =
                    let uu____7929 = p_noSeqTermAndComment false false just
                       in
                    let uu____7932 =
                      let uu____7933 =
                        let uu____7934 =
                          let uu____7935 =
                            let uu____7936 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7939 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7936 uu____7939  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7935
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7934
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7933
                       in
                    FStar_Pprint.op_Hat_Hat uu____7929 uu____7932  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7928  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7927  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7926  in
            FStar_Pprint.op_Hat_Hat uu____7922 uu____7925  in
          FStar_Pprint.group uu____7921

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7941  ->
    match uu___11_7941 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7953 =
          let uu____7954 = str "[@"  in
          let uu____7956 =
            let uu____7957 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7958 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7957 uu____7958  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7954 uu____7956  in
        FStar_Pprint.group uu____7953

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
        | FStar_Parser_AST.QForall (bs,nopattern,(uu____7977,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8013 =
                   let uu____8014 =
                     let uu____8015 =
                       let uu____8016 =
                         let uu____8017 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8017
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8016 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8020 = p_nopattern nopattern  in
                     prefix2_nonempty uu____8015 uu____8020  in
                   FStar_Pprint.group uu____8014  in
                 prefix2 uu____8013 term_doc
             | pats ->
                 let uu____8026 =
                   let uu____8027 =
                     let uu____8028 =
                       let uu____8029 =
                         let uu____8030 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8030
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8029 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8033 = p_trigger trigger  in
                     prefix2 uu____8028 uu____8033  in
                   FStar_Pprint.group uu____8027  in
                 prefix2 uu____8026 term_doc)
        | FStar_Parser_AST.QExists (bs,nopattern,(uu____8036,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8072 =
                   let uu____8073 =
                     let uu____8074 =
                       let uu____8075 =
                         let uu____8076 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8076
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8075 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8079 = p_nopattern nopattern  in
                     prefix2_nonempty uu____8074 uu____8079  in
                   FStar_Pprint.group uu____8073  in
                 prefix2 uu____8072 term_doc
             | pats ->
                 let uu____8085 =
                   let uu____8086 =
                     let uu____8087 =
                       let uu____8088 =
                         let uu____8089 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8089
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8088 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8092 = p_trigger trigger  in
                     prefix2 uu____8087 uu____8092  in
                   FStar_Pprint.group uu____8086  in
                 prefix2 uu____8085 term_doc)
        | uu____8093 -> p_simpleTerm ps pb e

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
      let uu____8114 = all_binders_annot t  in
      if uu____8114
      then
        let uu____8117 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8117
      else
        (let uu____8128 =
           let uu____8129 =
             let uu____8130 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8130  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8129  in
         FStar_Pprint.group uu____8128)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8189 = x  in
      match uu____8189 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8254 = hd1  in
               (match uu____8254 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8326 = cb  in
      match uu____8326 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8345 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8351 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8351) hd1 tl1
                  in
               cat_with_colon uu____8345 typ)
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
                 FStar_Parser_AST.brange = uu____8430;
                 FStar_Parser_AST.blevel = uu____8431;
                 FStar_Parser_AST.aqual = uu____8432;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8441 =
                 let uu____8446 = p_ident lid  in
                 p_refinement' aqual uu____8446 t1 phi  in
               FStar_Pervasives_Native.Some uu____8441
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8453) ->
               let uu____8458 =
                 let uu____8463 =
                   let uu____8464 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8465 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8464 uu____8465  in
                 let uu____8466 = p_tmEqNoRefinement t  in
                 (uu____8463, uu____8466)  in
               FStar_Pervasives_Native.Some uu____8458
           | uu____8471 -> FStar_Pervasives_Native.None)
      | uu____8480 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8493 -> false
      | uu____8505 -> true  in
    let uu____8507 = map_if_all all_binders pats  in
    match uu____8507 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8539 = collapse_pats bs  in
        (uu____8539,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8556 = FStar_List.map p_atomicPattern pats  in
        (uu____8556,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8568 -> str "forall"
    | FStar_Parser_AST.QExists uu____8591 -> str "exists"
    | uu____8614 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8616  ->
    match uu___12_8616 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8628 =
          let uu____8629 =
            let uu____8630 =
              let uu____8631 = str "pattern"  in
              let uu____8633 =
                let uu____8634 =
                  let uu____8635 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8635
                   in
                FStar_Pprint.op_Hat_Hat uu____8634 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8631 uu____8633  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8630  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8629  in
        FStar_Pprint.group uu____8628

and (p_nopattern : Prims.bool -> FStar_Pprint.document) =
  fun p  ->
    if p
    then
      let uu____8641 =
        let uu____8642 =
          let uu____8643 =
            let uu____8644 = str "nopattern"  in
            FStar_Pprint.op_Hat_Hat uu____8644 FStar_Pprint.rbrace  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8643  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8642  in
      FStar_Pprint.group uu____8641
    else FStar_Pprint.empty

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8653 = str "\\/"  in
    FStar_Pprint.separate_map uu____8653 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8660 =
      let uu____8661 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8661 p_appTerm pats  in
    FStar_Pprint.group uu____8660

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8673 = p_term_sep false pb e1  in
            (match uu____8673 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8682 = str "fun"  in
                   let uu____8684 =
                     let uu____8685 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8685
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8682 uu____8684  in
                 let uu____8686 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8688 =
                       let uu____8689 =
                         let uu____8690 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8690  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8689
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8688
                   else
                     (let uu____8693 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8693)
                    in
                 let uu____8694 = paren_if ps  in uu____8694 uu____8686)
        | uu____8699 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8707  ->
      match uu____8707 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8731 =
                    let uu____8732 =
                      let uu____8733 =
                        let uu____8734 = p_tuplePattern p  in
                        let uu____8735 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8734 uu____8735  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8733
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8732  in
                  FStar_Pprint.group uu____8731
              | FStar_Pervasives_Native.Some f ->
                  let uu____8737 =
                    let uu____8738 =
                      let uu____8739 =
                        let uu____8740 =
                          let uu____8741 =
                            let uu____8742 = p_tuplePattern p  in
                            let uu____8743 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8742
                              uu____8743
                             in
                          FStar_Pprint.group uu____8741  in
                        let uu____8745 =
                          let uu____8746 =
                            let uu____8749 = p_tmFormula f  in
                            [uu____8749; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8746  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8740 uu____8745
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8739
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8738  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8737
               in
            let uu____8751 = p_term_sep false pb e  in
            match uu____8751 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8761 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8761
                   else
                     (let uu____8764 =
                        let uu____8765 =
                          let uu____8766 =
                            let uu____8767 =
                              let uu____8768 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8768  in
                            op_Hat_Slash_Plus_Hat branch uu____8767  in
                          FStar_Pprint.group uu____8766  in
                        let uu____8769 =
                          let uu____8770 =
                            let uu____8771 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8771  in
                          FStar_Pprint.op_Hat_Hat branch uu____8770  in
                        FStar_Pprint.ifflat uu____8765 uu____8769  in
                      FStar_Pprint.group uu____8764))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8775 =
                       let uu____8776 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8776  in
                     op_Hat_Slash_Plus_Hat branch uu____8775)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8787 =
                      let uu____8788 =
                        let uu____8789 =
                          let uu____8790 =
                            let uu____8791 =
                              let uu____8792 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8792  in
                            FStar_Pprint.separate_map uu____8791
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8790
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8789
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8788  in
                    FStar_Pprint.group uu____8787
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8794 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8796;_},e1::e2::[])
        ->
        let uu____8802 = str "<==>"  in
        let uu____8804 = p_tmImplies e1  in
        let uu____8805 = p_tmIff e2  in
        infix0 uu____8802 uu____8804 uu____8805
    | uu____8806 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8808;_},e1::e2::[])
        ->
        let uu____8814 = str "==>"  in
        let uu____8816 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8822 = p_tmImplies e2  in
        infix0 uu____8814 uu____8816 uu____8822
    | uu____8823 ->
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
          let uu____8837 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8837 with
          | (terms',last1) ->
              let uu____8857 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8892 =
                      let uu____8893 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8893
                       in
                    let uu____8894 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8892, uu____8894)
                | Binders (n1,ln,parens1) ->
                    let uu____8908 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8916 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8908, break1, uu____8916)
                 in
              (match uu____8857 with
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
                    | _8949 when _8949 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____8950 ->
                        let uu____8951 =
                          let uu____8952 =
                            let uu____8953 =
                              let uu____8954 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8955 =
                                let uu____8956 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8956
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8954 uu____8955
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8953  in
                          let uu____8957 =
                            let uu____8958 =
                              let uu____8959 =
                                let uu____8960 =
                                  let uu____8961 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8961  in
                                let uu____8962 =
                                  let uu____8963 =
                                    let uu____8964 =
                                      let uu____8965 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8966 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8972 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8972)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8965
                                        uu____8966
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8964
                                     in
                                  jump2 uu____8963  in
                                FStar_Pprint.ifflat uu____8960 uu____8962  in
                              FStar_Pprint.group uu____8959  in
                            let uu____8974 =
                              let uu____8975 =
                                let uu____8976 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8976  in
                              FStar_Pprint.align uu____8975  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8958 uu____8974
                             in
                          FStar_Pprint.ifflat uu____8952 uu____8957  in
                        FStar_Pprint.group uu____8951))

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
            | Arrows uu____8990 -> p_tmArrow' p_Tm e
            | Binders uu____8997 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____9020 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9026 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____9020 uu____9026
      | uu____9029 -> let uu____9030 = p_Tm e  in [uu____9030]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9083 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9109 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9083 uu____9109
        | uu____9132 ->
            let uu____9133 =
              let uu____9144 = p_Tm1 e1  in
              (uu____9144, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9133]
         in
      let fold_fun bs x =
        let uu____9242 = x  in
        match uu____9242 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9374 = hd1  in
                 (match uu____9374 with
                  | (b2s,t2,uu____9403) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9505 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9562 = cb  in
        match uu____9562 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9591 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9602 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9608 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9608) hd1 tl1
                         in
                      f uu____9602 typ))
         in
      let binders =
        let uu____9624 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9624  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9687 =
        let uu____9688 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9688 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9687  in
    let disj =
      let uu____9691 =
        let uu____9692 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9692 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9691  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9712;_},e1::e2::[])
        ->
        let uu____9718 = p_tmDisjunction e1  in
        let uu____9723 = let uu____9728 = p_tmConjunction e2  in [uu____9728]
           in
        FStar_List.append uu____9718 uu____9723
    | uu____9737 -> let uu____9738 = p_tmConjunction e  in [uu____9738]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9748;_},e1::e2::[])
        ->
        let uu____9754 = p_tmConjunction e1  in
        let uu____9757 = let uu____9760 = p_tmTuple e2  in [uu____9760]  in
        FStar_List.append uu____9754 uu____9757
    | uu____9761 -> let uu____9762 = p_tmTuple e  in [uu____9762]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9779 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9779
          (fun uu____9787  ->
             match uu____9787 with | (e1,uu____9793) -> p_tmEq e1) args
    | uu____9794 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9803 =
             let uu____9804 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9804  in
           FStar_Pprint.group uu____9803)

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
               (let uu____9823 = FStar_Ident.text_of_id op  in
                uu____9823 = "="))
              ||
              (let uu____9828 = FStar_Ident.text_of_id op  in
               uu____9828 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9834 = levels op1  in
            (match uu____9834 with
             | (left1,mine,right1) ->
                 let uu____9853 =
                   let uu____9854 = FStar_All.pipe_left str op1  in
                   let uu____9856 = p_tmEqWith' p_X left1 e1  in
                   let uu____9857 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9854 uu____9856 uu____9857  in
                 paren_if_gt curr mine uu____9853)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9858;_},e1::e2::[])
            ->
            let uu____9864 =
              let uu____9865 = p_tmEqWith p_X e1  in
              let uu____9866 =
                let uu____9867 =
                  let uu____9868 =
                    let uu____9869 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9869  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9868  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9867  in
              FStar_Pprint.op_Hat_Hat uu____9865 uu____9866  in
            FStar_Pprint.group uu____9864
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9870;_},e1::[])
            ->
            let uu____9875 = levels "-"  in
            (match uu____9875 with
             | (left1,mine,right1) ->
                 let uu____9895 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9895)
        | uu____9896 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9944)::(e2,uu____9946)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9966 = is_list e  in Prims.op_Negation uu____9966)
              ->
              let op = "::"  in
              let uu____9971 = levels op  in
              (match uu____9971 with
               | (left1,mine,right1) ->
                   let uu____9990 =
                     let uu____9991 = str op  in
                     let uu____9992 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9994 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9991 uu____9992 uu____9994  in
                   paren_if_gt curr mine uu____9990)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____10013 = levels op  in
              (match uu____10013 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10047 = p_binder false b  in
                         let uu____10049 =
                           let uu____10050 =
                             let uu____10051 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10051 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10050
                            in
                         FStar_Pprint.op_Hat_Hat uu____10047 uu____10049
                     | FStar_Util.Inr t ->
                         let uu____10053 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10055 =
                           let uu____10056 =
                             let uu____10057 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10057 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10056
                            in
                         FStar_Pprint.op_Hat_Hat uu____10053 uu____10055
                      in
                   let uu____10058 =
                     let uu____10059 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10064 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10059 uu____10064  in
                   paren_if_gt curr mine uu____10058)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10066;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10096 = levels op  in
              (match uu____10096 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10116 = str op  in
                     let uu____10117 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10119 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10116 uu____10117 uu____10119
                   else
                     (let uu____10123 =
                        let uu____10124 = str op  in
                        let uu____10125 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10127 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10124 uu____10125 uu____10127  in
                      paren_if_gt curr mine uu____10123))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10136 = levels op1  in
              (match uu____10136 with
               | (left1,mine,right1) ->
                   let uu____10155 =
                     let uu____10156 = str op1  in
                     let uu____10157 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10159 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10156 uu____10157 uu____10159  in
                   paren_if_gt curr mine uu____10155)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10179 =
                let uu____10180 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10181 =
                  let uu____10182 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10182 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10180 uu____10181  in
              braces_with_nesting uu____10179
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10187;_},e1::[])
              ->
              let uu____10192 =
                let uu____10193 = str "~"  in
                let uu____10195 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10193 uu____10195  in
              FStar_Pprint.group uu____10192
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10197;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10206 = levels op  in
                   (match uu____10206 with
                    | (left1,mine,right1) ->
                        let uu____10225 =
                          let uu____10226 = str op  in
                          let uu____10227 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10229 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10226 uu____10227 uu____10229  in
                        paren_if_gt curr mine uu____10225)
               | uu____10231 -> p_X e)
          | uu____10232 -> p_X e

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
        let uu____10239 =
          let uu____10240 = p_lident lid  in
          let uu____10241 =
            let uu____10242 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10242  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10240 uu____10241  in
        FStar_Pprint.group uu____10239
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10245 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10247 = p_appTerm e  in
    let uu____10248 =
      let uu____10249 =
        let uu____10250 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10250 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10249  in
    FStar_Pprint.op_Hat_Hat uu____10247 uu____10248

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10256 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10256 t phi
      | FStar_Parser_AST.TAnnotated uu____10257 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10263 ->
          let uu____10264 =
            let uu____10266 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10266
             in
          failwith uu____10264
      | FStar_Parser_AST.TVariable uu____10269 ->
          let uu____10270 =
            let uu____10272 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10272
             in
          failwith uu____10270
      | FStar_Parser_AST.NoName uu____10275 ->
          let uu____10276 =
            let uu____10278 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10278
             in
          failwith uu____10276

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10282  ->
      match uu____10282 with
      | (lid,e) ->
          let uu____10290 =
            let uu____10291 = p_qlident lid  in
            let uu____10292 =
              let uu____10293 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10293
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10291 uu____10292  in
          FStar_Pprint.group uu____10290

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10296 when is_general_application e ->
        let uu____10303 = head_and_args e  in
        (match uu____10303 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10350 = p_argTerm e1  in
                  let uu____10351 =
                    let uu____10352 =
                      let uu____10353 =
                        let uu____10354 = str "`"  in
                        let uu____10356 =
                          let uu____10357 = p_indexingTerm head1  in
                          let uu____10358 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10357 uu____10358  in
                        FStar_Pprint.op_Hat_Hat uu____10354 uu____10356  in
                      FStar_Pprint.group uu____10353  in
                    let uu____10360 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10352 uu____10360  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10350 uu____10351
              | uu____10361 ->
                  let uu____10368 =
                    let uu____10379 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10379
                    then
                      let uu____10413 =
                        FStar_Util.take
                          (fun uu____10437  ->
                             match uu____10437 with
                             | (uu____10443,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10413 with
                      | (fs_typ_args,args1) ->
                          let uu____10481 =
                            let uu____10482 = p_indexingTerm head1  in
                            let uu____10483 =
                              let uu____10484 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10484
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10482 uu____10483
                             in
                          (uu____10481, args1)
                    else
                      (let uu____10499 = p_indexingTerm head1  in
                       (uu____10499, args))
                     in
                  (match uu____10368 with
                   | (head_doc,args1) ->
                       let uu____10520 =
                         let uu____10521 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10521 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10520)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10543 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10543)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10562 =
               let uu____10563 = p_quident lid  in
               let uu____10564 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10563 uu____10564  in
             FStar_Pprint.group uu____10562
         | hd1::tl1 ->
             let uu____10581 =
               let uu____10582 =
                 let uu____10583 =
                   let uu____10584 = p_quident lid  in
                   let uu____10585 = p_argTerm hd1  in
                   prefix2 uu____10584 uu____10585  in
                 FStar_Pprint.group uu____10583  in
               let uu____10586 =
                 let uu____10587 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10587  in
               FStar_Pprint.op_Hat_Hat uu____10582 uu____10586  in
             FStar_Pprint.group uu____10581)
    | uu____10592 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10603 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10603 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10607 = str "#"  in
        let uu____10609 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10607 uu____10609
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10612 = str "#["  in
        let uu____10614 =
          let uu____10615 = p_indexingTerm t  in
          let uu____10616 =
            let uu____10617 = str "]"  in
            let uu____10619 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10617 uu____10619  in
          FStar_Pprint.op_Hat_Hat uu____10615 uu____10616  in
        FStar_Pprint.op_Hat_Hat uu____10612 uu____10614
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10622  ->
    match uu____10622 with | (e,uu____10628) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10633;_},e1::e2::[])
          ->
          let uu____10639 =
            let uu____10640 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10641 =
              let uu____10642 =
                let uu____10643 = p_term false false e2  in
                soft_parens_with_nesting uu____10643  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10642  in
            FStar_Pprint.op_Hat_Hat uu____10640 uu____10641  in
          FStar_Pprint.group uu____10639
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10646;_},e1::e2::[])
          ->
          let uu____10652 =
            let uu____10653 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10654 =
              let uu____10655 =
                let uu____10656 = p_term false false e2  in
                soft_brackets_with_nesting uu____10656  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10655  in
            FStar_Pprint.op_Hat_Hat uu____10653 uu____10654  in
          FStar_Pprint.group uu____10652
      | uu____10659 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10664 = p_quident lid  in
        let uu____10665 =
          let uu____10666 =
            let uu____10667 = p_term false false e1  in
            soft_parens_with_nesting uu____10667  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10666  in
        FStar_Pprint.op_Hat_Hat uu____10664 uu____10665
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10675 =
          let uu____10676 = FStar_Ident.text_of_id op  in str uu____10676  in
        let uu____10678 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10675 uu____10678
    | uu____10679 -> p_atomicTermNotQUident e

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
         | uu____10692 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10701 =
          let uu____10702 = FStar_Ident.text_of_id op  in str uu____10702  in
        let uu____10704 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10701 uu____10704
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10708 =
          let uu____10709 =
            let uu____10710 =
              let uu____10711 = FStar_Ident.text_of_id op  in str uu____10711
               in
            let uu____10713 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10710 uu____10713  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10709  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10708
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10728 = all_explicit args  in
        if uu____10728
        then
          let uu____10731 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10732 =
            let uu____10733 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10734 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10733 p_tmEq uu____10734  in
          let uu____10741 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10731 uu____10732 uu____10741
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10763 =
                 let uu____10764 = p_quident lid  in
                 let uu____10765 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10764 uu____10765  in
               FStar_Pprint.group uu____10763
           | hd1::tl1 ->
               let uu____10782 =
                 let uu____10783 =
                   let uu____10784 =
                     let uu____10785 = p_quident lid  in
                     let uu____10786 = p_argTerm hd1  in
                     prefix2 uu____10785 uu____10786  in
                   FStar_Pprint.group uu____10784  in
                 let uu____10787 =
                   let uu____10788 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10788  in
                 FStar_Pprint.op_Hat_Hat uu____10783 uu____10787  in
               FStar_Pprint.group uu____10782)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10795 =
          let uu____10796 = p_atomicTermNotQUident e1  in
          let uu____10797 =
            let uu____10798 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10798  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10796 uu____10797
           in
        FStar_Pprint.group uu____10795
    | uu____10801 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10806 = p_quident constr_lid  in
        let uu____10807 =
          let uu____10808 =
            let uu____10809 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10809  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10808  in
        FStar_Pprint.op_Hat_Hat uu____10806 uu____10807
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10811 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10811 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10813 = p_term_sep false false e1  in
        (match uu____10813 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10826 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10826))
    | uu____10827 when is_array e ->
        let es = extract_from_list e  in
        let uu____10831 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10832 =
          let uu____10833 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10833
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10838 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10831 uu____10832 uu____10838
    | uu____10841 when is_list e ->
        let uu____10842 =
          let uu____10843 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10844 = extract_from_list e  in
          separate_map_or_flow_last uu____10843
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10844
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10842 FStar_Pprint.rbracket
    | uu____10853 when is_lex_list e ->
        let uu____10854 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10855 =
          let uu____10856 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10857 = extract_from_list e  in
          separate_map_or_flow_last uu____10856
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10857
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10854 uu____10855 FStar_Pprint.rbracket
    | uu____10866 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10870 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10871 =
          let uu____10872 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10872 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10870 uu____10871 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10882 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10885 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10882 uu____10885
    | FStar_Parser_AST.Op (op,args) when
        let uu____10894 = handleable_op op args  in
        Prims.op_Negation uu____10894 ->
        let uu____10896 =
          let uu____10898 =
            let uu____10900 = FStar_Ident.text_of_id op  in
            let uu____10902 =
              let uu____10904 =
                let uu____10906 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10906
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10904  in
            Prims.op_Hat uu____10900 uu____10902  in
          Prims.op_Hat "Operation " uu____10898  in
        failwith uu____10896
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10913 = p_term false false e  in
        soft_parens_with_nesting uu____10913
    | FStar_Parser_AST.Const uu____10916 ->
        let uu____10917 = p_term false false e  in
        soft_parens_with_nesting uu____10917
    | FStar_Parser_AST.Op uu____10920 ->
        let uu____10927 = p_term false false e  in
        soft_parens_with_nesting uu____10927
    | FStar_Parser_AST.Tvar uu____10930 ->
        let uu____10931 = p_term false false e  in
        soft_parens_with_nesting uu____10931
    | FStar_Parser_AST.Var uu____10934 ->
        let uu____10935 = p_term false false e  in
        soft_parens_with_nesting uu____10935
    | FStar_Parser_AST.Name uu____10938 ->
        let uu____10939 = p_term false false e  in
        soft_parens_with_nesting uu____10939
    | FStar_Parser_AST.Construct uu____10942 ->
        let uu____10953 = p_term false false e  in
        soft_parens_with_nesting uu____10953
    | FStar_Parser_AST.Abs uu____10956 ->
        let uu____10963 = p_term false false e  in
        soft_parens_with_nesting uu____10963
    | FStar_Parser_AST.App uu____10966 ->
        let uu____10973 = p_term false false e  in
        soft_parens_with_nesting uu____10973
    | FStar_Parser_AST.Let uu____10976 ->
        let uu____10997 = p_term false false e  in
        soft_parens_with_nesting uu____10997
    | FStar_Parser_AST.LetOpen uu____11000 ->
        let uu____11005 = p_term false false e  in
        soft_parens_with_nesting uu____11005
    | FStar_Parser_AST.Seq uu____11008 ->
        let uu____11013 = p_term false false e  in
        soft_parens_with_nesting uu____11013
    | FStar_Parser_AST.Bind uu____11016 ->
        let uu____11023 = p_term false false e  in
        soft_parens_with_nesting uu____11023
    | FStar_Parser_AST.If uu____11026 ->
        let uu____11033 = p_term false false e  in
        soft_parens_with_nesting uu____11033
    | FStar_Parser_AST.Match uu____11036 ->
        let uu____11051 = p_term false false e  in
        soft_parens_with_nesting uu____11051
    | FStar_Parser_AST.TryWith uu____11054 ->
        let uu____11069 = p_term false false e  in
        soft_parens_with_nesting uu____11069
    | FStar_Parser_AST.Ascribed uu____11072 ->
        let uu____11081 = p_term false false e  in
        soft_parens_with_nesting uu____11081
    | FStar_Parser_AST.Record uu____11084 ->
        let uu____11097 = p_term false false e  in
        soft_parens_with_nesting uu____11097
    | FStar_Parser_AST.Project uu____11100 ->
        let uu____11105 = p_term false false e  in
        soft_parens_with_nesting uu____11105
    | FStar_Parser_AST.Product uu____11108 ->
        let uu____11115 = p_term false false e  in
        soft_parens_with_nesting uu____11115
    | FStar_Parser_AST.Sum uu____11118 ->
        let uu____11129 = p_term false false e  in
        soft_parens_with_nesting uu____11129
    | FStar_Parser_AST.QForall uu____11132 ->
        let uu____11154 = p_term false false e  in
        soft_parens_with_nesting uu____11154
    | FStar_Parser_AST.QExists uu____11157 ->
        let uu____11179 = p_term false false e  in
        soft_parens_with_nesting uu____11179
    | FStar_Parser_AST.Refine uu____11182 ->
        let uu____11187 = p_term false false e  in
        soft_parens_with_nesting uu____11187
    | FStar_Parser_AST.NamedTyp uu____11190 ->
        let uu____11195 = p_term false false e  in
        soft_parens_with_nesting uu____11195
    | FStar_Parser_AST.Requires uu____11198 ->
        let uu____11206 = p_term false false e  in
        soft_parens_with_nesting uu____11206
    | FStar_Parser_AST.Ensures uu____11209 ->
        let uu____11217 = p_term false false e  in
        soft_parens_with_nesting uu____11217
    | FStar_Parser_AST.Attributes uu____11220 ->
        let uu____11223 = p_term false false e  in
        soft_parens_with_nesting uu____11223
    | FStar_Parser_AST.Quote uu____11226 ->
        let uu____11231 = p_term false false e  in
        soft_parens_with_nesting uu____11231
    | FStar_Parser_AST.VQuote uu____11234 ->
        let uu____11235 = p_term false false e  in
        soft_parens_with_nesting uu____11235
    | FStar_Parser_AST.Antiquote uu____11238 ->
        let uu____11239 = p_term false false e  in
        soft_parens_with_nesting uu____11239
    | FStar_Parser_AST.CalcProof uu____11242 ->
        let uu____11251 = p_term false false e  in
        soft_parens_with_nesting uu____11251

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11254  ->
    match uu___15_11254 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11266) ->
        let uu____11269 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11269
    | FStar_Const.Const_bytearray (bytes,uu____11271) ->
        let uu____11276 =
          let uu____11277 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11277  in
        let uu____11278 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11276 uu____11278
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_11301 =
          match uu___13_11301 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_11308 =
          match uu___14_11308 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11323  ->
               match uu____11323 with
               | (s,w) ->
                   let uu____11330 = signedness s  in
                   let uu____11331 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11330 uu____11331)
            sign_width_opt
           in
        let uu____11332 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11332 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11336 = FStar_Range.string_of_range r  in str uu____11336
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11340 = p_quident lid  in
        let uu____11341 =
          let uu____11342 =
            let uu____11343 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11343  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11342  in
        FStar_Pprint.op_Hat_Hat uu____11340 uu____11341

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11346 = str "u#"  in
    let uu____11348 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11346 uu____11348

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11350;_},u1::u2::[])
        ->
        let uu____11356 =
          let uu____11357 = p_universeFrom u1  in
          let uu____11358 =
            let uu____11359 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11359  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11357 uu____11358  in
        FStar_Pprint.group uu____11356
    | FStar_Parser_AST.App uu____11360 ->
        let uu____11367 = head_and_args u  in
        (match uu____11367 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11393 =
                    let uu____11394 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11395 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11403  ->
                           match uu____11403 with
                           | (u1,uu____11409) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11394 uu____11395  in
                  FStar_Pprint.group uu____11393
              | uu____11410 ->
                  let uu____11411 =
                    let uu____11413 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11413
                     in
                  failwith uu____11411))
    | uu____11416 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11442 = FStar_Ident.text_of_id id1  in str uu____11442
    | FStar_Parser_AST.Paren u1 ->
        let uu____11445 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11445
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11446;_},uu____11447::uu____11448::[])
        ->
        let uu____11452 = p_universeFrom u  in
        soft_parens_with_nesting uu____11452
    | FStar_Parser_AST.App uu____11453 ->
        let uu____11460 = p_universeFrom u  in
        soft_parens_with_nesting uu____11460
    | uu____11461 ->
        let uu____11462 =
          let uu____11464 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11464
           in
        failwith uu____11462

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
       | FStar_Parser_AST.Module (uu____11553,decls) ->
           let uu____11559 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11559
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11568,decls,uu____11570) ->
           let uu____11577 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11577
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11637  ->
         match uu____11637 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11659)) -> false
      | ([],uu____11663) -> false
      | uu____11667 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11677 -> true
         | uu____11679 -> false)
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
        | FStar_Parser_AST.Module (uu____11722,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11728,decls,uu____11730) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11782 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11795;
                 FStar_Parser_AST.doc = uu____11796;
                 FStar_Parser_AST.quals = uu____11797;
                 FStar_Parser_AST.attrs = uu____11798;_}::uu____11799 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11805 =
                   let uu____11808 =
                     let uu____11811 = FStar_List.tl ds  in d :: uu____11811
                      in
                   d0 :: uu____11808  in
                 (uu____11805, (d0.FStar_Parser_AST.drange))
             | uu____11816 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11782 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11873 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11873 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11982 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11982, comments1))))))
  