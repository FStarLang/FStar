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
      FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_one prefix_ body
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
let (op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let (jump2 : FStar_Pprint.document -> FStar_Pprint.document) =
  fun body  -> FStar_Pprint.jump (Prims.of_int (2)) Prims.int_one body 
let (infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix (Prims.of_int (2)) Prims.int_one 
let (infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document)
  = FStar_Pprint.infix Prims.int_zero Prims.int_one 
let (break1 : FStar_Pprint.document) = FStar_Pprint.break_ Prims.int_one 
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
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (soft_parens_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let (braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_zero
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let (brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun contents  ->
    FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let (soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    let uu____701 = str "begin"  in
    let uu____703 = str "end"  in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____701
      contents uu____703
  
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
            (fun i  -> fun e  -> f (i <> (l - Prims.int_one)) e) es
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
        if (FStar_List.length l) < (Prims.of_int (10))
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
            (fun i  -> fun e  -> f (i <> (l - Prims.int_one)) e) es
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
        if (FStar_List.length l) < (Prims.of_int (10))
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
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
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
      FStar_Util.char_at uu____1523 Prims.int_zero  in
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
          let uu____1719 = FStar_String.get s Prims.int_zero  in
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
    | Left  -> (l, l, (l - Prims.int_one))
    | Right  -> ((l - Prims.int_one), l, l)
    | NonAssoc  -> ((l - Prims.int_one), l, (l - Prims.int_one))  in
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
    FStar_List.fold_left find_level_and_max Prims.int_zero l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2434 = assign_levels level_associativity_spec op  in
    match uu____2434 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - Prims.int_one), mine, right1)
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
    then Prims.int_one
    else
      (let uu____2681 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2681
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
  
let handleable_op :
  'Auu____2727 . FStar_Ident.ident -> 'Auu____2727 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2743 when _2743 = Prims.int_zero -> true
      | _2745 when _2745 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2747 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2747 ["-"; "~"])
      | _2755 when _2755 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2757 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2757
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2779 when _2779 = (Prims.of_int (3)) ->
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
          else (false, Prims.int_zero)
      | uu____2982 -> (true, (l + Prims.int_one))  in
    let uu____2987 = all_binders e Prims.int_zero  in
    match uu____2987 with
    | (b,l) -> if b && (l > Prims.int_one) then true else false
  
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
                      let lnum1 = min (Prims.of_int (2)) lnum  in
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
                      place_comments_until_pos Prims.int_one uu____3728 pos
                        meta_decl doc2 true init1))
                | uu____3733 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3746 = FStar_Range.line_of_pos pos  in
                         uu____3746 - lbegin  in
                       let lnum1 = min (Prims.of_int (3)) lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - Prims.int_one
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.of_int (2))
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.of_int (2)) lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then Prims.int_one
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.of_int (2)) else lnum6  in
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
                    place_comments_until_pos Prims.int_one last_line
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
                    place_comments_until_pos Prims.int_one last_line
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
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
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
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
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
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
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
    | FStar_Parser_AST.RestartSolver  -> str "#restart-solver"
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
    fun uu____5633  ->
      match uu____5633 with
      | (typedecl,fsdoc_opt) ->
          let uu____5646 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5646 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5671 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5671
               else
                 (let uu____5674 =
                    let uu____5675 =
                      let uu____5676 =
                        let uu____5677 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5677 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5676  in
                    let uu____5678 =
                      let uu____5679 =
                        let uu____5680 =
                          let uu____5681 =
                            let uu____5682 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5682  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5681
                           in
                        FStar_Pprint.nest (Prims.of_int (2)) uu____5680  in
                      FStar_Pprint.op_Hat_Hat decl uu____5679  in
                    FStar_Pprint.ifflat uu____5675 uu____5678  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5674))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5685  ->
      match uu___6_5685 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5714 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5714, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5731 = p_typ_sep false false t  in
          (match uu____5731 with
           | (comm,doc1) ->
               let uu____5751 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5751, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5807 =
            match uu____5807 with
            | (lid1,t,doc_opt) ->
                let uu____5824 =
                  let uu____5829 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5829
                   in
                (match uu____5824 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5847 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5847  in
          let uu____5856 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5856, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5923 =
            match uu____5923 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5952 =
                    let uu____5953 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5953  in
                  FStar_Range.extend_to_end_of_line uu____5952  in
                let uu____5958 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5958 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5997 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5997, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6002  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6002 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6037 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6037  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6039 =
                        let uu____6042 =
                          let uu____6045 = p_fsdoc fsdoc  in
                          let uu____6046 =
                            let uu____6049 = cont lid_doc  in [uu____6049]
                             in
                          uu____6045 :: uu____6046  in
                        kw :: uu____6042  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6039
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6056 =
                        let uu____6057 =
                          let uu____6058 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6058 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6057
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6056
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6078 =
                          let uu____6079 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6079  in
                        prefix2 uu____6078 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6081  ->
      match uu____6081 with
      | (lid,t,doc_opt) ->
          let uu____6098 =
            let uu____6099 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6100 =
              let uu____6101 = p_lident lid  in
              let uu____6102 =
                let uu____6103 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6103  in
              FStar_Pprint.op_Hat_Hat uu____6101 uu____6102  in
            FStar_Pprint.op_Hat_Hat uu____6099 uu____6100  in
          FStar_Pprint.group uu____6098

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6105  ->
    match uu____6105 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6139 =
            let uu____6140 =
              let uu____6141 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6141  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6140  in
          FStar_Pprint.group uu____6139  in
        let uu____6142 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6143 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6147 =
                 let uu____6148 =
                   let uu____6149 =
                     let uu____6150 =
                       let uu____6151 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6151
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6150  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6149  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6148  in
               FStar_Pprint.group uu____6147) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6142 uu____6143

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6155  ->
      fun inner_let  ->
        match uu____6155 with
        | (pat,uu____6163) ->
            let uu____6164 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6216 =
                    let uu____6223 =
                      let uu____6228 =
                        let uu____6229 =
                          let uu____6230 =
                            let uu____6231 = str "by"  in
                            let uu____6233 =
                              let uu____6234 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6234
                               in
                            FStar_Pprint.op_Hat_Hat uu____6231 uu____6233  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6230
                           in
                        FStar_Pprint.group uu____6229  in
                      (t, uu____6228)  in
                    FStar_Pervasives_Native.Some uu____6223  in
                  (pat1, uu____6216)
              | uu____6245 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6164 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6271);
                         FStar_Parser_AST.prange = uu____6272;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6289 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6289 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6295 =
                        if inner_let
                        then
                          let uu____6309 = pats_as_binders_if_possible pats
                             in
                          match uu____6309 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6332 = pats_as_binders_if_possible pats
                              in
                           match uu____6332 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6295 with
                       | (terms,style) ->
                           let uu____6359 =
                             let uu____6360 =
                               let uu____6361 =
                                 let uu____6362 = p_lident lid  in
                                 let uu____6363 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6362
                                   uu____6363
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6361
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6360  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6359)
                  | uu____6366 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6374 =
                              let uu____6375 =
                                let uu____6376 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6376
                                 in
                              FStar_Pprint.group uu____6375  in
                            FStar_Pprint.op_Hat_Hat uu____6374 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6387 =
                        let uu____6388 =
                          let uu____6389 =
                            let uu____6390 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6390  in
                          FStar_Pprint.group uu____6389  in
                        FStar_Pprint.op_Hat_Hat uu____6388 ascr_doc  in
                      FStar_Pprint.group uu____6387))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6392  ->
      match uu____6392 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6401 = p_term_sep false false e  in
          (match uu____6401 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6411 =
                 let uu____6412 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6412  in
               let uu____6413 =
                 let uu____6414 =
                   let uu____6415 =
                     let uu____6416 =
                       let uu____6417 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6417
                        in
                     FStar_Pprint.group uu____6416  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6415  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6414  in
               FStar_Pprint.ifflat uu____6411 uu____6413)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_6418  ->
    match uu___7_6418 with
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
        let uu____6443 = p_uident uid  in
        let uu____6444 = p_binders true bs  in
        let uu____6446 =
          let uu____6447 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6447  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____6443
          uu____6444 uu____6446

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
          let uu____6462 =
            let uu____6463 =
              let uu____6464 =
                let uu____6465 = p_uident uid  in
                let uu____6466 = p_binders true bs  in
                let uu____6468 =
                  let uu____6469 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6469  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6465 uu____6466 uu____6468
                 in
              FStar_Pprint.group uu____6464  in
            let uu____6474 =
              let uu____6475 = str "with"  in
              let uu____6477 =
                let uu____6478 =
                  let uu____6479 =
                    let uu____6480 =
                      let uu____6481 =
                        let uu____6482 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6482
                         in
                      separate_map_last uu____6481 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6480  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6479  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6478  in
              FStar_Pprint.op_Hat_Hat uu____6475 uu____6477  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6463 uu____6474  in
          braces_with_nesting uu____6462

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6486,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6519 =
            let uu____6520 = p_lident lid  in
            let uu____6521 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6520 uu____6521  in
          let uu____6522 = p_simpleTerm ps false e  in
          prefix2 uu____6519 uu____6522
      | uu____6524 ->
          let uu____6525 =
            let uu____6527 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6527
             in
          failwith uu____6525

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6610 =
        match uu____6610 with
        | (kwd,t) ->
            let uu____6621 =
              let uu____6622 = str kwd  in
              let uu____6623 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6622 uu____6623  in
            let uu____6624 = p_simpleTerm ps false t  in
            prefix2 uu____6621 uu____6624
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6631 =
      let uu____6632 =
        let uu____6633 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6634 =
          let uu____6635 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6635  in
        FStar_Pprint.op_Hat_Hat uu____6633 uu____6634  in
      let uu____6637 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6632 uu____6637  in
    let uu____6638 =
      let uu____6639 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6639  in
    FStar_Pprint.op_Hat_Hat uu____6631 uu____6638

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6640  ->
    match uu___8_6640 with
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
        let uu____6660 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6660 FStar_Pprint.hardline
    | uu____6661 ->
        let uu____6662 =
          let uu____6663 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6663  in
        FStar_Pprint.op_Hat_Hat uu____6662 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6666  ->
    match uu___9_6666 with
    | FStar_Parser_AST.Rec  ->
        let uu____6667 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6667
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6669  ->
    match uu___10_6669 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6674,e) -> e
          | uu____6680 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6681 = str "#["  in
        let uu____6683 =
          let uu____6684 = p_term false false t1  in
          let uu____6687 =
            let uu____6688 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6688 break1  in
          FStar_Pprint.op_Hat_Hat uu____6684 uu____6687  in
        FStar_Pprint.op_Hat_Hat uu____6681 uu____6683

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6694 =
          let uu____6695 =
            let uu____6696 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6696  in
          FStar_Pprint.separate_map uu____6695 p_tuplePattern pats  in
        FStar_Pprint.group uu____6694
    | uu____6697 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6706 =
          let uu____6707 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6707 p_constructorPattern pats  in
        FStar_Pprint.group uu____6706
    | uu____6708 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6711;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6716 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6717 = p_constructorPattern hd1  in
        let uu____6718 = p_constructorPattern tl1  in
        infix0 uu____6716 uu____6717 uu____6718
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6720;_},pats)
        ->
        let uu____6726 = p_quident uid  in
        let uu____6727 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6726 uu____6727
    | uu____6728 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6744;
               FStar_Parser_AST.blevel = uu____6745;
               FStar_Parser_AST.aqual = uu____6746;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6755 =
               let uu____6756 = p_ident lid  in
               p_refinement aqual uu____6756 t1 phi  in
             soft_parens_with_nesting uu____6755
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6759;
               FStar_Parser_AST.blevel = uu____6760;
               FStar_Parser_AST.aqual = uu____6761;_},phi))
             ->
             let uu____6767 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6767
         | uu____6768 ->
             let uu____6773 =
               let uu____6774 = p_tuplePattern pat  in
               let uu____6775 =
                 let uu____6776 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6776
                  in
               FStar_Pprint.op_Hat_Hat uu____6774 uu____6775  in
             soft_parens_with_nesting uu____6773)
    | FStar_Parser_AST.PatList pats ->
        let uu____6780 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6780 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6799 =
          match uu____6799 with
          | (lid,pat) ->
              let uu____6806 = p_qlident lid  in
              let uu____6807 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6806 uu____6807
           in
        let uu____6808 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6808
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6820 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6821 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6822 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6820
          uu____6821 uu____6822
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6833 =
          let uu____6834 =
            let uu____6835 =
              let uu____6836 = FStar_Ident.text_of_id op  in str uu____6836
               in
            let uu____6838 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6835 uu____6838  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6834  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6833
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6842 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6842 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6850 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6851 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6850 uu____6851
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6853 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6857;
           FStar_Parser_AST.prange = uu____6858;_},uu____6859)
        ->
        let uu____6864 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6864
    | FStar_Parser_AST.PatTuple (uu____6865,false ) ->
        let uu____6872 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6872
    | uu____6873 ->
        let uu____6874 =
          let uu____6876 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6876  in
        failwith uu____6874

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6881;_},uu____6882)
        -> true
    | uu____6889 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6895) -> true
    | uu____6897 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6904 = p_binder' is_atomic b  in
      match uu____6904 with
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
          let uu____6941 =
            let uu____6942 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6943 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6942 uu____6943  in
          (uu____6941, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6949 = p_lident lid  in
          (uu____6949, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6956 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6967;
                   FStar_Parser_AST.blevel = uu____6968;
                   FStar_Parser_AST.aqual = uu____6969;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6974 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6974 t1 phi
            | uu____6975 ->
                let t' =
                  let uu____6977 = is_typ_tuple t  in
                  if uu____6977
                  then
                    let uu____6980 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6980
                  else p_tmFormula t  in
                let uu____6983 =
                  let uu____6984 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6985 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6984 uu____6985  in
                (uu____6983, t')
             in
          (match uu____6956 with
           | (b',t') ->
               let catf =
                 let uu____7003 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7003
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7010 =
                         let uu____7011 =
                           let uu____7012 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7012
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7011
                          in
                       FStar_Pprint.group uu____7010
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7017 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7017)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7022 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7050;
                  FStar_Parser_AST.blevel = uu____7051;
                  FStar_Parser_AST.aqual = uu____7052;_},phi)
               ->
               let uu____7056 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7056 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7077 ->
               if is_atomic
               then
                 let uu____7089 = p_atomicTerm t  in
                 (uu____7089, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7096 = p_appTerm t  in
                  (uu____7096, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7107 = p_refinement' aqual_opt binder t phi  in
          match uu____7107 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7123 -> false
            | FStar_Parser_AST.App uu____7135 -> false
            | FStar_Parser_AST.Op uu____7143 -> false
            | uu____7151 -> true  in
          let uu____7153 = p_noSeqTerm false false phi  in
          match uu____7153 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7170 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7170)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____7179 =
                let uu____7180 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7180 binder  in
              let uu____7181 =
                let uu____7182 = p_appTerm t  in
                let uu____7183 =
                  let uu____7184 =
                    let uu____7185 =
                      let uu____7186 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7187 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7186 uu____7187  in
                    FStar_Pprint.group uu____7185  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____7184
                   in
                FStar_Pprint.op_Hat_Hat uu____7182 uu____7183  in
              (uu____7179, uu____7181)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7201 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7201

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7205 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7208 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7208)
       in
    if uu____7205
    then FStar_Pprint.underscore
    else (let uu____7213 = FStar_Ident.text_of_id lid  in str uu____7213)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7216 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7219 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7219)
       in
    if uu____7216
    then FStar_Pprint.underscore
    else (let uu____7224 = FStar_Ident.text_of_lid lid  in str uu____7224)

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
          let uu____7245 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7245
        else
          (let uu____7248 =
             let uu____7249 =
               let uu____7250 =
                 let uu____7251 =
                   let uu____7252 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7252  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7251  in
               FStar_Pprint.group uu____7250  in
             let uu____7253 =
               let uu____7254 =
                 let uu____7255 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7255  in
               FStar_Pprint.op_Hat_Hat comm uu____7254  in
             FStar_Pprint.ifflat uu____7249 uu____7253  in
           FStar_All.pipe_left FStar_Pprint.group uu____7248)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7263 = p_noSeqTerm true false e1  in
            (match uu____7263 with
             | (comm,t1) ->
                 let uu____7272 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7273 =
                   let uu____7274 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7274
                    in
                 FStar_Pprint.op_Hat_Hat uu____7272 uu____7273)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7278 =
              let uu____7279 =
                let uu____7280 =
                  let uu____7281 = p_lident x  in
                  let uu____7282 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7281 uu____7282  in
                let uu____7283 =
                  let uu____7284 = p_noSeqTermAndComment true false e1  in
                  let uu____7287 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7284 uu____7287  in
                op_Hat_Slash_Plus_Hat uu____7280 uu____7283  in
              FStar_Pprint.group uu____7279  in
            let uu____7288 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7278 uu____7288
        | uu____7289 ->
            let uu____7290 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7290

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
            let uu____7302 = p_noSeqTerm true false e1  in
            (match uu____7302 with
             | (comm,t1) ->
                 let uu____7315 =
                   let uu____7316 =
                     let uu____7317 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7317  in
                   let uu____7318 =
                     let uu____7319 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7319
                      in
                   FStar_Pprint.op_Hat_Hat uu____7316 uu____7318  in
                 (comm, uu____7315))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7323 =
              let uu____7324 =
                let uu____7325 =
                  let uu____7326 =
                    let uu____7327 = p_lident x  in
                    let uu____7328 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7327 uu____7328  in
                  let uu____7329 =
                    let uu____7330 = p_noSeqTermAndComment true false e1  in
                    let uu____7333 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7330 uu____7333  in
                  op_Hat_Slash_Plus_Hat uu____7326 uu____7329  in
                FStar_Pprint.group uu____7325  in
              let uu____7334 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7324 uu____7334  in
            (FStar_Pprint.empty, uu____7323)
        | uu____7335 -> p_noSeqTerm ps pb e

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
            let uu____7355 =
              let uu____7356 = p_tmIff e1  in
              let uu____7357 =
                let uu____7358 =
                  let uu____7359 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7359
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7358  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7356 uu____7357  in
            FStar_Pprint.group uu____7355
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7365 =
              let uu____7366 = p_tmIff e1  in
              let uu____7367 =
                let uu____7368 =
                  let uu____7369 =
                    let uu____7370 = p_typ false false t  in
                    let uu____7373 =
                      let uu____7374 = str "by"  in
                      let uu____7376 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7374 uu____7376  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7370 uu____7373  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7369
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7368  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7366 uu____7367  in
            FStar_Pprint.group uu____7365
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7377;_},e1::e2::e3::[])
            ->
            let uu____7384 =
              let uu____7385 =
                let uu____7386 =
                  let uu____7387 = p_atomicTermNotQUident e1  in
                  let uu____7388 =
                    let uu____7389 =
                      let uu____7390 =
                        let uu____7391 = p_term false false e2  in
                        soft_parens_with_nesting uu____7391  in
                      let uu____7394 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7390 uu____7394  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7389  in
                  FStar_Pprint.op_Hat_Hat uu____7387 uu____7388  in
                FStar_Pprint.group uu____7386  in
              let uu____7395 =
                let uu____7396 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7396  in
              FStar_Pprint.op_Hat_Hat uu____7385 uu____7395  in
            FStar_Pprint.group uu____7384
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7397;_},e1::e2::e3::[])
            ->
            let uu____7404 =
              let uu____7405 =
                let uu____7406 =
                  let uu____7407 = p_atomicTermNotQUident e1  in
                  let uu____7408 =
                    let uu____7409 =
                      let uu____7410 =
                        let uu____7411 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7411  in
                      let uu____7414 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7410 uu____7414  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7409  in
                  FStar_Pprint.op_Hat_Hat uu____7407 uu____7408  in
                FStar_Pprint.group uu____7406  in
              let uu____7415 =
                let uu____7416 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7416  in
              FStar_Pprint.op_Hat_Hat uu____7405 uu____7415  in
            FStar_Pprint.group uu____7404
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7426 =
              let uu____7427 = str "requires"  in
              let uu____7429 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7427 uu____7429  in
            FStar_Pprint.group uu____7426
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7439 =
              let uu____7440 = str "ensures"  in
              let uu____7442 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7440 uu____7442  in
            FStar_Pprint.group uu____7439
        | FStar_Parser_AST.Attributes es ->
            let uu____7446 =
              let uu____7447 = str "attributes"  in
              let uu____7449 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7447 uu____7449  in
            FStar_Pprint.group uu____7446
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7454 =
                let uu____7455 =
                  let uu____7456 = str "if"  in
                  let uu____7458 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7456 uu____7458  in
                let uu____7461 =
                  let uu____7462 = str "then"  in
                  let uu____7464 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7462 uu____7464  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7455 uu____7461  in
              FStar_Pprint.group uu____7454
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7468,uu____7469,e31) when
                     is_unit e31 ->
                     let uu____7471 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7471
                 | uu____7474 -> p_noSeqTermAndComment false false e2  in
               let uu____7477 =
                 let uu____7478 =
                   let uu____7479 = str "if"  in
                   let uu____7481 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7479 uu____7481  in
                 let uu____7484 =
                   let uu____7485 =
                     let uu____7486 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7486 e2_doc  in
                   let uu____7488 =
                     let uu____7489 = str "else"  in
                     let uu____7491 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7489 uu____7491  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7485 uu____7488  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7478 uu____7484  in
               FStar_Pprint.group uu____7477)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7514 =
              let uu____7515 =
                let uu____7516 =
                  let uu____7517 = str "try"  in
                  let uu____7519 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7517 uu____7519  in
                let uu____7522 =
                  let uu____7523 = str "with"  in
                  let uu____7525 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7523 uu____7525  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7516 uu____7522  in
              FStar_Pprint.group uu____7515  in
            let uu____7534 = paren_if (ps || pb)  in uu____7534 uu____7514
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7561 =
              let uu____7562 =
                let uu____7563 =
                  let uu____7564 = str "match"  in
                  let uu____7566 = p_noSeqTermAndComment false false e1  in
                  let uu____7569 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7564 uu____7566 uu____7569
                   in
                let uu____7573 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7563 uu____7573  in
              FStar_Pprint.group uu____7562  in
            let uu____7582 = paren_if (ps || pb)  in uu____7582 uu____7561
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7589 =
              let uu____7590 =
                let uu____7591 =
                  let uu____7592 = str "let open"  in
                  let uu____7594 = p_quident uid  in
                  let uu____7595 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7592 uu____7594 uu____7595
                   in
                let uu____7599 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7591 uu____7599  in
              FStar_Pprint.group uu____7590  in
            let uu____7601 = paren_if ps  in uu____7601 uu____7589
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7666 is_last =
              match uu____7666 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7700 =
                          let uu____7701 = str "let"  in
                          let uu____7703 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7701 uu____7703
                           in
                        FStar_Pprint.group uu____7700
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7706 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7712 = p_term_sep false false e2  in
                  (match uu____7712 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7722 =
                         if is_last
                         then
                           let uu____7724 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7725 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7724 doc_expr1 uu____7725
                         else
                           (let uu____7731 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7731)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7722)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7782 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7782
                     else
                       (let uu____7787 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7787)) lbs
               in
            let lbs_doc =
              let uu____7791 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7791  in
            let uu____7792 =
              let uu____7793 =
                let uu____7794 =
                  let uu____7795 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7795
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7794  in
              FStar_Pprint.group uu____7793  in
            let uu____7797 = paren_if ps  in uu____7797 uu____7792
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7804;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7807;
                                                             FStar_Parser_AST.level
                                                               = uu____7808;_})
            when matches_var maybe_x x ->
            let uu____7835 =
              let uu____7836 =
                let uu____7837 = str "function"  in
                let uu____7839 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7837 uu____7839  in
              FStar_Pprint.group uu____7836  in
            let uu____7848 = paren_if (ps || pb)  in uu____7848 uu____7835
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7854 =
              let uu____7855 = str "quote"  in
              let uu____7857 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7855 uu____7857  in
            FStar_Pprint.group uu____7854
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7859 =
              let uu____7860 = str "`"  in
              let uu____7862 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7860 uu____7862  in
            FStar_Pprint.group uu____7859
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7864 =
              let uu____7865 = str "`%"  in
              let uu____7867 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7865 uu____7867  in
            FStar_Pprint.group uu____7864
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7869;
              FStar_Parser_AST.level = uu____7870;_}
            ->
            let uu____7871 =
              let uu____7872 = str "`@"  in
              let uu____7874 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7872 uu____7874  in
            FStar_Pprint.group uu____7871
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7876 =
              let uu____7877 = str "`#"  in
              let uu____7879 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7877 uu____7879  in
            FStar_Pprint.group uu____7876
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7888 = str "calc"  in
              let uu____7890 =
                let uu____7891 =
                  let uu____7892 = p_noSeqTermAndComment false false rel  in
                  let uu____7895 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7892 uu____7895  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7891  in
              FStar_Pprint.op_Hat_Hat uu____7888 uu____7890  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7897 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7898 =
              let uu____7899 =
                let uu____7900 =
                  let uu____7901 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7904 =
                    let uu____7905 = str ";"  in
                    let uu____7907 =
                      let uu____7908 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7908
                       in
                    FStar_Pprint.op_Hat_Hat uu____7905 uu____7907  in
                  FStar_Pprint.op_Hat_Hat uu____7901 uu____7904  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7900  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7899
               in
            FStar_Pprint.enclose head1 uu____7897 uu____7898
        | uu____7910 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7911  ->
    fun uu____7912  ->
      match uu____7912 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7917 =
            let uu____7918 = p_noSeqTermAndComment false false rel  in
            let uu____7921 =
              let uu____7922 =
                let uu____7923 =
                  let uu____7924 =
                    let uu____7925 = p_noSeqTermAndComment false false just
                       in
                    let uu____7928 =
                      let uu____7929 =
                        let uu____7930 =
                          let uu____7931 =
                            let uu____7932 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7935 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7932 uu____7935  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7931
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7930
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7929
                       in
                    FStar_Pprint.op_Hat_Hat uu____7925 uu____7928  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7924  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7923  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7922  in
            FStar_Pprint.op_Hat_Hat uu____7918 uu____7921  in
          FStar_Pprint.group uu____7917

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7937  ->
    match uu___11_7937 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7949 =
          let uu____7950 = str "[@"  in
          let uu____7952 =
            let uu____7953 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7954 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7953 uu____7954  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7950 uu____7952  in
        FStar_Pprint.group uu____7949

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
        | FStar_Parser_AST.QForall (bs,(uu____7972,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8006 =
                   let uu____8007 =
                     let uu____8008 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8008 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8007 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8006 term_doc
             | pats ->
                 let uu____8016 =
                   let uu____8017 =
                     let uu____8018 =
                       let uu____8019 =
                         let uu____8020 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8020
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8019 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8023 = p_trigger trigger  in
                     prefix2 uu____8018 uu____8023  in
                   FStar_Pprint.group uu____8017  in
                 prefix2 uu____8016 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____8025,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8059 =
                   let uu____8060 =
                     let uu____8061 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8061 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8060 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8059 term_doc
             | pats ->
                 let uu____8069 =
                   let uu____8070 =
                     let uu____8071 =
                       let uu____8072 =
                         let uu____8073 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8073
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8072 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8076 = p_trigger trigger  in
                     prefix2 uu____8071 uu____8076  in
                   FStar_Pprint.group uu____8070  in
                 prefix2 uu____8069 term_doc)
        | uu____8077 -> p_simpleTerm ps pb e

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
      let uu____8098 = all_binders_annot t  in
      if uu____8098
      then
        let uu____8101 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8101
      else
        (let uu____8112 =
           let uu____8113 =
             let uu____8114 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8114  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8113  in
         FStar_Pprint.group uu____8112)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8173 = x  in
      match uu____8173 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8238 = hd1  in
               (match uu____8238 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8310 = cb  in
      match uu____8310 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8329 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8335 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8335) hd1 tl1
                  in
               cat_with_colon uu____8329 typ)
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
                 FStar_Parser_AST.brange = uu____8414;
                 FStar_Parser_AST.blevel = uu____8415;
                 FStar_Parser_AST.aqual = uu____8416;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8425 =
                 let uu____8430 = p_ident lid  in
                 p_refinement' aqual uu____8430 t1 phi  in
               FStar_Pervasives_Native.Some uu____8425
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8437) ->
               let uu____8442 =
                 let uu____8447 =
                   let uu____8448 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8449 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8448 uu____8449  in
                 let uu____8450 = p_tmEqNoRefinement t  in
                 (uu____8447, uu____8450)  in
               FStar_Pervasives_Native.Some uu____8442
           | uu____8455 -> FStar_Pervasives_Native.None)
      | uu____8464 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8477 -> false
      | uu____8489 -> true  in
    let uu____8491 = map_if_all all_binders pats  in
    match uu____8491 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8523 = collapse_pats bs  in
        (uu____8523, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8540 = FStar_List.map p_atomicPattern pats  in
        (uu____8540, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8552 -> str "forall"
    | FStar_Parser_AST.QExists uu____8572 -> str "exists"
    | uu____8592 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8594  ->
    match uu___12_8594 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8606 =
          let uu____8607 =
            let uu____8608 =
              let uu____8609 = str "pattern"  in
              let uu____8611 =
                let uu____8612 =
                  let uu____8613 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8613
                   in
                FStar_Pprint.op_Hat_Hat uu____8612 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8609 uu____8611  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8608  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8607  in
        FStar_Pprint.group uu____8606

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8621 = str "\\/"  in
    FStar_Pprint.separate_map uu____8621 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8628 =
      let uu____8629 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8629 p_appTerm pats  in
    FStar_Pprint.group uu____8628

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8641 = p_term_sep false pb e1  in
            (match uu____8641 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8650 = str "fun"  in
                   let uu____8652 =
                     let uu____8653 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8653
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8650 uu____8652  in
                 let uu____8654 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8656 =
                       let uu____8657 =
                         let uu____8658 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8658  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8657
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8656
                   else
                     (let uu____8661 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8661)
                    in
                 let uu____8662 = paren_if ps  in uu____8662 uu____8654)
        | uu____8667 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8675  ->
      match uu____8675 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8699 =
                    let uu____8700 =
                      let uu____8701 =
                        let uu____8702 = p_tuplePattern p  in
                        let uu____8703 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8702 uu____8703  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8701
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8700  in
                  FStar_Pprint.group uu____8699
              | FStar_Pervasives_Native.Some f ->
                  let uu____8705 =
                    let uu____8706 =
                      let uu____8707 =
                        let uu____8708 =
                          let uu____8709 =
                            let uu____8710 = p_tuplePattern p  in
                            let uu____8711 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8710
                              uu____8711
                             in
                          FStar_Pprint.group uu____8709  in
                        let uu____8713 =
                          let uu____8714 =
                            let uu____8717 = p_tmFormula f  in
                            [uu____8717; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8714  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8708 uu____8713
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8707
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8706  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8705
               in
            let uu____8719 = p_term_sep false pb e  in
            match uu____8719 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8729 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8729
                   else
                     (let uu____8732 =
                        let uu____8733 =
                          let uu____8734 =
                            let uu____8735 =
                              let uu____8736 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8736  in
                            op_Hat_Slash_Plus_Hat branch uu____8735  in
                          FStar_Pprint.group uu____8734  in
                        let uu____8737 =
                          let uu____8738 =
                            let uu____8739 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8739  in
                          FStar_Pprint.op_Hat_Hat branch uu____8738  in
                        FStar_Pprint.ifflat uu____8733 uu____8737  in
                      FStar_Pprint.group uu____8732))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8743 =
                       let uu____8744 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8744  in
                     op_Hat_Slash_Plus_Hat branch uu____8743)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8755 =
                      let uu____8756 =
                        let uu____8757 =
                          let uu____8758 =
                            let uu____8759 =
                              let uu____8760 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8760  in
                            FStar_Pprint.separate_map uu____8759
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8758
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8757
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8756  in
                    FStar_Pprint.group uu____8755
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8762 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8764;_},e1::e2::[])
        ->
        let uu____8770 = str "<==>"  in
        let uu____8772 = p_tmImplies e1  in
        let uu____8773 = p_tmIff e2  in
        infix0 uu____8770 uu____8772 uu____8773
    | uu____8774 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8776;_},e1::e2::[])
        ->
        let uu____8782 = str "==>"  in
        let uu____8784 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8790 = p_tmImplies e2  in
        infix0 uu____8782 uu____8784 uu____8790
    | uu____8791 ->
        p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
          p_tmFormula e

and (format_sig :
  annotation_style ->
    FStar_Pprint.document Prims.list ->
      Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun style  ->
    fun terms  ->
      fun no_last_op  ->
        fun flat_space  ->
          let uu____8805 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8805 with
          | (terms',last1) ->
              let uu____8825 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8860 =
                      let uu____8861 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8861
                       in
                    let uu____8862 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8860, uu____8862)
                | Binders (n1,ln,parens1) ->
                    let uu____8876 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8884 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8876, break1, uu____8884)
                 in
              (match uu____8825 with
               | (n1,last_n,terms'1,sep,last_op) ->
                   let last2 = FStar_List.hd last1  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > Prims.int_one) &&
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
                    | _8917 when _8917 = Prims.int_one -> FStar_List.hd terms
                    | uu____8918 ->
                        let uu____8919 =
                          let uu____8920 =
                            let uu____8921 =
                              let uu____8922 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8923 =
                                let uu____8924 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8924
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8922 uu____8923
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8921  in
                          let uu____8925 =
                            let uu____8926 =
                              let uu____8927 =
                                let uu____8928 =
                                  let uu____8929 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8929  in
                                let uu____8930 =
                                  let uu____8931 =
                                    let uu____8932 =
                                      let uu____8933 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8934 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8940 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8940)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8933
                                        uu____8934
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8932
                                     in
                                  jump2 uu____8931  in
                                FStar_Pprint.ifflat uu____8928 uu____8930  in
                              FStar_Pprint.group uu____8927  in
                            let uu____8942 =
                              let uu____8943 =
                                let uu____8944 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8944  in
                              FStar_Pprint.align uu____8943  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8926
                              uu____8942
                             in
                          FStar_Pprint.ifflat uu____8920 uu____8925  in
                        FStar_Pprint.group uu____8919))

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
            | Arrows uu____8958 -> p_tmArrow' p_Tm e
            | Binders uu____8965 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8988 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8994 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8988 uu____8994
      | uu____8997 -> let uu____8998 = p_Tm e  in [uu____8998]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9051 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9077 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9051 uu____9077
        | uu____9100 ->
            let uu____9101 =
              let uu____9112 = p_Tm1 e1  in
              (uu____9112, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9101]
         in
      let fold_fun bs x =
        let uu____9210 = x  in
        match uu____9210 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9342 = hd1  in
                 (match uu____9342 with
                  | (b2s,t2,uu____9371) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9473 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9530 = cb  in
        match uu____9530 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9559 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9570 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9576 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9576) hd1 tl1
                         in
                      f uu____9570 typ))
         in
      let binders =
        let uu____9592 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9592  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9655 =
        let uu____9656 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9656 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9655  in
    let disj =
      let uu____9659 =
        let uu____9660 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9660 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9659  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9680;_},e1::e2::[])
        ->
        let uu____9686 = p_tmDisjunction e1  in
        let uu____9691 = let uu____9696 = p_tmConjunction e2  in [uu____9696]
           in
        FStar_List.append uu____9686 uu____9691
    | uu____9705 -> let uu____9706 = p_tmConjunction e  in [uu____9706]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9716;_},e1::e2::[])
        ->
        let uu____9722 = p_tmConjunction e1  in
        let uu____9725 = let uu____9728 = p_tmTuple e2  in [uu____9728]  in
        FStar_List.append uu____9722 uu____9725
    | uu____9729 -> let uu____9730 = p_tmTuple e  in [uu____9730]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9747 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9747
          (fun uu____9755  ->
             match uu____9755 with | (e1,uu____9761) -> p_tmEq e1) args
    | uu____9762 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9771 =
             let uu____9772 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9772  in
           FStar_Pprint.group uu____9771)

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
               (let uu____9791 = FStar_Ident.text_of_id op  in
                uu____9791 = "="))
              ||
              (let uu____9796 = FStar_Ident.text_of_id op  in
               uu____9796 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9802 = levels op1  in
            (match uu____9802 with
             | (left1,mine,right1) ->
                 let uu____9821 =
                   let uu____9822 = FStar_All.pipe_left str op1  in
                   let uu____9824 = p_tmEqWith' p_X left1 e1  in
                   let uu____9825 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9822 uu____9824 uu____9825  in
                 paren_if_gt curr mine uu____9821)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9826;_},e1::e2::[])
            ->
            let uu____9832 =
              let uu____9833 = p_tmEqWith p_X e1  in
              let uu____9834 =
                let uu____9835 =
                  let uu____9836 =
                    let uu____9837 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9837  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9836  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9835  in
              FStar_Pprint.op_Hat_Hat uu____9833 uu____9834  in
            FStar_Pprint.group uu____9832
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9838;_},e1::[])
            ->
            let uu____9843 = levels "-"  in
            (match uu____9843 with
             | (left1,mine,right1) ->
                 let uu____9863 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9863)
        | uu____9864 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9912)::(e2,uu____9914)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9934 = is_list e  in Prims.op_Negation uu____9934)
              ->
              let op = "::"  in
              let uu____9939 = levels op  in
              (match uu____9939 with
               | (left1,mine,right1) ->
                   let uu____9958 =
                     let uu____9959 = str op  in
                     let uu____9960 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9962 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9959 uu____9960 uu____9962  in
                   paren_if_gt curr mine uu____9958)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9981 = levels op  in
              (match uu____9981 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10015 = p_binder false b  in
                         let uu____10017 =
                           let uu____10018 =
                             let uu____10019 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10019 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10018
                            in
                         FStar_Pprint.op_Hat_Hat uu____10015 uu____10017
                     | FStar_Util.Inr t ->
                         let uu____10021 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10023 =
                           let uu____10024 =
                             let uu____10025 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10025 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10024
                            in
                         FStar_Pprint.op_Hat_Hat uu____10021 uu____10023
                      in
                   let uu____10026 =
                     let uu____10027 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10032 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10027 uu____10032  in
                   paren_if_gt curr mine uu____10026)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10034;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10064 = levels op  in
              (match uu____10064 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10084 = str op  in
                     let uu____10085 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10087 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10084 uu____10085 uu____10087
                   else
                     (let uu____10091 =
                        let uu____10092 = str op  in
                        let uu____10093 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10095 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10092 uu____10093 uu____10095  in
                      paren_if_gt curr mine uu____10091))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10104 = levels op1  in
              (match uu____10104 with
               | (left1,mine,right1) ->
                   let uu____10123 =
                     let uu____10124 = str op1  in
                     let uu____10125 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10127 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10124 uu____10125 uu____10127  in
                   paren_if_gt curr mine uu____10123)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10147 =
                let uu____10148 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10149 =
                  let uu____10150 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10150 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10148 uu____10149  in
              braces_with_nesting uu____10147
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10155;_},e1::[])
              ->
              let uu____10160 =
                let uu____10161 = str "~"  in
                let uu____10163 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10161 uu____10163  in
              FStar_Pprint.group uu____10160
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10165;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10174 = levels op  in
                   (match uu____10174 with
                    | (left1,mine,right1) ->
                        let uu____10193 =
                          let uu____10194 = str op  in
                          let uu____10195 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10197 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10194 uu____10195 uu____10197  in
                        paren_if_gt curr mine uu____10193)
               | uu____10199 -> p_X e)
          | uu____10200 -> p_X e

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
        let uu____10207 =
          let uu____10208 = p_lident lid  in
          let uu____10209 =
            let uu____10210 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10210  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10208 uu____10209  in
        FStar_Pprint.group uu____10207
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10213 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10215 = p_appTerm e  in
    let uu____10216 =
      let uu____10217 =
        let uu____10218 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10218 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10217  in
    FStar_Pprint.op_Hat_Hat uu____10215 uu____10216

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10224 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10224 t phi
      | FStar_Parser_AST.TAnnotated uu____10225 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10231 ->
          let uu____10232 =
            let uu____10234 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10234
             in
          failwith uu____10232
      | FStar_Parser_AST.TVariable uu____10237 ->
          let uu____10238 =
            let uu____10240 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10240
             in
          failwith uu____10238
      | FStar_Parser_AST.NoName uu____10243 ->
          let uu____10244 =
            let uu____10246 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10246
             in
          failwith uu____10244

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10250  ->
      match uu____10250 with
      | (lid,e) ->
          let uu____10258 =
            let uu____10259 = p_qlident lid  in
            let uu____10260 =
              let uu____10261 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10261
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10259 uu____10260  in
          FStar_Pprint.group uu____10258

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10264 when is_general_application e ->
        let uu____10271 = head_and_args e  in
        (match uu____10271 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10318 = p_argTerm e1  in
                  let uu____10319 =
                    let uu____10320 =
                      let uu____10321 =
                        let uu____10322 = str "`"  in
                        let uu____10324 =
                          let uu____10325 = p_indexingTerm head1  in
                          let uu____10326 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10325 uu____10326  in
                        FStar_Pprint.op_Hat_Hat uu____10322 uu____10324  in
                      FStar_Pprint.group uu____10321  in
                    let uu____10328 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10320 uu____10328  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10318 uu____10319
              | uu____10329 ->
                  let uu____10336 =
                    let uu____10347 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10347
                    then
                      let uu____10381 =
                        FStar_Util.take
                          (fun uu____10405  ->
                             match uu____10405 with
                             | (uu____10411,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10381 with
                      | (fs_typ_args,args1) ->
                          let uu____10449 =
                            let uu____10450 = p_indexingTerm head1  in
                            let uu____10451 =
                              let uu____10452 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10452
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10450 uu____10451
                             in
                          (uu____10449, args1)
                    else
                      (let uu____10467 = p_indexingTerm head1  in
                       (uu____10467, args))
                     in
                  (match uu____10336 with
                   | (head_doc,args1) ->
                       let uu____10488 =
                         let uu____10489 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10489 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10488)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10511 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10511)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10530 =
               let uu____10531 = p_quident lid  in
               let uu____10532 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10531 uu____10532  in
             FStar_Pprint.group uu____10530
         | hd1::tl1 ->
             let uu____10549 =
               let uu____10550 =
                 let uu____10551 =
                   let uu____10552 = p_quident lid  in
                   let uu____10553 = p_argTerm hd1  in
                   prefix2 uu____10552 uu____10553  in
                 FStar_Pprint.group uu____10551  in
               let uu____10554 =
                 let uu____10555 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10555  in
               FStar_Pprint.op_Hat_Hat uu____10550 uu____10554  in
             FStar_Pprint.group uu____10549)
    | uu____10560 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10571 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10571 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10575 = str "#"  in
        let uu____10577 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10575 uu____10577
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10580 = str "#["  in
        let uu____10582 =
          let uu____10583 = p_indexingTerm t  in
          let uu____10584 =
            let uu____10585 = str "]"  in
            let uu____10587 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10585 uu____10587  in
          FStar_Pprint.op_Hat_Hat uu____10583 uu____10584  in
        FStar_Pprint.op_Hat_Hat uu____10580 uu____10582
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10590  ->
    match uu____10590 with | (e,uu____10596) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10601;_},e1::e2::[])
          ->
          let uu____10607 =
            let uu____10608 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10609 =
              let uu____10610 =
                let uu____10611 = p_term false false e2  in
                soft_parens_with_nesting uu____10611  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10610  in
            FStar_Pprint.op_Hat_Hat uu____10608 uu____10609  in
          FStar_Pprint.group uu____10607
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10614;_},e1::e2::[])
          ->
          let uu____10620 =
            let uu____10621 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10622 =
              let uu____10623 =
                let uu____10624 = p_term false false e2  in
                soft_brackets_with_nesting uu____10624  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10623  in
            FStar_Pprint.op_Hat_Hat uu____10621 uu____10622  in
          FStar_Pprint.group uu____10620
      | uu____10627 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10632 = p_quident lid  in
        let uu____10633 =
          let uu____10634 =
            let uu____10635 = p_term false false e1  in
            soft_parens_with_nesting uu____10635  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10634  in
        FStar_Pprint.op_Hat_Hat uu____10632 uu____10633
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10643 =
          let uu____10644 = FStar_Ident.text_of_id op  in str uu____10644  in
        let uu____10646 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10643 uu____10646
    | uu____10647 -> p_atomicTermNotQUident e

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
         | uu____10660 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10669 =
          let uu____10670 = FStar_Ident.text_of_id op  in str uu____10670  in
        let uu____10672 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10669 uu____10672
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10676 =
          let uu____10677 =
            let uu____10678 =
              let uu____10679 = FStar_Ident.text_of_id op  in str uu____10679
               in
            let uu____10681 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10678 uu____10681  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10677  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10676
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10696 = all_explicit args  in
        if uu____10696
        then
          let uu____10699 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10700 =
            let uu____10701 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10702 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10701 p_tmEq uu____10702  in
          let uu____10709 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10699
            uu____10700 uu____10709
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10731 =
                 let uu____10732 = p_quident lid  in
                 let uu____10733 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10732 uu____10733  in
               FStar_Pprint.group uu____10731
           | hd1::tl1 ->
               let uu____10750 =
                 let uu____10751 =
                   let uu____10752 =
                     let uu____10753 = p_quident lid  in
                     let uu____10754 = p_argTerm hd1  in
                     prefix2 uu____10753 uu____10754  in
                   FStar_Pprint.group uu____10752  in
                 let uu____10755 =
                   let uu____10756 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10756  in
                 FStar_Pprint.op_Hat_Hat uu____10751 uu____10755  in
               FStar_Pprint.group uu____10750)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10763 =
          let uu____10764 = p_atomicTermNotQUident e1  in
          let uu____10765 =
            let uu____10766 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10766  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10764
            uu____10765
           in
        FStar_Pprint.group uu____10763
    | uu____10769 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10774 = p_quident constr_lid  in
        let uu____10775 =
          let uu____10776 =
            let uu____10777 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10777  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10776  in
        FStar_Pprint.op_Hat_Hat uu____10774 uu____10775
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10779 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10779 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10781 = p_term_sep false false e1  in
        (match uu____10781 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10794 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10794))
    | uu____10795 when is_array e ->
        let es = extract_from_list e  in
        let uu____10799 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10800 =
          let uu____10801 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10801
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10806 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10799
          uu____10800 uu____10806
    | uu____10809 when is_list e ->
        let uu____10810 =
          let uu____10811 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10812 = extract_from_list e  in
          separate_map_or_flow_last uu____10811
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10812
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10810 FStar_Pprint.rbracket
    | uu____10821 when is_lex_list e ->
        let uu____10822 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10823 =
          let uu____10824 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10825 = extract_from_list e  in
          separate_map_or_flow_last uu____10824
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10825
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10822
          uu____10823 FStar_Pprint.rbracket
    | uu____10834 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10838 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10839 =
          let uu____10840 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10840 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10838
          uu____10839 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10850 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10853 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10850 uu____10853
    | FStar_Parser_AST.Op (op,args) when
        let uu____10862 = handleable_op op args  in
        Prims.op_Negation uu____10862 ->
        let uu____10864 =
          let uu____10866 =
            let uu____10868 = FStar_Ident.text_of_id op  in
            let uu____10870 =
              let uu____10872 =
                let uu____10874 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10874
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10872  in
            Prims.op_Hat uu____10868 uu____10870  in
          Prims.op_Hat "Operation " uu____10866  in
        failwith uu____10864
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10881 = p_term false false e  in
        soft_parens_with_nesting uu____10881
    | FStar_Parser_AST.Const uu____10884 ->
        let uu____10885 = p_term false false e  in
        soft_parens_with_nesting uu____10885
    | FStar_Parser_AST.Op uu____10888 ->
        let uu____10895 = p_term false false e  in
        soft_parens_with_nesting uu____10895
    | FStar_Parser_AST.Tvar uu____10898 ->
        let uu____10899 = p_term false false e  in
        soft_parens_with_nesting uu____10899
    | FStar_Parser_AST.Var uu____10902 ->
        let uu____10903 = p_term false false e  in
        soft_parens_with_nesting uu____10903
    | FStar_Parser_AST.Name uu____10906 ->
        let uu____10907 = p_term false false e  in
        soft_parens_with_nesting uu____10907
    | FStar_Parser_AST.Construct uu____10910 ->
        let uu____10921 = p_term false false e  in
        soft_parens_with_nesting uu____10921
    | FStar_Parser_AST.Abs uu____10924 ->
        let uu____10931 = p_term false false e  in
        soft_parens_with_nesting uu____10931
    | FStar_Parser_AST.App uu____10934 ->
        let uu____10941 = p_term false false e  in
        soft_parens_with_nesting uu____10941
    | FStar_Parser_AST.Let uu____10944 ->
        let uu____10965 = p_term false false e  in
        soft_parens_with_nesting uu____10965
    | FStar_Parser_AST.LetOpen uu____10968 ->
        let uu____10973 = p_term false false e  in
        soft_parens_with_nesting uu____10973
    | FStar_Parser_AST.Seq uu____10976 ->
        let uu____10981 = p_term false false e  in
        soft_parens_with_nesting uu____10981
    | FStar_Parser_AST.Bind uu____10984 ->
        let uu____10991 = p_term false false e  in
        soft_parens_with_nesting uu____10991
    | FStar_Parser_AST.If uu____10994 ->
        let uu____11001 = p_term false false e  in
        soft_parens_with_nesting uu____11001
    | FStar_Parser_AST.Match uu____11004 ->
        let uu____11019 = p_term false false e  in
        soft_parens_with_nesting uu____11019
    | FStar_Parser_AST.TryWith uu____11022 ->
        let uu____11037 = p_term false false e  in
        soft_parens_with_nesting uu____11037
    | FStar_Parser_AST.Ascribed uu____11040 ->
        let uu____11049 = p_term false false e  in
        soft_parens_with_nesting uu____11049
    | FStar_Parser_AST.Record uu____11052 ->
        let uu____11065 = p_term false false e  in
        soft_parens_with_nesting uu____11065
    | FStar_Parser_AST.Project uu____11068 ->
        let uu____11073 = p_term false false e  in
        soft_parens_with_nesting uu____11073
    | FStar_Parser_AST.Product uu____11076 ->
        let uu____11083 = p_term false false e  in
        soft_parens_with_nesting uu____11083
    | FStar_Parser_AST.Sum uu____11086 ->
        let uu____11097 = p_term false false e  in
        soft_parens_with_nesting uu____11097
    | FStar_Parser_AST.QForall uu____11100 ->
        let uu____11119 = p_term false false e  in
        soft_parens_with_nesting uu____11119
    | FStar_Parser_AST.QExists uu____11122 ->
        let uu____11141 = p_term false false e  in
        soft_parens_with_nesting uu____11141
    | FStar_Parser_AST.Refine uu____11144 ->
        let uu____11149 = p_term false false e  in
        soft_parens_with_nesting uu____11149
    | FStar_Parser_AST.NamedTyp uu____11152 ->
        let uu____11157 = p_term false false e  in
        soft_parens_with_nesting uu____11157
    | FStar_Parser_AST.Requires uu____11160 ->
        let uu____11168 = p_term false false e  in
        soft_parens_with_nesting uu____11168
    | FStar_Parser_AST.Ensures uu____11171 ->
        let uu____11179 = p_term false false e  in
        soft_parens_with_nesting uu____11179
    | FStar_Parser_AST.Attributes uu____11182 ->
        let uu____11185 = p_term false false e  in
        soft_parens_with_nesting uu____11185
    | FStar_Parser_AST.Quote uu____11188 ->
        let uu____11193 = p_term false false e  in
        soft_parens_with_nesting uu____11193
    | FStar_Parser_AST.VQuote uu____11196 ->
        let uu____11197 = p_term false false e  in
        soft_parens_with_nesting uu____11197
    | FStar_Parser_AST.Antiquote uu____11200 ->
        let uu____11201 = p_term false false e  in
        soft_parens_with_nesting uu____11201
    | FStar_Parser_AST.CalcProof uu____11204 ->
        let uu____11213 = p_term false false e  in
        soft_parens_with_nesting uu____11213

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11216  ->
    match uu___15_11216 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11228) ->
        let uu____11231 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11231
    | FStar_Const.Const_bytearray (bytes,uu____11233) ->
        let uu____11238 =
          let uu____11239 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11239  in
        let uu____11240 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11238 uu____11240
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_11263 =
          match uu___13_11263 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_11270 =
          match uu___14_11270 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11285  ->
               match uu____11285 with
               | (s,w) ->
                   let uu____11292 = signedness s  in
                   let uu____11293 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11292 uu____11293)
            sign_width_opt
           in
        let uu____11294 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11294 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11298 = FStar_Range.string_of_range r  in str uu____11298
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11302 = p_quident lid  in
        let uu____11303 =
          let uu____11304 =
            let uu____11305 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11305  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11304  in
        FStar_Pprint.op_Hat_Hat uu____11302 uu____11303

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11308 = str "u#"  in
    let uu____11310 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11308 uu____11310

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11312;_},u1::u2::[])
        ->
        let uu____11318 =
          let uu____11319 = p_universeFrom u1  in
          let uu____11320 =
            let uu____11321 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11321  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11319 uu____11320  in
        FStar_Pprint.group uu____11318
    | FStar_Parser_AST.App uu____11322 ->
        let uu____11329 = head_and_args u  in
        (match uu____11329 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11355 =
                    let uu____11356 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11357 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11365  ->
                           match uu____11365 with
                           | (u1,uu____11371) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11356 uu____11357  in
                  FStar_Pprint.group uu____11355
              | uu____11372 ->
                  let uu____11373 =
                    let uu____11375 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11375
                     in
                  failwith uu____11373))
    | uu____11378 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11404 = FStar_Ident.text_of_id id1  in str uu____11404
    | FStar_Parser_AST.Paren u1 ->
        let uu____11407 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11407
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11408;_},uu____11409::uu____11410::[])
        ->
        let uu____11414 = p_universeFrom u  in
        soft_parens_with_nesting uu____11414
    | FStar_Parser_AST.App uu____11415 ->
        let uu____11422 = p_universeFrom u  in
        soft_parens_with_nesting uu____11422
    | uu____11423 ->
        let uu____11424 =
          let uu____11426 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11426
           in
        failwith uu____11424

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
       | FStar_Parser_AST.Module (uu____11515,decls) ->
           let uu____11521 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11521
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11530,decls,uu____11532) ->
           let uu____11539 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11539
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11599  ->
         match uu____11599 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11621)) -> false
      | ([],uu____11625) -> false
      | uu____11629 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11639 -> true
         | uu____11641 -> false)
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
        | FStar_Parser_AST.Module (uu____11684,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11690,decls,uu____11692) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11744 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11757;
                 FStar_Parser_AST.doc = uu____11758;
                 FStar_Parser_AST.quals = uu____11759;
                 FStar_Parser_AST.attrs = uu____11760;_}::uu____11761 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11767 =
                   let uu____11770 =
                     let uu____11773 = FStar_List.tl ds  in d :: uu____11773
                      in
                   d0 :: uu____11770  in
                 (uu____11767, (d0.FStar_Parser_AST.drange))
             | uu____11778 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11744 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11835 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11835 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11944 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11944, comments1))))))
  