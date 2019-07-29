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
                let uu____6465 =
                  let uu____6466 = p_uident uid  in
                  let uu____6467 = p_binders true bs  in
                  let uu____6469 =
                    let uu____6470 = p_typ false false t  in
                    prefix2 FStar_Pprint.colon uu____6470  in
                  surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                    uu____6466 uu____6467 uu____6469
                   in
                FStar_Pprint.group uu____6465  in
              let uu____6475 =
                let uu____6476 = str "with"  in
                let uu____6478 =
                  let uu____6479 =
                    let uu____6480 =
                      let uu____6481 =
                        let uu____6482 =
                          let uu____6483 =
                            FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                              FStar_Pprint.space
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____6483
                           in
                        separate_map_last uu____6482 p_effectDecl eff_decls
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6481
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6480  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6479
                   in
                FStar_Pprint.op_Hat_Hat uu____6476 uu____6478  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6464 uu____6475  in
            braces_with_nesting uu____6463  in
          FStar_Pprint.op_Hat_Hat uu____6462 FStar_Pprint.hardline

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6487,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6520 =
            let uu____6521 = p_lident lid  in
            let uu____6522 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6521 uu____6522  in
          let uu____6523 = p_simpleTerm ps false e  in
          prefix2 uu____6520 uu____6523
      | uu____6525 ->
          let uu____6526 =
            let uu____6528 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6528
             in
          failwith uu____6526

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6611 =
        match uu____6611 with
        | (kwd,t) ->
            let uu____6622 =
              let uu____6623 = str kwd  in
              let uu____6624 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6623 uu____6624  in
            let uu____6625 = p_simpleTerm ps false t  in
            prefix2 uu____6622 uu____6625
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6632 =
      let uu____6633 =
        let uu____6634 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6635 =
          let uu____6636 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6636  in
        FStar_Pprint.op_Hat_Hat uu____6634 uu____6635  in
      let uu____6638 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6633 uu____6638  in
    let uu____6639 =
      let uu____6640 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6640  in
    FStar_Pprint.op_Hat_Hat uu____6632 uu____6639

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6641  ->
    match uu___8_6641 with
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
        let uu____6661 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6661 FStar_Pprint.hardline
    | uu____6662 ->
        let uu____6663 =
          let uu____6664 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6664  in
        FStar_Pprint.op_Hat_Hat uu____6663 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6667  ->
    match uu___9_6667 with
    | FStar_Parser_AST.Rec  ->
        let uu____6668 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6668
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6670  ->
    match uu___10_6670 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6675,e) -> e
          | uu____6681 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6682 = str "#["  in
        let uu____6684 =
          let uu____6685 = p_term false false t1  in
          let uu____6688 =
            let uu____6689 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6689 break1  in
          FStar_Pprint.op_Hat_Hat uu____6685 uu____6688  in
        FStar_Pprint.op_Hat_Hat uu____6682 uu____6684

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6695 =
          let uu____6696 =
            let uu____6697 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6697  in
          FStar_Pprint.separate_map uu____6696 p_tuplePattern pats  in
        FStar_Pprint.group uu____6695
    | uu____6698 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6707 =
          let uu____6708 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6708 p_constructorPattern pats  in
        FStar_Pprint.group uu____6707
    | uu____6709 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6712;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6717 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6718 = p_constructorPattern hd1  in
        let uu____6719 = p_constructorPattern tl1  in
        infix0 uu____6717 uu____6718 uu____6719
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6721;_},pats)
        ->
        let uu____6727 = p_quident uid  in
        let uu____6728 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6727 uu____6728
    | uu____6729 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6745;
               FStar_Parser_AST.blevel = uu____6746;
               FStar_Parser_AST.aqual = uu____6747;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6756 =
               let uu____6757 = p_ident lid  in
               p_refinement aqual uu____6757 t1 phi  in
             soft_parens_with_nesting uu____6756
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6760;
               FStar_Parser_AST.blevel = uu____6761;
               FStar_Parser_AST.aqual = uu____6762;_},phi))
             ->
             let uu____6768 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6768
         | uu____6769 ->
             let uu____6774 =
               let uu____6775 = p_tuplePattern pat  in
               let uu____6776 =
                 let uu____6777 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6777
                  in
               FStar_Pprint.op_Hat_Hat uu____6775 uu____6776  in
             soft_parens_with_nesting uu____6774)
    | FStar_Parser_AST.PatList pats ->
        let uu____6781 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6781 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6800 =
          match uu____6800 with
          | (lid,pat) ->
              let uu____6807 = p_qlident lid  in
              let uu____6808 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6807 uu____6808
           in
        let uu____6809 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6809
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6821 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6822 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6823 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6821
          uu____6822 uu____6823
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6834 =
          let uu____6835 =
            let uu____6836 =
              let uu____6837 = FStar_Ident.text_of_id op  in str uu____6837
               in
            let uu____6839 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6836 uu____6839  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6835  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6834
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6843 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6843 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6851 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6852 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6851 uu____6852
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6854 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6858;
           FStar_Parser_AST.prange = uu____6859;_},uu____6860)
        ->
        let uu____6865 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6865
    | FStar_Parser_AST.PatTuple (uu____6866,false ) ->
        let uu____6873 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6873
    | uu____6874 ->
        let uu____6875 =
          let uu____6877 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6877  in
        failwith uu____6875

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6882;_},uu____6883)
        -> true
    | uu____6890 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6896) -> true
    | uu____6898 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6905 = p_binder' is_atomic b  in
      match uu____6905 with
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
          let uu____6942 =
            let uu____6943 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6944 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6943 uu____6944  in
          (uu____6942, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6950 = p_lident lid  in
          (uu____6950, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6957 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6968;
                   FStar_Parser_AST.blevel = uu____6969;
                   FStar_Parser_AST.aqual = uu____6970;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6975 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6975 t1 phi
            | uu____6976 ->
                let t' =
                  let uu____6978 = is_typ_tuple t  in
                  if uu____6978
                  then
                    let uu____6981 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6981
                  else p_tmFormula t  in
                let uu____6984 =
                  let uu____6985 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6986 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6985 uu____6986  in
                (uu____6984, t')
             in
          (match uu____6957 with
           | (b',t') ->
               let catf =
                 let uu____7004 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7004
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7011 =
                         let uu____7012 =
                           let uu____7013 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7013
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7012
                          in
                       FStar_Pprint.group uu____7011
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7018 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7018)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7023 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7051;
                  FStar_Parser_AST.blevel = uu____7052;
                  FStar_Parser_AST.aqual = uu____7053;_},phi)
               ->
               let uu____7057 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7057 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7078 ->
               if is_atomic
               then
                 let uu____7090 = p_atomicTerm t  in
                 (uu____7090, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7097 = p_appTerm t  in
                  (uu____7097, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7108 = p_refinement' aqual_opt binder t phi  in
          match uu____7108 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7124 -> false
            | FStar_Parser_AST.App uu____7136 -> false
            | FStar_Parser_AST.Op uu____7144 -> false
            | uu____7152 -> true  in
          let uu____7154 = p_noSeqTerm false false phi  in
          match uu____7154 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7171 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7171)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____7180 =
                let uu____7181 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7181 binder  in
              let uu____7182 =
                let uu____7183 = p_appTerm t  in
                let uu____7184 =
                  let uu____7185 =
                    let uu____7186 =
                      let uu____7187 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7188 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7187 uu____7188  in
                    FStar_Pprint.group uu____7186  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____7185
                   in
                FStar_Pprint.op_Hat_Hat uu____7183 uu____7184  in
              (uu____7180, uu____7182)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7202 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7202

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7206 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7209 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7209)
       in
    if uu____7206
    then FStar_Pprint.underscore
    else (let uu____7214 = FStar_Ident.text_of_id lid  in str uu____7214)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7217 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7220 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7220)
       in
    if uu____7217
    then FStar_Pprint.underscore
    else (let uu____7225 = FStar_Ident.text_of_lid lid  in str uu____7225)

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
          let uu____7246 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7246
        else
          (let uu____7249 =
             let uu____7250 =
               let uu____7251 =
                 let uu____7252 =
                   let uu____7253 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7253  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7252  in
               FStar_Pprint.group uu____7251  in
             let uu____7254 =
               let uu____7255 =
                 let uu____7256 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7256  in
               FStar_Pprint.op_Hat_Hat comm uu____7255  in
             FStar_Pprint.ifflat uu____7250 uu____7254  in
           FStar_All.pipe_left FStar_Pprint.group uu____7249)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7264 = p_noSeqTerm true false e1  in
            (match uu____7264 with
             | (comm,t1) ->
                 let uu____7273 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7274 =
                   let uu____7275 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7275
                    in
                 FStar_Pprint.op_Hat_Hat uu____7273 uu____7274)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7279 =
              let uu____7280 =
                let uu____7281 =
                  let uu____7282 = p_lident x  in
                  let uu____7283 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7282 uu____7283  in
                let uu____7284 =
                  let uu____7285 = p_noSeqTermAndComment true false e1  in
                  let uu____7288 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7285 uu____7288  in
                op_Hat_Slash_Plus_Hat uu____7281 uu____7284  in
              FStar_Pprint.group uu____7280  in
            let uu____7289 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7279 uu____7289
        | uu____7290 ->
            let uu____7291 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7291

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
            let uu____7303 = p_noSeqTerm true false e1  in
            (match uu____7303 with
             | (comm,t1) ->
                 let uu____7316 =
                   let uu____7317 =
                     let uu____7318 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7318  in
                   let uu____7319 =
                     let uu____7320 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7320
                      in
                   FStar_Pprint.op_Hat_Hat uu____7317 uu____7319  in
                 (comm, uu____7316))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7324 =
              let uu____7325 =
                let uu____7326 =
                  let uu____7327 =
                    let uu____7328 = p_lident x  in
                    let uu____7329 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7328 uu____7329  in
                  let uu____7330 =
                    let uu____7331 = p_noSeqTermAndComment true false e1  in
                    let uu____7334 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7331 uu____7334  in
                  op_Hat_Slash_Plus_Hat uu____7327 uu____7330  in
                FStar_Pprint.group uu____7326  in
              let uu____7335 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7325 uu____7335  in
            (FStar_Pprint.empty, uu____7324)
        | uu____7336 -> p_noSeqTerm ps pb e

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
            let uu____7356 =
              let uu____7357 = p_tmIff e1  in
              let uu____7358 =
                let uu____7359 =
                  let uu____7360 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7360
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7359  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7357 uu____7358  in
            FStar_Pprint.group uu____7356
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7366 =
              let uu____7367 = p_tmIff e1  in
              let uu____7368 =
                let uu____7369 =
                  let uu____7370 =
                    let uu____7371 = p_typ false false t  in
                    let uu____7374 =
                      let uu____7375 = str "by"  in
                      let uu____7377 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7375 uu____7377  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7371 uu____7374  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7370
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7369  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7367 uu____7368  in
            FStar_Pprint.group uu____7366
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7378;_},e1::e2::e3::[])
            ->
            let uu____7385 =
              let uu____7386 =
                let uu____7387 =
                  let uu____7388 = p_atomicTermNotQUident e1  in
                  let uu____7389 =
                    let uu____7390 =
                      let uu____7391 =
                        let uu____7392 = p_term false false e2  in
                        soft_parens_with_nesting uu____7392  in
                      let uu____7395 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7391 uu____7395  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7390  in
                  FStar_Pprint.op_Hat_Hat uu____7388 uu____7389  in
                FStar_Pprint.group uu____7387  in
              let uu____7396 =
                let uu____7397 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7397  in
              FStar_Pprint.op_Hat_Hat uu____7386 uu____7396  in
            FStar_Pprint.group uu____7385
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7398;_},e1::e2::e3::[])
            ->
            let uu____7405 =
              let uu____7406 =
                let uu____7407 =
                  let uu____7408 = p_atomicTermNotQUident e1  in
                  let uu____7409 =
                    let uu____7410 =
                      let uu____7411 =
                        let uu____7412 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7412  in
                      let uu____7415 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7411 uu____7415  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7410  in
                  FStar_Pprint.op_Hat_Hat uu____7408 uu____7409  in
                FStar_Pprint.group uu____7407  in
              let uu____7416 =
                let uu____7417 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7417  in
              FStar_Pprint.op_Hat_Hat uu____7406 uu____7416  in
            FStar_Pprint.group uu____7405
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7427 =
              let uu____7428 = str "requires"  in
              let uu____7430 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7428 uu____7430  in
            FStar_Pprint.group uu____7427
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7440 =
              let uu____7441 = str "ensures"  in
              let uu____7443 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7441 uu____7443  in
            FStar_Pprint.group uu____7440
        | FStar_Parser_AST.Attributes es ->
            let uu____7447 =
              let uu____7448 = str "attributes"  in
              let uu____7450 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7448 uu____7450  in
            FStar_Pprint.group uu____7447
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7455 =
                let uu____7456 =
                  let uu____7457 = str "if"  in
                  let uu____7459 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7457 uu____7459  in
                let uu____7462 =
                  let uu____7463 = str "then"  in
                  let uu____7465 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7463 uu____7465  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7456 uu____7462  in
              FStar_Pprint.group uu____7455
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7469,uu____7470,e31) when
                     is_unit e31 ->
                     let uu____7472 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7472
                 | uu____7475 -> p_noSeqTermAndComment false false e2  in
               let uu____7478 =
                 let uu____7479 =
                   let uu____7480 = str "if"  in
                   let uu____7482 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7480 uu____7482  in
                 let uu____7485 =
                   let uu____7486 =
                     let uu____7487 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7487 e2_doc  in
                   let uu____7489 =
                     let uu____7490 = str "else"  in
                     let uu____7492 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7490 uu____7492  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7486 uu____7489  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7479 uu____7485  in
               FStar_Pprint.group uu____7478)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7515 =
              let uu____7516 =
                let uu____7517 =
                  let uu____7518 = str "try"  in
                  let uu____7520 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7518 uu____7520  in
                let uu____7523 =
                  let uu____7524 = str "with"  in
                  let uu____7526 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7524 uu____7526  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7517 uu____7523  in
              FStar_Pprint.group uu____7516  in
            let uu____7535 = paren_if (ps || pb)  in uu____7535 uu____7515
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7562 =
              let uu____7563 =
                let uu____7564 =
                  let uu____7565 = str "match"  in
                  let uu____7567 = p_noSeqTermAndComment false false e1  in
                  let uu____7570 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7565 uu____7567 uu____7570
                   in
                let uu____7574 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7564 uu____7574  in
              FStar_Pprint.group uu____7563  in
            let uu____7583 = paren_if (ps || pb)  in uu____7583 uu____7562
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7590 =
              let uu____7591 =
                let uu____7592 =
                  let uu____7593 = str "let open"  in
                  let uu____7595 = p_quident uid  in
                  let uu____7596 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7593 uu____7595 uu____7596
                   in
                let uu____7600 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7592 uu____7600  in
              FStar_Pprint.group uu____7591  in
            let uu____7602 = paren_if ps  in uu____7602 uu____7590
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7667 is_last =
              match uu____7667 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7701 =
                          let uu____7702 = str "let"  in
                          let uu____7704 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7702 uu____7704
                           in
                        FStar_Pprint.group uu____7701
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7707 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7713 = p_term_sep false false e2  in
                  (match uu____7713 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7723 =
                         if is_last
                         then
                           let uu____7725 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7726 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7725 doc_expr1 uu____7726
                         else
                           (let uu____7732 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7732)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7723)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7783 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7783
                     else
                       (let uu____7788 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7788)) lbs
               in
            let lbs_doc =
              let uu____7792 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7792  in
            let uu____7793 =
              let uu____7794 =
                let uu____7795 =
                  let uu____7796 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7796
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7795  in
              FStar_Pprint.group uu____7794  in
            let uu____7798 = paren_if ps  in uu____7798 uu____7793
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7805;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7808;
                                                             FStar_Parser_AST.level
                                                               = uu____7809;_})
            when matches_var maybe_x x ->
            let uu____7836 =
              let uu____7837 =
                let uu____7838 = str "function"  in
                let uu____7840 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7838 uu____7840  in
              FStar_Pprint.group uu____7837  in
            let uu____7849 = paren_if (ps || pb)  in uu____7849 uu____7836
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7855 =
              let uu____7856 = str "quote"  in
              let uu____7858 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7856 uu____7858  in
            FStar_Pprint.group uu____7855
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7860 =
              let uu____7861 = str "`"  in
              let uu____7863 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7861 uu____7863  in
            FStar_Pprint.group uu____7860
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7865 =
              let uu____7866 = str "`%"  in
              let uu____7868 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7866 uu____7868  in
            FStar_Pprint.group uu____7865
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7870;
              FStar_Parser_AST.level = uu____7871;_}
            ->
            let uu____7872 =
              let uu____7873 = str "`@"  in
              let uu____7875 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7873 uu____7875  in
            FStar_Pprint.group uu____7872
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7877 =
              let uu____7878 = str "`#"  in
              let uu____7880 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7878 uu____7880  in
            FStar_Pprint.group uu____7877
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7889 = str "calc"  in
              let uu____7891 =
                let uu____7892 =
                  let uu____7893 = p_noSeqTermAndComment false false rel  in
                  let uu____7896 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7893 uu____7896  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7892  in
              FStar_Pprint.op_Hat_Hat uu____7889 uu____7891  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7898 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7899 =
              let uu____7900 =
                let uu____7901 =
                  let uu____7902 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7905 =
                    let uu____7906 = str ";"  in
                    let uu____7908 =
                      let uu____7909 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7909
                       in
                    FStar_Pprint.op_Hat_Hat uu____7906 uu____7908  in
                  FStar_Pprint.op_Hat_Hat uu____7902 uu____7905  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7901  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7900
               in
            FStar_Pprint.enclose head1 uu____7898 uu____7899
        | uu____7911 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7912  ->
    fun uu____7913  ->
      match uu____7913 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7918 =
            let uu____7919 = p_noSeqTermAndComment false false rel  in
            let uu____7922 =
              let uu____7923 =
                let uu____7924 =
                  let uu____7925 =
                    let uu____7926 = p_noSeqTermAndComment false false just
                       in
                    let uu____7929 =
                      let uu____7930 =
                        let uu____7931 =
                          let uu____7932 =
                            let uu____7933 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7936 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7933 uu____7936  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7932
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7931
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7930
                       in
                    FStar_Pprint.op_Hat_Hat uu____7926 uu____7929  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7925  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7924  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7923  in
            FStar_Pprint.op_Hat_Hat uu____7919 uu____7922  in
          FStar_Pprint.group uu____7918

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7938  ->
    match uu___11_7938 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7950 =
          let uu____7951 = str "[@"  in
          let uu____7953 =
            let uu____7954 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7955 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7954 uu____7955  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7951 uu____7953  in
        FStar_Pprint.group uu____7950

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
        | FStar_Parser_AST.QForall (bs,(uu____7973,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8007 =
                   let uu____8008 =
                     let uu____8009 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8009 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8008 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8007 term_doc
             | pats ->
                 let uu____8017 =
                   let uu____8018 =
                     let uu____8019 =
                       let uu____8020 =
                         let uu____8021 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8021
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8020 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8024 = p_trigger trigger  in
                     prefix2 uu____8019 uu____8024  in
                   FStar_Pprint.group uu____8018  in
                 prefix2 uu____8017 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____8026,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8060 =
                   let uu____8061 =
                     let uu____8062 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8062 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8061 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8060 term_doc
             | pats ->
                 let uu____8070 =
                   let uu____8071 =
                     let uu____8072 =
                       let uu____8073 =
                         let uu____8074 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8074
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8073 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8077 = p_trigger trigger  in
                     prefix2 uu____8072 uu____8077  in
                   FStar_Pprint.group uu____8071  in
                 prefix2 uu____8070 term_doc)
        | uu____8078 -> p_simpleTerm ps pb e

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
      let uu____8099 = all_binders_annot t  in
      if uu____8099
      then
        let uu____8102 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8102
      else
        (let uu____8113 =
           let uu____8114 =
             let uu____8115 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8115  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8114  in
         FStar_Pprint.group uu____8113)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8174 = x  in
      match uu____8174 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8239 = hd1  in
               (match uu____8239 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8311 = cb  in
      match uu____8311 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8330 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8336 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8336) hd1 tl1
                  in
               cat_with_colon uu____8330 typ)
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
                 FStar_Parser_AST.brange = uu____8415;
                 FStar_Parser_AST.blevel = uu____8416;
                 FStar_Parser_AST.aqual = uu____8417;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8426 =
                 let uu____8431 = p_ident lid  in
                 p_refinement' aqual uu____8431 t1 phi  in
               FStar_Pervasives_Native.Some uu____8426
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8438) ->
               let uu____8443 =
                 let uu____8448 =
                   let uu____8449 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8450 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8449 uu____8450  in
                 let uu____8451 = p_tmEqNoRefinement t  in
                 (uu____8448, uu____8451)  in
               FStar_Pervasives_Native.Some uu____8443
           | uu____8456 -> FStar_Pervasives_Native.None)
      | uu____8465 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8478 -> false
      | uu____8490 -> true  in
    let uu____8492 = map_if_all all_binders pats  in
    match uu____8492 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8524 = collapse_pats bs  in
        (uu____8524, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8541 = FStar_List.map p_atomicPattern pats  in
        (uu____8541, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8553 -> str "forall"
    | FStar_Parser_AST.QExists uu____8573 -> str "exists"
    | uu____8593 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8595  ->
    match uu___12_8595 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8607 =
          let uu____8608 =
            let uu____8609 =
              let uu____8610 = str "pattern"  in
              let uu____8612 =
                let uu____8613 =
                  let uu____8614 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8614
                   in
                FStar_Pprint.op_Hat_Hat uu____8613 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8610 uu____8612  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8609  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8608  in
        FStar_Pprint.group uu____8607

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8622 = str "\\/"  in
    FStar_Pprint.separate_map uu____8622 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8629 =
      let uu____8630 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8630 p_appTerm pats  in
    FStar_Pprint.group uu____8629

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8642 = p_term_sep false pb e1  in
            (match uu____8642 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8651 = str "fun"  in
                   let uu____8653 =
                     let uu____8654 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8654
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8651 uu____8653  in
                 let uu____8655 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8657 =
                       let uu____8658 =
                         let uu____8659 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8659  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8658
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8657
                   else
                     (let uu____8662 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8662)
                    in
                 let uu____8663 = paren_if ps  in uu____8663 uu____8655)
        | uu____8668 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8676  ->
      match uu____8676 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8700 =
                    let uu____8701 =
                      let uu____8702 =
                        let uu____8703 = p_tuplePattern p  in
                        let uu____8704 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8703 uu____8704  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8702
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8701  in
                  FStar_Pprint.group uu____8700
              | FStar_Pervasives_Native.Some f ->
                  let uu____8706 =
                    let uu____8707 =
                      let uu____8708 =
                        let uu____8709 =
                          let uu____8710 =
                            let uu____8711 = p_tuplePattern p  in
                            let uu____8712 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8711
                              uu____8712
                             in
                          FStar_Pprint.group uu____8710  in
                        let uu____8714 =
                          let uu____8715 =
                            let uu____8718 = p_tmFormula f  in
                            [uu____8718; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8715  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8709 uu____8714
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8708
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8707  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8706
               in
            let uu____8720 = p_term_sep false pb e  in
            match uu____8720 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8730 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8730
                   else
                     (let uu____8733 =
                        let uu____8734 =
                          let uu____8735 =
                            let uu____8736 =
                              let uu____8737 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8737  in
                            op_Hat_Slash_Plus_Hat branch uu____8736  in
                          FStar_Pprint.group uu____8735  in
                        let uu____8738 =
                          let uu____8739 =
                            let uu____8740 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8740  in
                          FStar_Pprint.op_Hat_Hat branch uu____8739  in
                        FStar_Pprint.ifflat uu____8734 uu____8738  in
                      FStar_Pprint.group uu____8733))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8744 =
                       let uu____8745 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8745  in
                     op_Hat_Slash_Plus_Hat branch uu____8744)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8756 =
                      let uu____8757 =
                        let uu____8758 =
                          let uu____8759 =
                            let uu____8760 =
                              let uu____8761 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8761  in
                            FStar_Pprint.separate_map uu____8760
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8759
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8758
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8757  in
                    FStar_Pprint.group uu____8756
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8763 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8765;_},e1::e2::[])
        ->
        let uu____8771 = str "<==>"  in
        let uu____8773 = p_tmImplies e1  in
        let uu____8774 = p_tmIff e2  in
        infix0 uu____8771 uu____8773 uu____8774
    | uu____8775 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8777;_},e1::e2::[])
        ->
        let uu____8783 = str "==>"  in
        let uu____8785 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8791 = p_tmImplies e2  in
        infix0 uu____8783 uu____8785 uu____8791
    | uu____8792 ->
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
          let uu____8806 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8806 with
          | (terms',last1) ->
              let uu____8826 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8861 =
                      let uu____8862 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8862
                       in
                    let uu____8863 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8861, uu____8863)
                | Binders (n1,ln,parens1) ->
                    let uu____8877 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8885 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8877, break1, uu____8885)
                 in
              (match uu____8826 with
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
                    | _8918 when _8918 = Prims.int_one -> FStar_List.hd terms
                    | uu____8919 ->
                        let uu____8920 =
                          let uu____8921 =
                            let uu____8922 =
                              let uu____8923 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8924 =
                                let uu____8925 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8925
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8923 uu____8924
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8922  in
                          let uu____8926 =
                            let uu____8927 =
                              let uu____8928 =
                                let uu____8929 =
                                  let uu____8930 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8930  in
                                let uu____8931 =
                                  let uu____8932 =
                                    let uu____8933 =
                                      let uu____8934 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8935 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8941 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8941)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8934
                                        uu____8935
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8933
                                     in
                                  jump2 uu____8932  in
                                FStar_Pprint.ifflat uu____8929 uu____8931  in
                              FStar_Pprint.group uu____8928  in
                            let uu____8943 =
                              let uu____8944 =
                                let uu____8945 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8945  in
                              FStar_Pprint.align uu____8944  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8927
                              uu____8943
                             in
                          FStar_Pprint.ifflat uu____8921 uu____8926  in
                        FStar_Pprint.group uu____8920))

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
            | Arrows uu____8959 -> p_tmArrow' p_Tm e
            | Binders uu____8966 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8989 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8995 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8989 uu____8995
      | uu____8998 -> let uu____8999 = p_Tm e  in [uu____8999]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9052 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9078 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9052 uu____9078
        | uu____9101 ->
            let uu____9102 =
              let uu____9113 = p_Tm1 e1  in
              (uu____9113, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9102]
         in
      let fold_fun bs x =
        let uu____9211 = x  in
        match uu____9211 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9343 = hd1  in
                 (match uu____9343 with
                  | (b2s,t2,uu____9372) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9474 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9531 = cb  in
        match uu____9531 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9560 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9571 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9577 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9577) hd1 tl1
                         in
                      f uu____9571 typ))
         in
      let binders =
        let uu____9593 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9593  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9656 =
        let uu____9657 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9657 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9656  in
    let disj =
      let uu____9660 =
        let uu____9661 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9661 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9660  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9681;_},e1::e2::[])
        ->
        let uu____9687 = p_tmDisjunction e1  in
        let uu____9692 = let uu____9697 = p_tmConjunction e2  in [uu____9697]
           in
        FStar_List.append uu____9687 uu____9692
    | uu____9706 -> let uu____9707 = p_tmConjunction e  in [uu____9707]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9717;_},e1::e2::[])
        ->
        let uu____9723 = p_tmConjunction e1  in
        let uu____9726 = let uu____9729 = p_tmTuple e2  in [uu____9729]  in
        FStar_List.append uu____9723 uu____9726
    | uu____9730 -> let uu____9731 = p_tmTuple e  in [uu____9731]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9748 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9748
          (fun uu____9756  ->
             match uu____9756 with | (e1,uu____9762) -> p_tmEq e1) args
    | uu____9763 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9772 =
             let uu____9773 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9773  in
           FStar_Pprint.group uu____9772)

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
               (let uu____9792 = FStar_Ident.text_of_id op  in
                uu____9792 = "="))
              ||
              (let uu____9797 = FStar_Ident.text_of_id op  in
               uu____9797 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9803 = levels op1  in
            (match uu____9803 with
             | (left1,mine,right1) ->
                 let uu____9822 =
                   let uu____9823 = FStar_All.pipe_left str op1  in
                   let uu____9825 = p_tmEqWith' p_X left1 e1  in
                   let uu____9826 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9823 uu____9825 uu____9826  in
                 paren_if_gt curr mine uu____9822)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9827;_},e1::e2::[])
            ->
            let uu____9833 =
              let uu____9834 = p_tmEqWith p_X e1  in
              let uu____9835 =
                let uu____9836 =
                  let uu____9837 =
                    let uu____9838 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9838  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9837  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9836  in
              FStar_Pprint.op_Hat_Hat uu____9834 uu____9835  in
            FStar_Pprint.group uu____9833
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9839;_},e1::[])
            ->
            let uu____9844 = levels "-"  in
            (match uu____9844 with
             | (left1,mine,right1) ->
                 let uu____9864 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9864)
        | uu____9865 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9913)::(e2,uu____9915)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9935 = is_list e  in Prims.op_Negation uu____9935)
              ->
              let op = "::"  in
              let uu____9940 = levels op  in
              (match uu____9940 with
               | (left1,mine,right1) ->
                   let uu____9959 =
                     let uu____9960 = str op  in
                     let uu____9961 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9963 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9960 uu____9961 uu____9963  in
                   paren_if_gt curr mine uu____9959)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9982 = levels op  in
              (match uu____9982 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10016 = p_binder false b  in
                         let uu____10018 =
                           let uu____10019 =
                             let uu____10020 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10020 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10019
                            in
                         FStar_Pprint.op_Hat_Hat uu____10016 uu____10018
                     | FStar_Util.Inr t ->
                         let uu____10022 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10024 =
                           let uu____10025 =
                             let uu____10026 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10026 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10025
                            in
                         FStar_Pprint.op_Hat_Hat uu____10022 uu____10024
                      in
                   let uu____10027 =
                     let uu____10028 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10033 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10028 uu____10033  in
                   paren_if_gt curr mine uu____10027)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10035;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10065 = levels op  in
              (match uu____10065 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10085 = str op  in
                     let uu____10086 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10088 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10085 uu____10086 uu____10088
                   else
                     (let uu____10092 =
                        let uu____10093 = str op  in
                        let uu____10094 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10096 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10093 uu____10094 uu____10096  in
                      paren_if_gt curr mine uu____10092))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10105 = levels op1  in
              (match uu____10105 with
               | (left1,mine,right1) ->
                   let uu____10124 =
                     let uu____10125 = str op1  in
                     let uu____10126 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10128 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10125 uu____10126 uu____10128  in
                   paren_if_gt curr mine uu____10124)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10148 =
                let uu____10149 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10150 =
                  let uu____10151 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10151 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10149 uu____10150  in
              braces_with_nesting uu____10148
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10156;_},e1::[])
              ->
              let uu____10161 =
                let uu____10162 = str "~"  in
                let uu____10164 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10162 uu____10164  in
              FStar_Pprint.group uu____10161
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10166;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10175 = levels op  in
                   (match uu____10175 with
                    | (left1,mine,right1) ->
                        let uu____10194 =
                          let uu____10195 = str op  in
                          let uu____10196 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10198 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10195 uu____10196 uu____10198  in
                        paren_if_gt curr mine uu____10194)
               | uu____10200 -> p_X e)
          | uu____10201 -> p_X e

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
        let uu____10208 =
          let uu____10209 = p_lident lid  in
          let uu____10210 =
            let uu____10211 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10211  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10209 uu____10210  in
        FStar_Pprint.group uu____10208
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10214 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10216 = p_appTerm e  in
    let uu____10217 =
      let uu____10218 =
        let uu____10219 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10219 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10218  in
    FStar_Pprint.op_Hat_Hat uu____10216 uu____10217

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10225 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10225 t phi
      | FStar_Parser_AST.TAnnotated uu____10226 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10232 ->
          let uu____10233 =
            let uu____10235 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10235
             in
          failwith uu____10233
      | FStar_Parser_AST.TVariable uu____10238 ->
          let uu____10239 =
            let uu____10241 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10241
             in
          failwith uu____10239
      | FStar_Parser_AST.NoName uu____10244 ->
          let uu____10245 =
            let uu____10247 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10247
             in
          failwith uu____10245

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10251  ->
      match uu____10251 with
      | (lid,e) ->
          let uu____10259 =
            let uu____10260 = p_qlident lid  in
            let uu____10261 =
              let uu____10262 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10262
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10260 uu____10261  in
          FStar_Pprint.group uu____10259

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10265 when is_general_application e ->
        let uu____10272 = head_and_args e  in
        (match uu____10272 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10319 = p_argTerm e1  in
                  let uu____10320 =
                    let uu____10321 =
                      let uu____10322 =
                        let uu____10323 = str "`"  in
                        let uu____10325 =
                          let uu____10326 = p_indexingTerm head1  in
                          let uu____10327 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10326 uu____10327  in
                        FStar_Pprint.op_Hat_Hat uu____10323 uu____10325  in
                      FStar_Pprint.group uu____10322  in
                    let uu____10329 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10321 uu____10329  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10319 uu____10320
              | uu____10330 ->
                  let uu____10337 =
                    let uu____10348 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10348
                    then
                      let uu____10382 =
                        FStar_Util.take
                          (fun uu____10406  ->
                             match uu____10406 with
                             | (uu____10412,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10382 with
                      | (fs_typ_args,args1) ->
                          let uu____10450 =
                            let uu____10451 = p_indexingTerm head1  in
                            let uu____10452 =
                              let uu____10453 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10453
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10451 uu____10452
                             in
                          (uu____10450, args1)
                    else
                      (let uu____10468 = p_indexingTerm head1  in
                       (uu____10468, args))
                     in
                  (match uu____10337 with
                   | (head_doc,args1) ->
                       let uu____10489 =
                         let uu____10490 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10490 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10489)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10512 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10512)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10531 =
               let uu____10532 = p_quident lid  in
               let uu____10533 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10532 uu____10533  in
             FStar_Pprint.group uu____10531
         | hd1::tl1 ->
             let uu____10550 =
               let uu____10551 =
                 let uu____10552 =
                   let uu____10553 = p_quident lid  in
                   let uu____10554 = p_argTerm hd1  in
                   prefix2 uu____10553 uu____10554  in
                 FStar_Pprint.group uu____10552  in
               let uu____10555 =
                 let uu____10556 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10556  in
               FStar_Pprint.op_Hat_Hat uu____10551 uu____10555  in
             FStar_Pprint.group uu____10550)
    | uu____10561 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10572 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10572 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10576 = str "#"  in
        let uu____10578 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10576 uu____10578
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10581 = str "#["  in
        let uu____10583 =
          let uu____10584 = p_indexingTerm t  in
          let uu____10585 =
            let uu____10586 = str "]"  in
            let uu____10588 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10586 uu____10588  in
          FStar_Pprint.op_Hat_Hat uu____10584 uu____10585  in
        FStar_Pprint.op_Hat_Hat uu____10581 uu____10583
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10591  ->
    match uu____10591 with | (e,uu____10597) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10602;_},e1::e2::[])
          ->
          let uu____10608 =
            let uu____10609 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10610 =
              let uu____10611 =
                let uu____10612 = p_term false false e2  in
                soft_parens_with_nesting uu____10612  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10611  in
            FStar_Pprint.op_Hat_Hat uu____10609 uu____10610  in
          FStar_Pprint.group uu____10608
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10615;_},e1::e2::[])
          ->
          let uu____10621 =
            let uu____10622 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10623 =
              let uu____10624 =
                let uu____10625 = p_term false false e2  in
                soft_brackets_with_nesting uu____10625  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10624  in
            FStar_Pprint.op_Hat_Hat uu____10622 uu____10623  in
          FStar_Pprint.group uu____10621
      | uu____10628 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10633 = p_quident lid  in
        let uu____10634 =
          let uu____10635 =
            let uu____10636 = p_term false false e1  in
            soft_parens_with_nesting uu____10636  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10635  in
        FStar_Pprint.op_Hat_Hat uu____10633 uu____10634
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10644 =
          let uu____10645 = FStar_Ident.text_of_id op  in str uu____10645  in
        let uu____10647 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10644 uu____10647
    | uu____10648 -> p_atomicTermNotQUident e

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
         | uu____10661 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10670 =
          let uu____10671 = FStar_Ident.text_of_id op  in str uu____10671  in
        let uu____10673 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10670 uu____10673
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10677 =
          let uu____10678 =
            let uu____10679 =
              let uu____10680 = FStar_Ident.text_of_id op  in str uu____10680
               in
            let uu____10682 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10679 uu____10682  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10678  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10677
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10697 = all_explicit args  in
        if uu____10697
        then
          let uu____10700 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10701 =
            let uu____10702 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10703 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10702 p_tmEq uu____10703  in
          let uu____10710 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10700
            uu____10701 uu____10710
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10732 =
                 let uu____10733 = p_quident lid  in
                 let uu____10734 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10733 uu____10734  in
               FStar_Pprint.group uu____10732
           | hd1::tl1 ->
               let uu____10751 =
                 let uu____10752 =
                   let uu____10753 =
                     let uu____10754 = p_quident lid  in
                     let uu____10755 = p_argTerm hd1  in
                     prefix2 uu____10754 uu____10755  in
                   FStar_Pprint.group uu____10753  in
                 let uu____10756 =
                   let uu____10757 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10757  in
                 FStar_Pprint.op_Hat_Hat uu____10752 uu____10756  in
               FStar_Pprint.group uu____10751)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10764 =
          let uu____10765 = p_atomicTermNotQUident e1  in
          let uu____10766 =
            let uu____10767 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10767  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10765
            uu____10766
           in
        FStar_Pprint.group uu____10764
    | uu____10770 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10775 = p_quident constr_lid  in
        let uu____10776 =
          let uu____10777 =
            let uu____10778 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10778  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10777  in
        FStar_Pprint.op_Hat_Hat uu____10775 uu____10776
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10780 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10780 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10782 = p_term_sep false false e1  in
        (match uu____10782 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10795 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10795))
    | uu____10796 when is_array e ->
        let es = extract_from_list e  in
        let uu____10800 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10801 =
          let uu____10802 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10802
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10807 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10800
          uu____10801 uu____10807
    | uu____10810 when is_list e ->
        let uu____10811 =
          let uu____10812 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10813 = extract_from_list e  in
          separate_map_or_flow_last uu____10812
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10813
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10811 FStar_Pprint.rbracket
    | uu____10822 when is_lex_list e ->
        let uu____10823 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10824 =
          let uu____10825 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10826 = extract_from_list e  in
          separate_map_or_flow_last uu____10825
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10826
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10823
          uu____10824 FStar_Pprint.rbracket
    | uu____10835 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10839 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10840 =
          let uu____10841 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10841 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10839
          uu____10840 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10851 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10854 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10851 uu____10854
    | FStar_Parser_AST.Op (op,args) when
        let uu____10863 = handleable_op op args  in
        Prims.op_Negation uu____10863 ->
        let uu____10865 =
          let uu____10867 =
            let uu____10869 = FStar_Ident.text_of_id op  in
            let uu____10871 =
              let uu____10873 =
                let uu____10875 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10875
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10873  in
            Prims.op_Hat uu____10869 uu____10871  in
          Prims.op_Hat "Operation " uu____10867  in
        failwith uu____10865
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10882 = p_term false false e  in
        soft_parens_with_nesting uu____10882
    | FStar_Parser_AST.Const uu____10885 ->
        let uu____10886 = p_term false false e  in
        soft_parens_with_nesting uu____10886
    | FStar_Parser_AST.Op uu____10889 ->
        let uu____10896 = p_term false false e  in
        soft_parens_with_nesting uu____10896
    | FStar_Parser_AST.Tvar uu____10899 ->
        let uu____10900 = p_term false false e  in
        soft_parens_with_nesting uu____10900
    | FStar_Parser_AST.Var uu____10903 ->
        let uu____10904 = p_term false false e  in
        soft_parens_with_nesting uu____10904
    | FStar_Parser_AST.Name uu____10907 ->
        let uu____10908 = p_term false false e  in
        soft_parens_with_nesting uu____10908
    | FStar_Parser_AST.Construct uu____10911 ->
        let uu____10922 = p_term false false e  in
        soft_parens_with_nesting uu____10922
    | FStar_Parser_AST.Abs uu____10925 ->
        let uu____10932 = p_term false false e  in
        soft_parens_with_nesting uu____10932
    | FStar_Parser_AST.App uu____10935 ->
        let uu____10942 = p_term false false e  in
        soft_parens_with_nesting uu____10942
    | FStar_Parser_AST.Let uu____10945 ->
        let uu____10966 = p_term false false e  in
        soft_parens_with_nesting uu____10966
    | FStar_Parser_AST.LetOpen uu____10969 ->
        let uu____10974 = p_term false false e  in
        soft_parens_with_nesting uu____10974
    | FStar_Parser_AST.Seq uu____10977 ->
        let uu____10982 = p_term false false e  in
        soft_parens_with_nesting uu____10982
    | FStar_Parser_AST.Bind uu____10985 ->
        let uu____10992 = p_term false false e  in
        soft_parens_with_nesting uu____10992
    | FStar_Parser_AST.If uu____10995 ->
        let uu____11002 = p_term false false e  in
        soft_parens_with_nesting uu____11002
    | FStar_Parser_AST.Match uu____11005 ->
        let uu____11020 = p_term false false e  in
        soft_parens_with_nesting uu____11020
    | FStar_Parser_AST.TryWith uu____11023 ->
        let uu____11038 = p_term false false e  in
        soft_parens_with_nesting uu____11038
    | FStar_Parser_AST.Ascribed uu____11041 ->
        let uu____11050 = p_term false false e  in
        soft_parens_with_nesting uu____11050
    | FStar_Parser_AST.Record uu____11053 ->
        let uu____11066 = p_term false false e  in
        soft_parens_with_nesting uu____11066
    | FStar_Parser_AST.Project uu____11069 ->
        let uu____11074 = p_term false false e  in
        soft_parens_with_nesting uu____11074
    | FStar_Parser_AST.Product uu____11077 ->
        let uu____11084 = p_term false false e  in
        soft_parens_with_nesting uu____11084
    | FStar_Parser_AST.Sum uu____11087 ->
        let uu____11098 = p_term false false e  in
        soft_parens_with_nesting uu____11098
    | FStar_Parser_AST.QForall uu____11101 ->
        let uu____11120 = p_term false false e  in
        soft_parens_with_nesting uu____11120
    | FStar_Parser_AST.QExists uu____11123 ->
        let uu____11142 = p_term false false e  in
        soft_parens_with_nesting uu____11142
    | FStar_Parser_AST.Refine uu____11145 ->
        let uu____11150 = p_term false false e  in
        soft_parens_with_nesting uu____11150
    | FStar_Parser_AST.NamedTyp uu____11153 ->
        let uu____11158 = p_term false false e  in
        soft_parens_with_nesting uu____11158
    | FStar_Parser_AST.Requires uu____11161 ->
        let uu____11169 = p_term false false e  in
        soft_parens_with_nesting uu____11169
    | FStar_Parser_AST.Ensures uu____11172 ->
        let uu____11180 = p_term false false e  in
        soft_parens_with_nesting uu____11180
    | FStar_Parser_AST.Attributes uu____11183 ->
        let uu____11186 = p_term false false e  in
        soft_parens_with_nesting uu____11186
    | FStar_Parser_AST.Quote uu____11189 ->
        let uu____11194 = p_term false false e  in
        soft_parens_with_nesting uu____11194
    | FStar_Parser_AST.VQuote uu____11197 ->
        let uu____11198 = p_term false false e  in
        soft_parens_with_nesting uu____11198
    | FStar_Parser_AST.Antiquote uu____11201 ->
        let uu____11202 = p_term false false e  in
        soft_parens_with_nesting uu____11202
    | FStar_Parser_AST.CalcProof uu____11205 ->
        let uu____11214 = p_term false false e  in
        soft_parens_with_nesting uu____11214

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11217  ->
    match uu___15_11217 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11229) ->
        let uu____11232 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11232
    | FStar_Const.Const_bytearray (bytes,uu____11234) ->
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
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11836 dummy_meta FStar_Pprint.empty false true
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
  