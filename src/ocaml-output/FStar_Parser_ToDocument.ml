open Prims
let (maybe_unthunk : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Abs (uu____10::[],body) -> body
    | uu____14 -> t
  
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
            let uu____114 = let uu____117 = f x  in uu____117 :: acc  in
            aux xs uu____114
         in
      aux l []
  
let map_if_all :
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
            let uu____183 = f x  in
            (match uu____183 with
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
          let uu____239 = f x  in if uu____239 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___0_272  ->
         match uu___0_272 with
         | (uu____278,FStar_Parser_AST.Nothing ) -> true
         | uu____280 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____309 'Auu____310 .
    Prims.bool -> ('Auu____309 -> 'Auu____310) -> 'Auu____309 -> 'Auu____310
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
  'Auu____420 'Auu____421 .
    'Auu____420 ->
      ('Auu____421 -> 'Auu____420) ->
        'Auu____421 FStar_Pervasives_Native.option -> 'Auu____420
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
  'Auu____534 .
    FStar_Pprint.document ->
      ('Auu____534 -> FStar_Pprint.document) ->
        'Auu____534 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____559 =
          let uu____560 =
            let uu____561 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____561  in
          FStar_Pprint.separate_map uu____560 f l  in
        FStar_Pprint.group uu____559
  
let precede_break_separate_map :
  'Auu____573 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____573 -> FStar_Pprint.document) ->
          'Auu____573 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____603 =
            let uu____604 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____605 =
              let uu____606 = FStar_List.hd l  in
              FStar_All.pipe_right uu____606 f  in
            FStar_Pprint.precede uu____604 uu____605  in
          let uu____607 =
            let uu____608 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____614 =
                   let uu____615 =
                     let uu____616 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____616  in
                   FStar_Pprint.op_Hat_Hat sep uu____615  in
                 FStar_Pprint.op_Hat_Hat break1 uu____614) uu____608
             in
          FStar_Pprint.op_Hat_Hat uu____603 uu____607
  
let concat_break_map :
  'Auu____624 .
    ('Auu____624 -> FStar_Pprint.document) ->
      'Auu____624 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____644 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____648 = f x  in FStar_Pprint.op_Hat_Hat uu____648 break1)
          l
         in
      FStar_Pprint.group uu____644
  
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
    let uu____711 = str "begin"  in
    let uu____713 = str "end"  in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____711
      contents uu____713
  
let separate_map_last :
  'Auu____726 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____726 -> FStar_Pprint.document) ->
        'Auu____726 Prims.list -> FStar_Pprint.document
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
  'Auu____778 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____778 -> FStar_Pprint.document) ->
        'Auu____778 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____810 =
          let uu____811 =
            let uu____812 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____812  in
          separate_map_last uu____811 f l  in
        FStar_Pprint.group uu____810
  
let separate_map_or_flow :
  'Auu____822 .
    FStar_Pprint.document ->
      ('Auu____822 -> FStar_Pprint.document) ->
        'Auu____822 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____860 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____860 -> FStar_Pprint.document) ->
        'Auu____860 Prims.list -> FStar_Pprint.document
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
  'Auu____912 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____912 -> FStar_Pprint.document) ->
        'Auu____912 Prims.list -> FStar_Pprint.document
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
              let uu____994 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____994
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1016 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1016 -> FStar_Pprint.document) ->
                  'Auu____1016 Prims.list -> FStar_Pprint.document
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
                    (let uu____1075 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1075
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1095 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1095 -> FStar_Pprint.document) ->
                  'Auu____1095 Prims.list -> FStar_Pprint.document
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
                    (let uu____1154 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1154
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1173  ->
    match uu____1173 with
    | (comment,keywords) ->
        let uu____1207 =
          let uu____1208 =
            let uu____1211 = str comment  in
            let uu____1212 =
              let uu____1215 =
                let uu____1218 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1229  ->
                       match uu____1229 with
                       | (k,v1) ->
                           let uu____1242 =
                             let uu____1245 = str k  in
                             let uu____1246 =
                               let uu____1249 =
                                 let uu____1252 = str v1  in [uu____1252]  in
                               FStar_Pprint.rarrow :: uu____1249  in
                             uu____1245 :: uu____1246  in
                           FStar_Pprint.concat uu____1242) keywords
                   in
                [uu____1218]  in
              FStar_Pprint.space :: uu____1215  in
            uu____1211 :: uu____1212  in
          FStar_Pprint.concat uu____1208  in
        FStar_Pprint.group uu____1207
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1262 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1278 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1278
      | uu____1281 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1332::(e2,uu____1334)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1357 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1381,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1392,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1413 = extract_from_list e2  in e1 :: uu____1413
    | uu____1416 ->
        let uu____1417 =
          let uu____1419 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1419  in
        failwith uu____1417
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1433;
           FStar_Parser_AST.level = uu____1434;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1436 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1448;
           FStar_Parser_AST.level = uu____1449;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1451;
                                                         FStar_Parser_AST.level
                                                           = uu____1452;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1454;
                                                    FStar_Parser_AST.level =
                                                      uu____1455;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1457;
                FStar_Parser_AST.level = uu____1458;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1460;
           FStar_Parser_AST.level = uu____1461;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1463 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1475 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1476;
           FStar_Parser_AST.range = uu____1477;
           FStar_Parser_AST.level = uu____1478;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1479;
                                                         FStar_Parser_AST.range
                                                           = uu____1480;
                                                         FStar_Parser_AST.level
                                                           = uu____1481;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1483;
                                                    FStar_Parser_AST.level =
                                                      uu____1484;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1485;
                FStar_Parser_AST.range = uu____1486;
                FStar_Parser_AST.level = uu____1487;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1489;
           FStar_Parser_AST.level = uu____1490;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1492 = extract_from_ref_set e1  in
        let uu____1495 = extract_from_ref_set e2  in
        FStar_List.append uu____1492 uu____1495
    | uu____1498 ->
        let uu____1499 =
          let uu____1501 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1501  in
        failwith uu____1499
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1513 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1513
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1522 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1522
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1533 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1533 Prims.int_zero  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1543 = FStar_Ident.text_of_id op  in uu____1543 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1613 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1633 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1644 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1655 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1681  ->
    match uu___1_1681 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1716  ->
      match uu___2_1716 with
      | FStar_Util.Inl c ->
          let uu____1729 = FStar_String.get s Prims.int_zero  in
          uu____1729 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1745 .
    Prims.string ->
      ('Auu____1745 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1769  ->
      match uu____1769 with
      | (assoc_levels,tokens) ->
          let uu____1801 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1801 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_1973 =
    match uu___3_1973 with
    | Left  -> (l, l, (l - Prims.int_one))
    | Right  -> ((l - Prims.int_one), l, l)
    | NonAssoc  -> ((l - Prims.int_one), l, (l - Prims.int_one))  in
  FStar_List.mapi
    (fun i  ->
       fun uu____2023  ->
         match uu____2023 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2098 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2098 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2150) ->
          assoc_levels
      | uu____2188 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2221 . ('Auu____2221 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2270 =
        FStar_List.tryFind
          (fun uu____2306  ->
             match uu____2306 with
             | (uu____2323,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2270 with
      | FStar_Pervasives_Native.Some ((uu____2352,l1,uu____2354),uu____2355)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2405 =
            let uu____2407 =
              let uu____2409 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2409  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2407
             in
          failwith uu____2405
       in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2444 = assign_levels level_associativity_spec op  in
    match uu____2444 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - Prims.int_one), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2503 =
      let uu____2506 =
        let uu____2512 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2512  in
      FStar_List.tryFind uu____2506 operatorInfix0ad12  in
    uu____2503 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2579 =
      let uu____2594 =
        let uu____2612 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2612  in
      FStar_List.tryFind uu____2594 opinfix34  in
    uu____2579 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2678 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2678
    then Prims.int_one
    else
      (let uu____2691 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2691
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
  
let handleable_op :
  'Auu____2737 . FStar_Ident.ident -> 'Auu____2737 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2753 when _2753 = Prims.int_zero -> true
      | _2755 when _2755 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2757 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2757 ["-"; "~"])
      | _2765 when _2765 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2767 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2767
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2789 when _2789 = (Prims.of_int (3)) ->
          let uu____2790 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2790 [".()<-"; ".[]<-"]
      | uu____2798 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2844 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2896 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2938 -> true
      | uu____2944 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2977 = FStar_List.for_all is_binder_annot bs  in
          if uu____2977
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2992 -> (true, (l + Prims.int_one))  in
    let uu____2997 = all_binders e Prims.int_zero  in
    match uu____2997 with
    | (b,l) -> if b && (l > Prims.int_one) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3036 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3036
  
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
  'Auu____3185 .
    ('Auu____3185 -> FStar_Pprint.document) ->
      'Auu____3185 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3227 = FStar_ST.op_Bang comment_stack  in
          match uu____3227 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3298 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3298 FStar_Pprint.hardline  in
              let uu____3299 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3299
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3341 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3341 print_pos lookahead_pos))
              else
                (let uu____3344 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3344))
           in
        let uu____3347 =
          let uu____3353 =
            let uu____3354 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3354  in
          let uu____3355 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3353 uu____3355  in
        match uu____3347 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3364 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3364
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3376 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3376)
  
let with_comment_sep :
  'Auu____3388 'Auu____3389 .
    ('Auu____3388 -> 'Auu____3389) ->
      'Auu____3388 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3389)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3435 = FStar_ST.op_Bang comment_stack  in
          match uu____3435 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3506 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3506
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3548 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3552 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3552)
                     in
                  comments_before_pos uu____3548 print_pos lookahead_pos))
              else
                (let uu____3555 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3555))
           in
        let uu____3558 =
          let uu____3564 =
            let uu____3565 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3565  in
          let uu____3566 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3564 uu____3566  in
        match uu____3558 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3579 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3579
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
                let uu____3632 = FStar_ST.op_Bang comment_stack  in
                match uu____3632 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3726 =
                          let uu____3728 =
                            let uu____3730 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3730  in
                          uu____3728 - lbegin  in
                        max k uu____3726  in
                      let lnum1 = min (Prims.of_int (2)) lnum  in
                      let doc2 =
                        let uu____3735 =
                          let uu____3736 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3737 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3736 uu____3737  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3735  in
                      let uu____3738 =
                        let uu____3740 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3740  in
                      place_comments_until_pos Prims.int_one uu____3738 pos
                        meta_decl doc2 true init1))
                | uu____3743 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3756 = FStar_Range.line_of_pos pos  in
                         uu____3756 - lbegin  in
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
                       let uu____3798 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3798)
  
let separate_map_with_comments :
  'Auu____3812 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3812 -> FStar_Pprint.document) ->
          'Auu____3812 Prims.list ->
            ('Auu____3812 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3871 x =
              match uu____3871 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3890 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3890 meta_decl doc1 false false
                     in
                  let uu____3894 =
                    let uu____3896 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3896  in
                  let uu____3897 =
                    let uu____3898 =
                      let uu____3899 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3899  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3898  in
                  (uu____3894, uu____3897)
               in
            let uu____3901 =
              let uu____3908 = FStar_List.hd xs  in
              let uu____3909 = FStar_List.tl xs  in (uu____3908, uu____3909)
               in
            match uu____3901 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3927 =
                    let uu____3929 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3929  in
                  let uu____3930 =
                    let uu____3931 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3931  in
                  (uu____3927, uu____3930)  in
                let uu____3933 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3933
  
let separate_map_with_comments_kw :
  'Auu____3960 'Auu____3961 .
    'Auu____3960 ->
      'Auu____3960 ->
        ('Auu____3960 -> 'Auu____3961 -> FStar_Pprint.document) ->
          'Auu____3961 Prims.list ->
            ('Auu____3961 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4025 x =
              match uu____4025 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4044 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____4044 meta_decl doc1 false false
                     in
                  let uu____4048 =
                    let uu____4050 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4050  in
                  let uu____4051 =
                    let uu____4052 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4052  in
                  (uu____4048, uu____4051)
               in
            let uu____4054 =
              let uu____4061 = FStar_List.hd xs  in
              let uu____4062 = FStar_List.tl xs  in (uu____4061, uu____4062)
               in
            match uu____4054 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4080 =
                    let uu____4082 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4082  in
                  let uu____4083 = f prefix1 x  in (uu____4080, uu____4083)
                   in
                let uu____4085 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4085
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5071)) ->
          let uu____5074 =
            let uu____5076 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5076 FStar_Util.is_upper  in
          if uu____5074
          then
            let uu____5082 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5082 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5085 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5092 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5095 =
      let uu____5096 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5097 =
        let uu____5098 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5098  in
      FStar_Pprint.op_Hat_Hat uu____5096 uu____5097  in
    FStar_Pprint.op_Hat_Hat uu____5092 uu____5095

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5100 ->
        let uu____5101 =
          let uu____5102 = str "@ "  in
          let uu____5104 =
            let uu____5105 =
              let uu____5106 =
                let uu____5107 =
                  let uu____5108 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5108  in
                FStar_Pprint.op_Hat_Hat uu____5107 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5106  in
            FStar_Pprint.op_Hat_Hat uu____5105 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5102 uu____5104  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5101

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5111  ->
    match uu____5111 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5159 =
                match uu____5159 with
                | (kwd,arg) ->
                    let uu____5172 = str "@"  in
                    let uu____5174 =
                      let uu____5175 = str kwd  in
                      let uu____5176 =
                        let uu____5177 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5177
                         in
                      FStar_Pprint.op_Hat_Hat uu____5175 uu____5176  in
                    FStar_Pprint.op_Hat_Hat uu____5172 uu____5174
                 in
              let uu____5178 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5178 FStar_Pprint.hardline
           in
        let uu____5185 =
          let uu____5186 =
            let uu____5187 =
              let uu____5188 = str doc1  in
              let uu____5189 =
                let uu____5190 =
                  let uu____5191 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5191  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5190  in
              FStar_Pprint.op_Hat_Hat uu____5188 uu____5189  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5187  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5186  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5185

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5195 =
          let uu____5196 = str "val"  in
          let uu____5198 =
            let uu____5199 =
              let uu____5200 = p_lident lid  in
              let uu____5201 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5200 uu____5201  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5199  in
          FStar_Pprint.op_Hat_Hat uu____5196 uu____5198  in
        let uu____5202 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5195 uu____5202
    | FStar_Parser_AST.TopLevelLet (uu____5205,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5230 =
               let uu____5231 = str "let"  in p_letlhs uu____5231 lb false
                in
             FStar_Pprint.group uu____5230) lbs
    | uu____5234 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_5249 =
          match uu___4_5249 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5257 = f x  in
              let uu____5258 =
                let uu____5259 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5259  in
              FStar_Pprint.op_Hat_Hat uu____5257 uu____5258
           in
        let uu____5260 = str "["  in
        let uu____5262 =
          let uu____5263 = p_list' l  in
          let uu____5264 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5263 uu____5264  in
        FStar_Pprint.op_Hat_Hat uu____5260 uu____5262

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5268 =
          let uu____5269 = str "open"  in
          let uu____5271 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5269 uu____5271  in
        FStar_Pprint.group uu____5268
    | FStar_Parser_AST.Include uid ->
        let uu____5273 =
          let uu____5274 = str "include"  in
          let uu____5276 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5274 uu____5276  in
        FStar_Pprint.group uu____5273
    | FStar_Parser_AST.Friend uid ->
        let uu____5278 =
          let uu____5279 = str "friend"  in
          let uu____5281 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5279 uu____5281  in
        FStar_Pprint.group uu____5278
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5284 =
          let uu____5285 = str "module"  in
          let uu____5287 =
            let uu____5288 =
              let uu____5289 = p_uident uid1  in
              let uu____5290 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5289 uu____5290  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5288  in
          FStar_Pprint.op_Hat_Hat uu____5285 uu____5287  in
        let uu____5291 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5284 uu____5291
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5293 =
          let uu____5294 = str "module"  in
          let uu____5296 =
            let uu____5297 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5297  in
          FStar_Pprint.op_Hat_Hat uu____5294 uu____5296  in
        FStar_Pprint.group uu____5293
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5298,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5335 = str "effect"  in
          let uu____5337 =
            let uu____5338 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5338  in
          FStar_Pprint.op_Hat_Hat uu____5335 uu____5337  in
        let uu____5339 =
          let uu____5340 = p_typars tpars  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5340 FStar_Pprint.equals
           in
        let uu____5343 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5339 uu____5343
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5374 =
          let uu____5375 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5375  in
        let uu____5388 =
          let uu____5389 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5427 =
                    let uu____5428 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5428 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5427)) uu____5389
           in
        FStar_Pprint.op_Hat_Hat uu____5374 uu____5388
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5445 = str "let"  in
          let uu____5447 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5445 uu____5447  in
        let uu____5448 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5448 p_letbinding lbs
          (fun uu____5458  ->
             match uu____5458 with
             | (p,t) ->
                 let uu____5465 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5465;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5471 =
          let uu____5472 = str "val"  in
          let uu____5474 =
            let uu____5475 =
              let uu____5476 = p_lident lid  in
              let uu____5477 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5476 uu____5477  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5475  in
          FStar_Pprint.op_Hat_Hat uu____5472 uu____5474  in
        FStar_All.pipe_left FStar_Pprint.group uu____5471
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5482 =
            let uu____5484 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5484 FStar_Util.is_upper  in
          if uu____5482
          then FStar_Pprint.empty
          else
            (let uu____5492 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5492 FStar_Pprint.space)
           in
        let uu____5494 =
          let uu____5495 = p_ident id1  in
          let uu____5496 =
            let uu____5497 =
              let uu____5498 =
                let uu____5499 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5499  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5498  in
            FStar_Pprint.group uu____5497  in
          FStar_Pprint.op_Hat_Hat uu____5495 uu____5496  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5494
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5508 = str "exception"  in
        let uu____5510 =
          let uu____5511 =
            let uu____5512 = p_uident uid  in
            let uu____5513 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5517 =
                     let uu____5518 = str "of"  in
                     let uu____5520 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5518 uu____5520  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5517) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5512 uu____5513  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5511  in
        FStar_Pprint.op_Hat_Hat uu____5508 uu____5510
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5524 = str "new_effect"  in
        let uu____5526 =
          let uu____5527 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5527  in
        FStar_Pprint.op_Hat_Hat uu____5524 uu____5526
    | FStar_Parser_AST.SubEffect se ->
        let uu____5529 = str "sub_effect"  in
        let uu____5531 =
          let uu____5532 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5532  in
        FStar_Pprint.op_Hat_Hat uu____5529 uu____5531
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5535 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5537,uu____5538) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5566 = str "%splice"  in
        let uu____5568 =
          let uu____5569 =
            let uu____5570 = str ";"  in p_list p_uident uu____5570 ids  in
          let uu____5572 =
            let uu____5573 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5573  in
          FStar_Pprint.op_Hat_Hat uu____5569 uu____5572  in
        FStar_Pprint.op_Hat_Hat uu____5566 uu____5568

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5576  ->
    match uu___5_5576 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5579 = str "#set-options"  in
        let uu____5581 =
          let uu____5582 =
            let uu____5583 = str s  in FStar_Pprint.dquotes uu____5583  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5582  in
        FStar_Pprint.op_Hat_Hat uu____5579 uu____5581
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5588 = str "#reset-options"  in
        let uu____5590 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5596 =
                 let uu____5597 = str s  in FStar_Pprint.dquotes uu____5597
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5596) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5588 uu____5590
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5602 = str "#push-options"  in
        let uu____5604 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5610 =
                 let uu____5611 = str s  in FStar_Pprint.dquotes uu____5611
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5610) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5602 uu____5604
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
    fun uu____5643  ->
      match uu____5643 with
      | (typedecl,fsdoc_opt) ->
          let uu____5656 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5656 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5681 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5681
               else
                 (let uu____5684 =
                    let uu____5685 =
                      let uu____5686 =
                        let uu____5687 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5687 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5686  in
                    let uu____5688 =
                      let uu____5689 =
                        let uu____5690 =
                          let uu____5691 =
                            let uu____5692 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5692  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5691
                           in
                        FStar_Pprint.nest (Prims.of_int (2)) uu____5690  in
                      FStar_Pprint.op_Hat_Hat decl uu____5689  in
                    FStar_Pprint.ifflat uu____5685 uu____5688  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5684))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5695  ->
      match uu___6_5695 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5724 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5724, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5741 = p_typ_sep false false t  in
          (match uu____5741 with
           | (comm,doc1) ->
               let uu____5761 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5761, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5817 =
            match uu____5817 with
            | (lid1,t,doc_opt) ->
                let uu____5834 =
                  let uu____5839 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5839
                   in
                (match uu____5834 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5857 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5857  in
          let uu____5866 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5866, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5933 =
            match uu____5933 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5962 =
                    let uu____5963 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5963  in
                  FStar_Range.extend_to_end_of_line uu____5962  in
                let uu____5968 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5968 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6007 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6007, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6012  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6012 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6047 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6047  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6049 =
                        let uu____6052 =
                          let uu____6055 = p_fsdoc fsdoc  in
                          let uu____6056 =
                            let uu____6059 = cont lid_doc  in [uu____6059]
                             in
                          uu____6055 :: uu____6056  in
                        kw :: uu____6052  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6049
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6066 =
                        let uu____6067 =
                          let uu____6068 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6068 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6067
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6066
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6088 =
                          let uu____6089 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6089  in
                        prefix2 uu____6088 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6091  ->
      match uu____6091 with
      | (lid,t,doc_opt) ->
          let uu____6108 =
            let uu____6109 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6110 =
              let uu____6111 = p_lident lid  in
              let uu____6112 =
                let uu____6113 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6113  in
              FStar_Pprint.op_Hat_Hat uu____6111 uu____6112  in
            FStar_Pprint.op_Hat_Hat uu____6109 uu____6110  in
          FStar_Pprint.group uu____6108

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6115  ->
    match uu____6115 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6149 =
            let uu____6150 =
              let uu____6151 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6151  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6150  in
          FStar_Pprint.group uu____6149  in
        let uu____6152 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6153 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6157 =
                 let uu____6158 =
                   let uu____6159 =
                     let uu____6160 =
                       let uu____6161 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6161
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6160  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6159  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6158  in
               FStar_Pprint.group uu____6157) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6152 uu____6153

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6165  ->
      fun inner_let  ->
        match uu____6165 with
        | (pat,uu____6173) ->
            let uu____6174 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6226 =
                    let uu____6233 =
                      let uu____6238 =
                        let uu____6239 =
                          let uu____6240 =
                            let uu____6241 = str "by"  in
                            let uu____6243 =
                              let uu____6244 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6244
                               in
                            FStar_Pprint.op_Hat_Hat uu____6241 uu____6243  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6240
                           in
                        FStar_Pprint.group uu____6239  in
                      (t, uu____6238)  in
                    FStar_Pervasives_Native.Some uu____6233  in
                  (pat1, uu____6226)
              | uu____6255 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6174 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6281);
                         FStar_Parser_AST.prange = uu____6282;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6299 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6299 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6305 =
                        if inner_let
                        then
                          let uu____6319 = pats_as_binders_if_possible pats
                             in
                          match uu____6319 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6342 = pats_as_binders_if_possible pats
                              in
                           match uu____6342 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6305 with
                       | (terms,style) ->
                           let uu____6369 =
                             let uu____6370 =
                               let uu____6371 =
                                 let uu____6372 = p_lident lid  in
                                 let uu____6373 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6372
                                   uu____6373
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6371
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6370  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6369)
                  | uu____6376 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6384 =
                              let uu____6385 =
                                let uu____6386 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6386
                                 in
                              FStar_Pprint.group uu____6385  in
                            FStar_Pprint.op_Hat_Hat uu____6384 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6397 =
                        let uu____6398 =
                          let uu____6399 =
                            let uu____6400 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6400  in
                          FStar_Pprint.group uu____6399  in
                        FStar_Pprint.op_Hat_Hat uu____6398 ascr_doc  in
                      FStar_Pprint.group uu____6397))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6402  ->
      match uu____6402 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6411 = p_term_sep false false e  in
          (match uu____6411 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6421 =
                 let uu____6422 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6422  in
               let uu____6423 =
                 let uu____6424 =
                   let uu____6425 =
                     let uu____6426 =
                       let uu____6427 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6427
                        in
                     FStar_Pprint.group uu____6426  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6425  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6424  in
               FStar_Pprint.ifflat uu____6421 uu____6423)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_6428  ->
    match uu___7_6428 with
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
        let uu____6453 = p_uident uid  in
        let uu____6454 = p_binders true bs  in
        let uu____6456 =
          let uu____6457 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6457  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____6453
          uu____6454 uu____6456

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
          let uu____6472 =
            let uu____6473 =
              let uu____6474 =
                let uu____6475 = p_uident uid  in
                let uu____6476 = p_binders true bs  in
                let uu____6478 =
                  let uu____6479 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6479  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6475 uu____6476 uu____6478
                 in
              FStar_Pprint.group uu____6474  in
            let uu____6484 =
              let uu____6485 = str "with"  in
              let uu____6487 =
                let uu____6488 =
                  let uu____6489 =
                    let uu____6490 =
                      let uu____6491 =
                        let uu____6492 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6492
                         in
                      separate_map_last uu____6491 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6490  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6489  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6488  in
              FStar_Pprint.op_Hat_Hat uu____6485 uu____6487  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6473 uu____6484  in
          braces_with_nesting uu____6472

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6496,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6529 =
            let uu____6530 = p_lident lid  in
            let uu____6531 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6530 uu____6531  in
          let uu____6532 = p_simpleTerm ps false e  in
          prefix2 uu____6529 uu____6532
      | uu____6534 ->
          let uu____6535 =
            let uu____6537 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6537
             in
          failwith uu____6535

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6620 =
        match uu____6620 with
        | (kwd,t) ->
            let uu____6631 =
              let uu____6632 = str kwd  in
              let uu____6633 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6632 uu____6633  in
            let uu____6634 = p_simpleTerm ps false t  in
            prefix2 uu____6631 uu____6634
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6641 =
      let uu____6642 =
        let uu____6643 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6644 =
          let uu____6645 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6645  in
        FStar_Pprint.op_Hat_Hat uu____6643 uu____6644  in
      let uu____6647 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6642 uu____6647  in
    let uu____6648 =
      let uu____6649 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6649  in
    FStar_Pprint.op_Hat_Hat uu____6641 uu____6648

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6650  ->
    match uu___8_6650 with
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
        let uu____6670 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6670 FStar_Pprint.hardline
    | uu____6671 ->
        let uu____6672 =
          let uu____6673 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6673  in
        FStar_Pprint.op_Hat_Hat uu____6672 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6676  ->
    match uu___9_6676 with
    | FStar_Parser_AST.Rec  ->
        let uu____6677 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6677
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6679  ->
    match uu___10_6679 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6684,e) -> e
          | uu____6690 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6691 = str "#["  in
        let uu____6693 =
          let uu____6694 = p_term false false t1  in
          let uu____6697 =
            let uu____6698 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6698 break1  in
          FStar_Pprint.op_Hat_Hat uu____6694 uu____6697  in
        FStar_Pprint.op_Hat_Hat uu____6691 uu____6693

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6704 =
          let uu____6705 =
            let uu____6706 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6706  in
          FStar_Pprint.separate_map uu____6705 p_tuplePattern pats  in
        FStar_Pprint.group uu____6704
    | uu____6707 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6716 =
          let uu____6717 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6717 p_constructorPattern pats  in
        FStar_Pprint.group uu____6716
    | uu____6718 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6721;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6726 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6727 = p_constructorPattern hd1  in
        let uu____6728 = p_constructorPattern tl1  in
        infix0 uu____6726 uu____6727 uu____6728
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6730;_},pats)
        ->
        let uu____6736 = p_quident uid  in
        let uu____6737 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6736 uu____6737
    | uu____6738 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6754;
               FStar_Parser_AST.blevel = uu____6755;
               FStar_Parser_AST.aqual = uu____6756;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6765 =
               let uu____6766 = p_ident lid  in
               p_refinement aqual uu____6766 t1 phi  in
             soft_parens_with_nesting uu____6765
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6769;
               FStar_Parser_AST.blevel = uu____6770;
               FStar_Parser_AST.aqual = uu____6771;_},phi))
             ->
             let uu____6777 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6777
         | uu____6778 ->
             let uu____6783 =
               let uu____6784 = p_tuplePattern pat  in
               let uu____6785 =
                 let uu____6786 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6786
                  in
               FStar_Pprint.op_Hat_Hat uu____6784 uu____6785  in
             soft_parens_with_nesting uu____6783)
    | FStar_Parser_AST.PatList pats ->
        let uu____6790 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6790 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6809 =
          match uu____6809 with
          | (lid,pat) ->
              let uu____6816 = p_qlident lid  in
              let uu____6817 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6816 uu____6817
           in
        let uu____6818 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6818
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6830 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6831 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6832 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6830
          uu____6831 uu____6832
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6843 =
          let uu____6844 =
            let uu____6845 =
              let uu____6846 = FStar_Ident.text_of_id op  in str uu____6846
               in
            let uu____6848 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6845 uu____6848  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6844  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6843
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6852 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6852 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6860 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6861 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6860 uu____6861
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6863 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6867;
           FStar_Parser_AST.prange = uu____6868;_},uu____6869)
        ->
        let uu____6874 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6874
    | FStar_Parser_AST.PatTuple (uu____6875,false ) ->
        let uu____6882 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6882
    | uu____6883 ->
        let uu____6884 =
          let uu____6886 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6886  in
        failwith uu____6884

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6891;_},uu____6892)
        -> true
    | uu____6899 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6905) -> true
    | uu____6907 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6914 = p_binder' is_atomic b  in
      match uu____6914 with
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
          let uu____6951 =
            let uu____6952 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6953 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6952 uu____6953  in
          (uu____6951, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6959 = p_lident lid  in
          (uu____6959, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6966 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6977;
                   FStar_Parser_AST.blevel = uu____6978;
                   FStar_Parser_AST.aqual = uu____6979;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6984 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6984 t1 phi
            | uu____6985 ->
                let t' =
                  let uu____6987 = is_typ_tuple t  in
                  if uu____6987
                  then
                    let uu____6990 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6990
                  else p_tmFormula t  in
                let uu____6993 =
                  let uu____6994 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6995 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6994 uu____6995  in
                (uu____6993, t')
             in
          (match uu____6966 with
           | (b',t') ->
               let catf =
                 let uu____7013 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7013
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7020 =
                         let uu____7021 =
                           let uu____7022 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7022
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7021
                          in
                       FStar_Pprint.group uu____7020
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7027 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7027)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7032 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7060;
                  FStar_Parser_AST.blevel = uu____7061;
                  FStar_Parser_AST.aqual = uu____7062;_},phi)
               ->
               let uu____7066 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7066 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7087 ->
               if is_atomic
               then
                 let uu____7099 = p_atomicTerm t  in
                 (uu____7099, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7106 = p_appTerm t  in
                  (uu____7106, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7117 = p_refinement' aqual_opt binder t phi  in
          match uu____7117 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7133 -> false
            | FStar_Parser_AST.App uu____7145 -> false
            | FStar_Parser_AST.Op uu____7153 -> false
            | uu____7161 -> true  in
          let uu____7163 = p_noSeqTerm false false phi  in
          match uu____7163 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7180 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7180)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____7189 =
                let uu____7190 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7190 binder  in
              let uu____7191 =
                let uu____7192 = p_appTerm t  in
                let uu____7193 =
                  let uu____7194 =
                    let uu____7195 =
                      let uu____7196 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7197 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7196 uu____7197  in
                    FStar_Pprint.group uu____7195  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____7194
                   in
                FStar_Pprint.op_Hat_Hat uu____7192 uu____7193  in
              (uu____7189, uu____7191)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7211 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7211

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7215 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7218 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7218)
       in
    if uu____7215
    then FStar_Pprint.underscore
    else (let uu____7223 = FStar_Ident.text_of_id lid  in str uu____7223)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7226 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7229 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7229)
       in
    if uu____7226
    then FStar_Pprint.underscore
    else (let uu____7234 = FStar_Ident.text_of_lid lid  in str uu____7234)

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
          let uu____7255 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7255
        else
          (let uu____7258 =
             let uu____7259 =
               let uu____7260 =
                 let uu____7261 =
                   let uu____7262 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7262  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7261  in
               FStar_Pprint.group uu____7260  in
             let uu____7263 =
               let uu____7264 =
                 let uu____7265 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7265  in
               FStar_Pprint.op_Hat_Hat comm uu____7264  in
             FStar_Pprint.ifflat uu____7259 uu____7263  in
           FStar_All.pipe_left FStar_Pprint.group uu____7258)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7273 = p_noSeqTerm true false e1  in
            (match uu____7273 with
             | (comm,t1) ->
                 let uu____7282 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7283 =
                   let uu____7284 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7284
                    in
                 FStar_Pprint.op_Hat_Hat uu____7282 uu____7283)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7288 =
              let uu____7289 =
                let uu____7290 =
                  let uu____7291 = p_lident x  in
                  let uu____7292 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7291 uu____7292  in
                let uu____7293 =
                  let uu____7294 = p_noSeqTermAndComment true false e1  in
                  let uu____7297 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7294 uu____7297  in
                op_Hat_Slash_Plus_Hat uu____7290 uu____7293  in
              FStar_Pprint.group uu____7289  in
            let uu____7298 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7288 uu____7298
        | uu____7299 ->
            let uu____7300 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7300

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
            let uu____7312 = p_noSeqTerm true false e1  in
            (match uu____7312 with
             | (comm,t1) ->
                 let uu____7325 =
                   let uu____7326 =
                     let uu____7327 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7327  in
                   let uu____7328 =
                     let uu____7329 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7329
                      in
                   FStar_Pprint.op_Hat_Hat uu____7326 uu____7328  in
                 (comm, uu____7325))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7333 =
              let uu____7334 =
                let uu____7335 =
                  let uu____7336 =
                    let uu____7337 = p_lident x  in
                    let uu____7338 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7337 uu____7338  in
                  let uu____7339 =
                    let uu____7340 = p_noSeqTermAndComment true false e1  in
                    let uu____7343 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7340 uu____7343  in
                  op_Hat_Slash_Plus_Hat uu____7336 uu____7339  in
                FStar_Pprint.group uu____7335  in
              let uu____7344 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7334 uu____7344  in
            (FStar_Pprint.empty, uu____7333)
        | uu____7345 -> p_noSeqTerm ps pb e

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
            let uu____7365 =
              let uu____7366 = p_tmIff e1  in
              let uu____7367 =
                let uu____7368 =
                  let uu____7369 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7369
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7368  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7366 uu____7367  in
            FStar_Pprint.group uu____7365
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7375 =
              let uu____7376 = p_tmIff e1  in
              let uu____7377 =
                let uu____7378 =
                  let uu____7379 =
                    let uu____7380 = p_typ false false t  in
                    let uu____7383 =
                      let uu____7384 = str "by"  in
                      let uu____7386 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7384 uu____7386  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7380 uu____7383  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7379
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7378  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7376 uu____7377  in
            FStar_Pprint.group uu____7375
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7387;_},e1::e2::e3::[])
            ->
            let uu____7394 =
              let uu____7395 =
                let uu____7396 =
                  let uu____7397 = p_atomicTermNotQUident e1  in
                  let uu____7398 =
                    let uu____7399 =
                      let uu____7400 =
                        let uu____7401 = p_term false false e2  in
                        soft_parens_with_nesting uu____7401  in
                      let uu____7404 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7400 uu____7404  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7399  in
                  FStar_Pprint.op_Hat_Hat uu____7397 uu____7398  in
                FStar_Pprint.group uu____7396  in
              let uu____7405 =
                let uu____7406 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7406  in
              FStar_Pprint.op_Hat_Hat uu____7395 uu____7405  in
            FStar_Pprint.group uu____7394
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7407;_},e1::e2::e3::[])
            ->
            let uu____7414 =
              let uu____7415 =
                let uu____7416 =
                  let uu____7417 = p_atomicTermNotQUident e1  in
                  let uu____7418 =
                    let uu____7419 =
                      let uu____7420 =
                        let uu____7421 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7421  in
                      let uu____7424 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7420 uu____7424  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7419  in
                  FStar_Pprint.op_Hat_Hat uu____7417 uu____7418  in
                FStar_Pprint.group uu____7416  in
              let uu____7425 =
                let uu____7426 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7426  in
              FStar_Pprint.op_Hat_Hat uu____7415 uu____7425  in
            FStar_Pprint.group uu____7414
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7436 =
              let uu____7437 = str "requires"  in
              let uu____7439 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7437 uu____7439  in
            FStar_Pprint.group uu____7436
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7449 =
              let uu____7450 = str "ensures"  in
              let uu____7452 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7450 uu____7452  in
            FStar_Pprint.group uu____7449
        | FStar_Parser_AST.Attributes es ->
            let uu____7456 =
              let uu____7457 = str "attributes"  in
              let uu____7459 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7457 uu____7459  in
            FStar_Pprint.group uu____7456
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7464 =
                let uu____7465 =
                  let uu____7466 = str "if"  in
                  let uu____7468 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7466 uu____7468  in
                let uu____7471 =
                  let uu____7472 = str "then"  in
                  let uu____7474 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7472 uu____7474  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7465 uu____7471  in
              FStar_Pprint.group uu____7464
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7478,uu____7479,e31) when
                     is_unit e31 ->
                     let uu____7481 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7481
                 | uu____7484 -> p_noSeqTermAndComment false false e2  in
               let uu____7487 =
                 let uu____7488 =
                   let uu____7489 = str "if"  in
                   let uu____7491 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7489 uu____7491  in
                 let uu____7494 =
                   let uu____7495 =
                     let uu____7496 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7496 e2_doc  in
                   let uu____7498 =
                     let uu____7499 = str "else"  in
                     let uu____7501 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7499 uu____7501  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7495 uu____7498  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7488 uu____7494  in
               FStar_Pprint.group uu____7487)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7524 =
              let uu____7525 =
                let uu____7526 =
                  let uu____7527 = str "try"  in
                  let uu____7529 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7527 uu____7529  in
                let uu____7532 =
                  let uu____7533 = str "with"  in
                  let uu____7535 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7533 uu____7535  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7526 uu____7532  in
              FStar_Pprint.group uu____7525  in
            let uu____7544 = paren_if (ps || pb)  in uu____7544 uu____7524
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7571 =
              let uu____7572 =
                let uu____7573 =
                  let uu____7574 = str "match"  in
                  let uu____7576 = p_noSeqTermAndComment false false e1  in
                  let uu____7579 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7574 uu____7576 uu____7579
                   in
                let uu____7583 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7573 uu____7583  in
              FStar_Pprint.group uu____7572  in
            let uu____7592 = paren_if (ps || pb)  in uu____7592 uu____7571
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7599 =
              let uu____7600 =
                let uu____7601 =
                  let uu____7602 = str "let open"  in
                  let uu____7604 = p_quident uid  in
                  let uu____7605 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7602 uu____7604 uu____7605
                   in
                let uu____7609 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7601 uu____7609  in
              FStar_Pprint.group uu____7600  in
            let uu____7611 = paren_if ps  in uu____7611 uu____7599
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7676 is_last =
              match uu____7676 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7710 =
                          let uu____7711 = str "let"  in
                          let uu____7713 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7711 uu____7713
                           in
                        FStar_Pprint.group uu____7710
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7716 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7722 = p_term_sep false false e2  in
                  (match uu____7722 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7732 =
                         if is_last
                         then
                           let uu____7734 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7735 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7734 doc_expr1 uu____7735
                         else
                           (let uu____7741 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7741)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7732)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7792 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7792
                     else
                       (let uu____7797 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7797)) lbs
               in
            let lbs_doc =
              let uu____7801 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7801  in
            let uu____7802 =
              let uu____7803 =
                let uu____7804 =
                  let uu____7805 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7805
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7804  in
              FStar_Pprint.group uu____7803  in
            let uu____7807 = paren_if ps  in uu____7807 uu____7802
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7814;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7817;
                                                             FStar_Parser_AST.level
                                                               = uu____7818;_})
            when matches_var maybe_x x ->
            let uu____7845 =
              let uu____7846 =
                let uu____7847 = str "function"  in
                let uu____7849 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7847 uu____7849  in
              FStar_Pprint.group uu____7846  in
            let uu____7858 = paren_if (ps || pb)  in uu____7858 uu____7845
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7864 =
              let uu____7865 = str "quote"  in
              let uu____7867 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7865 uu____7867  in
            FStar_Pprint.group uu____7864
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7869 =
              let uu____7870 = str "`"  in
              let uu____7872 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7870 uu____7872  in
            FStar_Pprint.group uu____7869
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7874 =
              let uu____7875 = str "`%"  in
              let uu____7877 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7875 uu____7877  in
            FStar_Pprint.group uu____7874
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7879;
              FStar_Parser_AST.level = uu____7880;_}
            ->
            let uu____7881 =
              let uu____7882 = str "`@"  in
              let uu____7884 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7882 uu____7884  in
            FStar_Pprint.group uu____7881
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7886 =
              let uu____7887 = str "`#"  in
              let uu____7889 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7887 uu____7889  in
            FStar_Pprint.group uu____7886
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7898 = str "calc"  in
              let uu____7900 =
                let uu____7901 =
                  let uu____7902 = p_noSeqTermAndComment false false rel  in
                  let uu____7905 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7902 uu____7905  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7901  in
              FStar_Pprint.op_Hat_Hat uu____7898 uu____7900  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7907 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7908 =
              let uu____7909 =
                let uu____7910 =
                  let uu____7911 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7914 =
                    let uu____7915 = str ";"  in
                    let uu____7917 =
                      let uu____7918 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7918
                       in
                    FStar_Pprint.op_Hat_Hat uu____7915 uu____7917  in
                  FStar_Pprint.op_Hat_Hat uu____7911 uu____7914  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7910  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7909
               in
            FStar_Pprint.enclose head1 uu____7907 uu____7908
        | uu____7920 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7921  ->
    fun uu____7922  ->
      match uu____7922 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7927 =
            let uu____7928 = p_noSeqTermAndComment false false rel  in
            let uu____7931 =
              let uu____7932 =
                let uu____7933 =
                  let uu____7934 =
                    let uu____7935 = p_noSeqTermAndComment false false just
                       in
                    let uu____7938 =
                      let uu____7939 =
                        let uu____7940 =
                          let uu____7941 =
                            let uu____7942 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7945 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7942 uu____7945  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7941
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7940
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7939
                       in
                    FStar_Pprint.op_Hat_Hat uu____7935 uu____7938  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7934  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7933  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7932  in
            FStar_Pprint.op_Hat_Hat uu____7928 uu____7931  in
          FStar_Pprint.group uu____7927

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7947  ->
    match uu___11_7947 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7959 =
          let uu____7960 = str "[@"  in
          let uu____7962 =
            let uu____7963 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7964 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7963 uu____7964  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7960 uu____7962  in
        FStar_Pprint.group uu____7959

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
        | FStar_Parser_AST.QForall (bs,(uu____7982,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8016 =
                   let uu____8017 =
                     let uu____8018 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8018 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8017 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8016 term_doc
             | pats ->
                 let uu____8026 =
                   let uu____8027 =
                     let uu____8028 =
                       let uu____8029 =
                         let uu____8030 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8030
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8029 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8033 = p_trigger trigger  in
                     prefix2 uu____8028 uu____8033  in
                   FStar_Pprint.group uu____8027  in
                 prefix2 uu____8026 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____8035,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8069 =
                   let uu____8070 =
                     let uu____8071 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8071 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____8070 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____8069 term_doc
             | pats ->
                 let uu____8079 =
                   let uu____8080 =
                     let uu____8081 =
                       let uu____8082 =
                         let uu____8083 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8083
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____8082 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8086 = p_trigger trigger  in
                     prefix2 uu____8081 uu____8086  in
                   FStar_Pprint.group uu____8080  in
                 prefix2 uu____8079 term_doc)
        | uu____8087 -> p_simpleTerm ps pb e

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
      let uu____8108 = all_binders_annot t  in
      if uu____8108
      then
        let uu____8111 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8111
      else
        (let uu____8122 =
           let uu____8123 =
             let uu____8124 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8124  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8123  in
         FStar_Pprint.group uu____8122)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8183 = x  in
      match uu____8183 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8248 = hd1  in
               (match uu____8248 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8320 = cb  in
      match uu____8320 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8339 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8345 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8345) hd1 tl1
                  in
               cat_with_colon uu____8339 typ)
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
                 FStar_Parser_AST.brange = uu____8424;
                 FStar_Parser_AST.blevel = uu____8425;
                 FStar_Parser_AST.aqual = uu____8426;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8435 =
                 let uu____8440 = p_ident lid  in
                 p_refinement' aqual uu____8440 t1 phi  in
               FStar_Pervasives_Native.Some uu____8435
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8447) ->
               let uu____8452 =
                 let uu____8457 =
                   let uu____8458 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8459 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8458 uu____8459  in
                 let uu____8460 = p_tmEqNoRefinement t  in
                 (uu____8457, uu____8460)  in
               FStar_Pervasives_Native.Some uu____8452
           | uu____8465 -> FStar_Pervasives_Native.None)
      | uu____8474 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8487 -> false
      | uu____8499 -> true  in
    let uu____8501 = map_if_all all_binders pats  in
    match uu____8501 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8533 = collapse_pats bs  in
        (uu____8533, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8550 = FStar_List.map p_atomicPattern pats  in
        (uu____8550, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8562 -> str "forall"
    | FStar_Parser_AST.QExists uu____8582 -> str "exists"
    | uu____8602 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8604  ->
    match uu___12_8604 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8616 =
          let uu____8617 =
            let uu____8618 =
              let uu____8619 = str "pattern"  in
              let uu____8621 =
                let uu____8622 =
                  let uu____8623 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8623
                   in
                FStar_Pprint.op_Hat_Hat uu____8622 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8619 uu____8621  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8618  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8617  in
        FStar_Pprint.group uu____8616

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8631 = str "\\/"  in
    FStar_Pprint.separate_map uu____8631 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8638 =
      let uu____8639 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8639 p_appTerm pats  in
    FStar_Pprint.group uu____8638

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8651 = p_term_sep false pb e1  in
            (match uu____8651 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8660 = str "fun"  in
                   let uu____8662 =
                     let uu____8663 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8663
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8660 uu____8662  in
                 let uu____8664 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8666 =
                       let uu____8667 =
                         let uu____8668 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8668  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8667
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8666
                   else
                     (let uu____8671 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8671)
                    in
                 let uu____8672 = paren_if ps  in uu____8672 uu____8664)
        | uu____8677 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8685  ->
      match uu____8685 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8709 =
                    let uu____8710 =
                      let uu____8711 =
                        let uu____8712 = p_tuplePattern p  in
                        let uu____8713 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8712 uu____8713  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8711
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8710  in
                  FStar_Pprint.group uu____8709
              | FStar_Pervasives_Native.Some f ->
                  let uu____8715 =
                    let uu____8716 =
                      let uu____8717 =
                        let uu____8718 =
                          let uu____8719 =
                            let uu____8720 = p_tuplePattern p  in
                            let uu____8721 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8720
                              uu____8721
                             in
                          FStar_Pprint.group uu____8719  in
                        let uu____8723 =
                          let uu____8724 =
                            let uu____8727 = p_tmFormula f  in
                            [uu____8727; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8724  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8718 uu____8723
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8717
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8716  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8715
               in
            let uu____8729 = p_term_sep false pb e  in
            match uu____8729 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8739 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8739
                   else
                     (let uu____8742 =
                        let uu____8743 =
                          let uu____8744 =
                            let uu____8745 =
                              let uu____8746 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8746  in
                            op_Hat_Slash_Plus_Hat branch uu____8745  in
                          FStar_Pprint.group uu____8744  in
                        let uu____8747 =
                          let uu____8748 =
                            let uu____8749 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8749  in
                          FStar_Pprint.op_Hat_Hat branch uu____8748  in
                        FStar_Pprint.ifflat uu____8743 uu____8747  in
                      FStar_Pprint.group uu____8742))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8753 =
                       let uu____8754 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8754  in
                     op_Hat_Slash_Plus_Hat branch uu____8753)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8765 =
                      let uu____8766 =
                        let uu____8767 =
                          let uu____8768 =
                            let uu____8769 =
                              let uu____8770 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8770  in
                            FStar_Pprint.separate_map uu____8769
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8768
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8767
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8766  in
                    FStar_Pprint.group uu____8765
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8772 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8774;_},e1::e2::[])
        ->
        let uu____8780 = str "<==>"  in
        let uu____8782 = p_tmImplies e1  in
        let uu____8783 = p_tmIff e2  in
        infix0 uu____8780 uu____8782 uu____8783
    | uu____8784 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8786;_},e1::e2::[])
        ->
        let uu____8792 = str "==>"  in
        let uu____8794 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8800 = p_tmImplies e2  in
        infix0 uu____8792 uu____8794 uu____8800
    | uu____8801 ->
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
          let uu____8815 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8815 with
          | (terms',last1) ->
              let uu____8835 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8870 =
                      let uu____8871 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8871
                       in
                    let uu____8872 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8870, uu____8872)
                | Binders (n1,ln,parens1) ->
                    let uu____8886 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8894 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8886, break1, uu____8894)
                 in
              (match uu____8835 with
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
                    | _8927 when _8927 = Prims.int_one -> FStar_List.hd terms
                    | uu____8928 ->
                        let uu____8929 =
                          let uu____8930 =
                            let uu____8931 =
                              let uu____8932 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8933 =
                                let uu____8934 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8934
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8932 uu____8933
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8931  in
                          let uu____8935 =
                            let uu____8936 =
                              let uu____8937 =
                                let uu____8938 =
                                  let uu____8939 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8939  in
                                let uu____8940 =
                                  let uu____8941 =
                                    let uu____8942 =
                                      let uu____8943 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8944 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8950 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8950)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8943
                                        uu____8944
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8942
                                     in
                                  jump2 uu____8941  in
                                FStar_Pprint.ifflat uu____8938 uu____8940  in
                              FStar_Pprint.group uu____8937  in
                            let uu____8952 =
                              let uu____8953 =
                                let uu____8954 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8954  in
                              FStar_Pprint.align uu____8953  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8936
                              uu____8952
                             in
                          FStar_Pprint.ifflat uu____8930 uu____8935  in
                        FStar_Pprint.group uu____8929))

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
            | Arrows uu____8968 -> p_tmArrow' p_Tm e
            | Binders uu____8975 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8998 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9004 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8998 uu____9004
      | uu____9007 -> let uu____9008 = p_Tm e  in [uu____9008]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9061 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9087 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9061 uu____9087
        | uu____9110 ->
            let uu____9111 =
              let uu____9122 = p_Tm1 e1  in
              (uu____9122, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9111]
         in
      let fold_fun bs x =
        let uu____9220 = x  in
        match uu____9220 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9352 = hd1  in
                 (match uu____9352 with
                  | (b2s,t2,uu____9381) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9483 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9540 = cb  in
        match uu____9540 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9569 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9580 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9586 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9586) hd1 tl1
                         in
                      f uu____9580 typ))
         in
      let binders =
        let uu____9602 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9602  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9665 =
        let uu____9666 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9666 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9665  in
    let disj =
      let uu____9669 =
        let uu____9670 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9670 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9669  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9690;_},e1::e2::[])
        ->
        let uu____9696 = p_tmDisjunction e1  in
        let uu____9701 = let uu____9706 = p_tmConjunction e2  in [uu____9706]
           in
        FStar_List.append uu____9696 uu____9701
    | uu____9715 -> let uu____9716 = p_tmConjunction e  in [uu____9716]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9726;_},e1::e2::[])
        ->
        let uu____9732 = p_tmConjunction e1  in
        let uu____9735 = let uu____9738 = p_tmTuple e2  in [uu____9738]  in
        FStar_List.append uu____9732 uu____9735
    | uu____9739 -> let uu____9740 = p_tmTuple e  in [uu____9740]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9757 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9757
          (fun uu____9765  ->
             match uu____9765 with | (e1,uu____9771) -> p_tmEq e1) args
    | uu____9772 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9781 =
             let uu____9782 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9782  in
           FStar_Pprint.group uu____9781)

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
               (let uu____9801 = FStar_Ident.text_of_id op  in
                uu____9801 = "="))
              ||
              (let uu____9806 = FStar_Ident.text_of_id op  in
               uu____9806 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9812 = levels op1  in
            (match uu____9812 with
             | (left1,mine,right1) ->
                 let uu____9831 =
                   let uu____9832 = FStar_All.pipe_left str op1  in
                   let uu____9834 = p_tmEqWith' p_X left1 e1  in
                   let uu____9835 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9832 uu____9834 uu____9835  in
                 paren_if_gt curr mine uu____9831)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9836;_},e1::e2::[])
            ->
            let uu____9842 =
              let uu____9843 = p_tmEqWith p_X e1  in
              let uu____9844 =
                let uu____9845 =
                  let uu____9846 =
                    let uu____9847 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9847  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9846  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9845  in
              FStar_Pprint.op_Hat_Hat uu____9843 uu____9844  in
            FStar_Pprint.group uu____9842
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9848;_},e1::[])
            ->
            let uu____9853 = levels "-"  in
            (match uu____9853 with
             | (left1,mine,right1) ->
                 let uu____9873 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9873)
        | uu____9874 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9922)::(e2,uu____9924)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9944 = is_list e  in Prims.op_Negation uu____9944)
              ->
              let op = "::"  in
              let uu____9949 = levels op  in
              (match uu____9949 with
               | (left1,mine,right1) ->
                   let uu____9968 =
                     let uu____9969 = str op  in
                     let uu____9970 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9972 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9969 uu____9970 uu____9972  in
                   paren_if_gt curr mine uu____9968)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9991 = levels op  in
              (match uu____9991 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10025 = p_binder false b  in
                         let uu____10027 =
                           let uu____10028 =
                             let uu____10029 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10029 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10028
                            in
                         FStar_Pprint.op_Hat_Hat uu____10025 uu____10027
                     | FStar_Util.Inr t ->
                         let uu____10031 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10033 =
                           let uu____10034 =
                             let uu____10035 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10035 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10034
                            in
                         FStar_Pprint.op_Hat_Hat uu____10031 uu____10033
                      in
                   let uu____10036 =
                     let uu____10037 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10042 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10037 uu____10042  in
                   paren_if_gt curr mine uu____10036)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10044;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10074 = levels op  in
              (match uu____10074 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10094 = str op  in
                     let uu____10095 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10097 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10094 uu____10095 uu____10097
                   else
                     (let uu____10101 =
                        let uu____10102 = str op  in
                        let uu____10103 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10105 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10102 uu____10103 uu____10105  in
                      paren_if_gt curr mine uu____10101))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10114 = levels op1  in
              (match uu____10114 with
               | (left1,mine,right1) ->
                   let uu____10133 =
                     let uu____10134 = str op1  in
                     let uu____10135 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10137 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10134 uu____10135 uu____10137  in
                   paren_if_gt curr mine uu____10133)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10157 =
                let uu____10158 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10159 =
                  let uu____10160 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10160 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10158 uu____10159  in
              braces_with_nesting uu____10157
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10165;_},e1::[])
              ->
              let uu____10170 =
                let uu____10171 = str "~"  in
                let uu____10173 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10171 uu____10173  in
              FStar_Pprint.group uu____10170
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10175;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10184 = levels op  in
                   (match uu____10184 with
                    | (left1,mine,right1) ->
                        let uu____10203 =
                          let uu____10204 = str op  in
                          let uu____10205 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10207 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10204 uu____10205 uu____10207  in
                        paren_if_gt curr mine uu____10203)
               | uu____10209 -> p_X e)
          | uu____10210 -> p_X e

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
        let uu____10217 =
          let uu____10218 = p_lident lid  in
          let uu____10219 =
            let uu____10220 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10220  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10218 uu____10219  in
        FStar_Pprint.group uu____10217
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10223 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10225 = p_appTerm e  in
    let uu____10226 =
      let uu____10227 =
        let uu____10228 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10228 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10227  in
    FStar_Pprint.op_Hat_Hat uu____10225 uu____10226

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10234 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10234 t phi
      | FStar_Parser_AST.TAnnotated uu____10235 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10241 ->
          let uu____10242 =
            let uu____10244 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10244
             in
          failwith uu____10242
      | FStar_Parser_AST.TVariable uu____10247 ->
          let uu____10248 =
            let uu____10250 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10250
             in
          failwith uu____10248
      | FStar_Parser_AST.NoName uu____10253 ->
          let uu____10254 =
            let uu____10256 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10256
             in
          failwith uu____10254

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10260  ->
      match uu____10260 with
      | (lid,e) ->
          let uu____10268 =
            let uu____10269 = p_qlident lid  in
            let uu____10270 =
              let uu____10271 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10271
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10269 uu____10270  in
          FStar_Pprint.group uu____10268

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10274 when is_general_application e ->
        let uu____10281 = head_and_args e  in
        (match uu____10281 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10328 = p_argTerm e1  in
                  let uu____10329 =
                    let uu____10330 =
                      let uu____10331 =
                        let uu____10332 = str "`"  in
                        let uu____10334 =
                          let uu____10335 = p_indexingTerm head1  in
                          let uu____10336 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10335 uu____10336  in
                        FStar_Pprint.op_Hat_Hat uu____10332 uu____10334  in
                      FStar_Pprint.group uu____10331  in
                    let uu____10338 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10330 uu____10338  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10328 uu____10329
              | uu____10339 ->
                  let uu____10346 =
                    let uu____10357 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10357
                    then
                      let uu____10391 =
                        FStar_Util.take
                          (fun uu____10415  ->
                             match uu____10415 with
                             | (uu____10421,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10391 with
                      | (fs_typ_args,args1) ->
                          let uu____10459 =
                            let uu____10460 = p_indexingTerm head1  in
                            let uu____10461 =
                              let uu____10462 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10462
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10460 uu____10461
                             in
                          (uu____10459, args1)
                    else
                      (let uu____10477 = p_indexingTerm head1  in
                       (uu____10477, args))
                     in
                  (match uu____10346 with
                   | (head_doc,args1) ->
                       let uu____10498 =
                         let uu____10499 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10499 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10498)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10521 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10521)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10540 =
               let uu____10541 = p_quident lid  in
               let uu____10542 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10541 uu____10542  in
             FStar_Pprint.group uu____10540
         | hd1::tl1 ->
             let uu____10559 =
               let uu____10560 =
                 let uu____10561 =
                   let uu____10562 = p_quident lid  in
                   let uu____10563 = p_argTerm hd1  in
                   prefix2 uu____10562 uu____10563  in
                 FStar_Pprint.group uu____10561  in
               let uu____10564 =
                 let uu____10565 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10565  in
               FStar_Pprint.op_Hat_Hat uu____10560 uu____10564  in
             FStar_Pprint.group uu____10559)
    | uu____10570 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10581 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10581 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10585 = str "#"  in
        let uu____10587 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10585 uu____10587
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10590 = str "#["  in
        let uu____10592 =
          let uu____10593 = p_indexingTerm t  in
          let uu____10594 =
            let uu____10595 = str "]"  in
            let uu____10597 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10595 uu____10597  in
          FStar_Pprint.op_Hat_Hat uu____10593 uu____10594  in
        FStar_Pprint.op_Hat_Hat uu____10590 uu____10592
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10600  ->
    match uu____10600 with | (e,uu____10606) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10611;_},e1::e2::[])
          ->
          let uu____10617 =
            let uu____10618 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10619 =
              let uu____10620 =
                let uu____10621 = p_term false false e2  in
                soft_parens_with_nesting uu____10621  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10620  in
            FStar_Pprint.op_Hat_Hat uu____10618 uu____10619  in
          FStar_Pprint.group uu____10617
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10624;_},e1::e2::[])
          ->
          let uu____10630 =
            let uu____10631 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10632 =
              let uu____10633 =
                let uu____10634 = p_term false false e2  in
                soft_brackets_with_nesting uu____10634  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10633  in
            FStar_Pprint.op_Hat_Hat uu____10631 uu____10632  in
          FStar_Pprint.group uu____10630
      | uu____10637 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10642 = p_quident lid  in
        let uu____10643 =
          let uu____10644 =
            let uu____10645 = p_term false false e1  in
            soft_parens_with_nesting uu____10645  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10644  in
        FStar_Pprint.op_Hat_Hat uu____10642 uu____10643
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10653 =
          let uu____10654 = FStar_Ident.text_of_id op  in str uu____10654  in
        let uu____10656 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10653 uu____10656
    | uu____10657 -> p_atomicTermNotQUident e

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
         | uu____10670 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10679 =
          let uu____10680 = FStar_Ident.text_of_id op  in str uu____10680  in
        let uu____10682 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10679 uu____10682
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10686 =
          let uu____10687 =
            let uu____10688 =
              let uu____10689 = FStar_Ident.text_of_id op  in str uu____10689
               in
            let uu____10691 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10688 uu____10691  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10687  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10686
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10706 = all_explicit args  in
        if uu____10706
        then
          let uu____10709 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10710 =
            let uu____10711 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10712 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10711 p_tmEq uu____10712  in
          let uu____10719 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10709
            uu____10710 uu____10719
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10741 =
                 let uu____10742 = p_quident lid  in
                 let uu____10743 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10742 uu____10743  in
               FStar_Pprint.group uu____10741
           | hd1::tl1 ->
               let uu____10760 =
                 let uu____10761 =
                   let uu____10762 =
                     let uu____10763 = p_quident lid  in
                     let uu____10764 = p_argTerm hd1  in
                     prefix2 uu____10763 uu____10764  in
                   FStar_Pprint.group uu____10762  in
                 let uu____10765 =
                   let uu____10766 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10766  in
                 FStar_Pprint.op_Hat_Hat uu____10761 uu____10765  in
               FStar_Pprint.group uu____10760)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10773 =
          let uu____10774 = p_atomicTermNotQUident e1  in
          let uu____10775 =
            let uu____10776 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10776  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10774
            uu____10775
           in
        FStar_Pprint.group uu____10773
    | uu____10779 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10784 = p_quident constr_lid  in
        let uu____10785 =
          let uu____10786 =
            let uu____10787 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10787  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10786  in
        FStar_Pprint.op_Hat_Hat uu____10784 uu____10785
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10789 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10789 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10791 = p_term_sep false false e1  in
        (match uu____10791 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10804 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10804))
    | uu____10805 when is_array e ->
        let es = extract_from_list e  in
        let uu____10809 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10810 =
          let uu____10811 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10811
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10816 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10809
          uu____10810 uu____10816
    | uu____10819 when is_list e ->
        let uu____10820 =
          let uu____10821 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10822 = extract_from_list e  in
          separate_map_or_flow_last uu____10821
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10822
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10820 FStar_Pprint.rbracket
    | uu____10831 when is_lex_list e ->
        let uu____10832 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10833 =
          let uu____10834 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10835 = extract_from_list e  in
          separate_map_or_flow_last uu____10834
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10835
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10832
          uu____10833 FStar_Pprint.rbracket
    | uu____10844 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10848 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10849 =
          let uu____10850 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10850 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10848
          uu____10849 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10860 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10863 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10860 uu____10863
    | FStar_Parser_AST.Op (op,args) when
        let uu____10872 = handleable_op op args  in
        Prims.op_Negation uu____10872 ->
        let uu____10874 =
          let uu____10876 =
            let uu____10878 = FStar_Ident.text_of_id op  in
            let uu____10880 =
              let uu____10882 =
                let uu____10884 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10884
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10882  in
            Prims.op_Hat uu____10878 uu____10880  in
          Prims.op_Hat "Operation " uu____10876  in
        failwith uu____10874
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10891 = p_term false false e  in
        soft_parens_with_nesting uu____10891
    | FStar_Parser_AST.Const uu____10894 ->
        let uu____10895 = p_term false false e  in
        soft_parens_with_nesting uu____10895
    | FStar_Parser_AST.Op uu____10898 ->
        let uu____10905 = p_term false false e  in
        soft_parens_with_nesting uu____10905
    | FStar_Parser_AST.Tvar uu____10908 ->
        let uu____10909 = p_term false false e  in
        soft_parens_with_nesting uu____10909
    | FStar_Parser_AST.Var uu____10912 ->
        let uu____10913 = p_term false false e  in
        soft_parens_with_nesting uu____10913
    | FStar_Parser_AST.Name uu____10916 ->
        let uu____10917 = p_term false false e  in
        soft_parens_with_nesting uu____10917
    | FStar_Parser_AST.Construct uu____10920 ->
        let uu____10931 = p_term false false e  in
        soft_parens_with_nesting uu____10931
    | FStar_Parser_AST.Abs uu____10934 ->
        let uu____10941 = p_term false false e  in
        soft_parens_with_nesting uu____10941
    | FStar_Parser_AST.App uu____10944 ->
        let uu____10951 = p_term false false e  in
        soft_parens_with_nesting uu____10951
    | FStar_Parser_AST.Let uu____10954 ->
        let uu____10975 = p_term false false e  in
        soft_parens_with_nesting uu____10975
    | FStar_Parser_AST.LetOpen uu____10978 ->
        let uu____10983 = p_term false false e  in
        soft_parens_with_nesting uu____10983
    | FStar_Parser_AST.Seq uu____10986 ->
        let uu____10991 = p_term false false e  in
        soft_parens_with_nesting uu____10991
    | FStar_Parser_AST.Bind uu____10994 ->
        let uu____11001 = p_term false false e  in
        soft_parens_with_nesting uu____11001
    | FStar_Parser_AST.If uu____11004 ->
        let uu____11011 = p_term false false e  in
        soft_parens_with_nesting uu____11011
    | FStar_Parser_AST.Match uu____11014 ->
        let uu____11029 = p_term false false e  in
        soft_parens_with_nesting uu____11029
    | FStar_Parser_AST.TryWith uu____11032 ->
        let uu____11047 = p_term false false e  in
        soft_parens_with_nesting uu____11047
    | FStar_Parser_AST.Ascribed uu____11050 ->
        let uu____11059 = p_term false false e  in
        soft_parens_with_nesting uu____11059
    | FStar_Parser_AST.Record uu____11062 ->
        let uu____11075 = p_term false false e  in
        soft_parens_with_nesting uu____11075
    | FStar_Parser_AST.Project uu____11078 ->
        let uu____11083 = p_term false false e  in
        soft_parens_with_nesting uu____11083
    | FStar_Parser_AST.Product uu____11086 ->
        let uu____11093 = p_term false false e  in
        soft_parens_with_nesting uu____11093
    | FStar_Parser_AST.Sum uu____11096 ->
        let uu____11107 = p_term false false e  in
        soft_parens_with_nesting uu____11107
    | FStar_Parser_AST.QForall uu____11110 ->
        let uu____11129 = p_term false false e  in
        soft_parens_with_nesting uu____11129
    | FStar_Parser_AST.QExists uu____11132 ->
        let uu____11151 = p_term false false e  in
        soft_parens_with_nesting uu____11151
    | FStar_Parser_AST.Refine uu____11154 ->
        let uu____11159 = p_term false false e  in
        soft_parens_with_nesting uu____11159
    | FStar_Parser_AST.NamedTyp uu____11162 ->
        let uu____11167 = p_term false false e  in
        soft_parens_with_nesting uu____11167
    | FStar_Parser_AST.Requires uu____11170 ->
        let uu____11178 = p_term false false e  in
        soft_parens_with_nesting uu____11178
    | FStar_Parser_AST.Ensures uu____11181 ->
        let uu____11189 = p_term false false e  in
        soft_parens_with_nesting uu____11189
    | FStar_Parser_AST.Attributes uu____11192 ->
        let uu____11195 = p_term false false e  in
        soft_parens_with_nesting uu____11195
    | FStar_Parser_AST.Quote uu____11198 ->
        let uu____11203 = p_term false false e  in
        soft_parens_with_nesting uu____11203
    | FStar_Parser_AST.VQuote uu____11206 ->
        let uu____11207 = p_term false false e  in
        soft_parens_with_nesting uu____11207
    | FStar_Parser_AST.Antiquote uu____11210 ->
        let uu____11211 = p_term false false e  in
        soft_parens_with_nesting uu____11211
    | FStar_Parser_AST.CalcProof uu____11214 ->
        let uu____11223 = p_term false false e  in
        soft_parens_with_nesting uu____11223

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_11226  ->
    match uu___15_11226 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11238) ->
        let uu____11241 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11241
    | FStar_Const.Const_bytearray (bytes,uu____11243) ->
        let uu____11248 =
          let uu____11249 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11249  in
        let uu____11250 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11248 uu____11250
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_11273 =
          match uu___13_11273 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_11280 =
          match uu___14_11280 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11295  ->
               match uu____11295 with
               | (s,w) ->
                   let uu____11302 = signedness s  in
                   let uu____11303 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11302 uu____11303)
            sign_width_opt
           in
        let uu____11304 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11304 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11308 = FStar_Range.string_of_range r  in str uu____11308
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11312 = p_quident lid  in
        let uu____11313 =
          let uu____11314 =
            let uu____11315 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11315  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11314  in
        FStar_Pprint.op_Hat_Hat uu____11312 uu____11313

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11318 = str "u#"  in
    let uu____11320 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11318 uu____11320

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11322;_},u1::u2::[])
        ->
        let uu____11328 =
          let uu____11329 = p_universeFrom u1  in
          let uu____11330 =
            let uu____11331 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11331  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11329 uu____11330  in
        FStar_Pprint.group uu____11328
    | FStar_Parser_AST.App uu____11332 ->
        let uu____11339 = head_and_args u  in
        (match uu____11339 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11365 =
                    let uu____11366 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11367 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11375  ->
                           match uu____11375 with
                           | (u1,uu____11381) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11366 uu____11367  in
                  FStar_Pprint.group uu____11365
              | uu____11382 ->
                  let uu____11383 =
                    let uu____11385 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11385
                     in
                  failwith uu____11383))
    | uu____11388 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11414 = FStar_Ident.text_of_id id1  in str uu____11414
    | FStar_Parser_AST.Paren u1 ->
        let uu____11417 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11417
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11418;_},uu____11419::uu____11420::[])
        ->
        let uu____11424 = p_universeFrom u  in
        soft_parens_with_nesting uu____11424
    | FStar_Parser_AST.App uu____11425 ->
        let uu____11432 = p_universeFrom u  in
        soft_parens_with_nesting uu____11432
    | uu____11433 ->
        let uu____11434 =
          let uu____11436 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11436
           in
        failwith uu____11434

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
       | FStar_Parser_AST.Module (uu____11525,decls) ->
           let uu____11531 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11531
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11540,decls,uu____11542) ->
           let uu____11549 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11549
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11609  ->
         match uu____11609 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11631)) -> false
      | ([],uu____11635) -> false
      | uu____11639 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11649 -> true
         | uu____11651 -> false)
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
        | FStar_Parser_AST.Module (uu____11694,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11700,decls,uu____11702) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11754 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11767;
                 FStar_Parser_AST.doc = uu____11768;
                 FStar_Parser_AST.quals = uu____11769;
                 FStar_Parser_AST.attrs = uu____11770;_}::uu____11771 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11777 =
                   let uu____11780 =
                     let uu____11783 = FStar_List.tl ds  in d :: uu____11783
                      in
                   d0 :: uu____11780  in
                 (uu____11777, (d0.FStar_Parser_AST.drange))
             | uu____11788 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11754 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11845 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11845 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11954 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11954, comments1))))))
  