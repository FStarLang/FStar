open Prims
let (maybe_unthunk : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Abs (uu____8::[],body) -> body
    | uu____12 -> t
  
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
            let uu____112 = let uu____115 = f x  in uu____115 :: acc  in
            aux xs uu____112
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
            let uu____181 = f x  in
            (match uu____181 with
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
          let uu____237 = f x  in if uu____237 then all f xs else false
  
let (all1_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    (Prims.op_Negation (FStar_List.isEmpty args)) &&
      (FStar_Util.for_all
         (fun uu___0_274  ->
            match uu___0_274 with
            | (uu____280,FStar_Parser_AST.Nothing ) -> true
            | uu____282 -> false) args)
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____311 'Auu____312 .
    Prims.bool -> ('Auu____311 -> 'Auu____312) -> 'Auu____311 -> 'Auu____312
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
  'Auu____422 'Auu____423 .
    'Auu____422 ->
      ('Auu____423 -> 'Auu____422) ->
        'Auu____423 FStar_Pervasives_Native.option -> 'Auu____422
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
  'Auu____536 .
    FStar_Pprint.document ->
      ('Auu____536 -> FStar_Pprint.document) ->
        'Auu____536 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____561 =
          let uu____562 =
            let uu____563 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____563  in
          FStar_Pprint.separate_map uu____562 f l  in
        FStar_Pprint.group uu____561
  
let precede_break_separate_map :
  'Auu____575 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____575 -> FStar_Pprint.document) ->
          'Auu____575 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____605 =
            let uu____606 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____607 =
              let uu____608 = FStar_List.hd l  in
              FStar_All.pipe_right uu____608 f  in
            FStar_Pprint.precede uu____606 uu____607  in
          let uu____609 =
            let uu____610 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____616 =
                   let uu____617 =
                     let uu____618 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____618  in
                   FStar_Pprint.op_Hat_Hat sep uu____617  in
                 FStar_Pprint.op_Hat_Hat break1 uu____616) uu____610
             in
          FStar_Pprint.op_Hat_Hat uu____605 uu____609
  
let concat_break_map :
  'Auu____626 .
    ('Auu____626 -> FStar_Pprint.document) ->
      'Auu____626 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____646 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____650 = f x  in FStar_Pprint.op_Hat_Hat uu____650 break1)
          l
         in
      FStar_Pprint.group uu____646
  
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
    let uu____713 = str "begin"  in
    let uu____715 = str "end"  in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____713
      contents uu____715
  
let separate_map_last :
  'Auu____728 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____728 -> FStar_Pprint.document) ->
        'Auu____728 Prims.list -> FStar_Pprint.document
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
  'Auu____780 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____780 -> FStar_Pprint.document) ->
        'Auu____780 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____812 =
          let uu____813 =
            let uu____814 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____814  in
          separate_map_last uu____813 f l  in
        FStar_Pprint.group uu____812
  
let separate_map_or_flow :
  'Auu____824 .
    FStar_Pprint.document ->
      ('Auu____824 -> FStar_Pprint.document) ->
        'Auu____824 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____862 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____862 -> FStar_Pprint.document) ->
        'Auu____862 Prims.list -> FStar_Pprint.document
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
  'Auu____914 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____914 -> FStar_Pprint.document) ->
        'Auu____914 Prims.list -> FStar_Pprint.document
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
              let uu____996 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____996
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1018 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1018 -> FStar_Pprint.document) ->
                  'Auu____1018 Prims.list -> FStar_Pprint.document
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
                    (let uu____1077 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1077
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1097 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1097 -> FStar_Pprint.document) ->
                  'Auu____1097 Prims.list -> FStar_Pprint.document
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
                    (let uu____1156 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1156
                       closing)
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1166 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1182 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1182
      | uu____1185 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1236::(e2,uu____1238)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1261 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1285,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1296,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1317 = extract_from_list e2  in e1 :: uu____1317
    | uu____1320 ->
        let uu____1321 =
          let uu____1323 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1323  in
        failwith uu____1321
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1337;
           FStar_Parser_AST.level = uu____1338;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1340 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1352;
           FStar_Parser_AST.level = uu____1353;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1355;
                                                         FStar_Parser_AST.level
                                                           = uu____1356;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1358;
                                                    FStar_Parser_AST.level =
                                                      uu____1359;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1361;
                FStar_Parser_AST.level = uu____1362;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1364;
           FStar_Parser_AST.level = uu____1365;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1367 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1379 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1380;
           FStar_Parser_AST.range = uu____1381;
           FStar_Parser_AST.level = uu____1382;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1383;
                                                         FStar_Parser_AST.range
                                                           = uu____1384;
                                                         FStar_Parser_AST.level
                                                           = uu____1385;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1387;
                                                    FStar_Parser_AST.level =
                                                      uu____1388;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1389;
                FStar_Parser_AST.range = uu____1390;
                FStar_Parser_AST.level = uu____1391;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1393;
           FStar_Parser_AST.level = uu____1394;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1396 = extract_from_ref_set e1  in
        let uu____1399 = extract_from_ref_set e2  in
        FStar_List.append uu____1396 uu____1399
    | uu____1402 ->
        let uu____1403 =
          let uu____1405 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1405  in
        failwith uu____1403
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1417 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1417
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1426 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1426
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1437 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1437 Prims.int_zero  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1447 = FStar_Ident.text_of_id op  in uu____1447 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1517 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1537 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1548 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1559 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1585  ->
    match uu___1_1585 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1620  ->
      match uu___2_1620 with
      | FStar_Util.Inl c ->
          let uu____1633 = FStar_String.get s Prims.int_zero  in
          uu____1633 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1649 .
    Prims.string ->
      ('Auu____1649 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1673  ->
      match uu____1673 with
      | (assoc_levels,tokens) ->
          let uu____1705 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1705 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_1877 =
    match uu___3_1877 with
    | Left  -> (l, l, (l - Prims.int_one))
    | Right  -> ((l - Prims.int_one), l, l)
    | NonAssoc  -> ((l - Prims.int_one), l, (l - Prims.int_one))  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1927  ->
         match uu____1927 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2002 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2002 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2054) ->
          assoc_levels
      | uu____2092 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2125 . ('Auu____2125 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2174 =
        FStar_List.tryFind
          (fun uu____2210  ->
             match uu____2210 with
             | (uu____2227,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2174 with
      | FStar_Pervasives_Native.Some ((uu____2256,l1,uu____2258),uu____2259)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2309 =
            let uu____2311 =
              let uu____2313 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2313  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2311
             in
          failwith uu____2309
       in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2348 = assign_levels level_associativity_spec op  in
    match uu____2348 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - Prims.int_one), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2407 =
      let uu____2410 =
        let uu____2416 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2416  in
      FStar_List.tryFind uu____2410 operatorInfix0ad12  in
    uu____2407 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2483 =
      let uu____2498 =
        let uu____2516 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2516  in
      FStar_List.tryFind uu____2498 opinfix34  in
    uu____2483 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2582 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2582
    then Prims.int_one
    else
      (let uu____2595 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2595
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
  
let handleable_op :
  'Auu____2641 . FStar_Ident.ident -> 'Auu____2641 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2657 when _2657 = Prims.int_zero -> true
      | _2659 when _2659 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2661 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2661 ["-"; "~"])
      | _2669 when _2669 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2671 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2671
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2693 when _2693 = (Prims.of_int (3)) ->
          let uu____2694 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2694 [".()<-"; ".[]<-"]
      | uu____2702 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2748 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2800 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2842 -> true
      | uu____2848 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2881 = FStar_List.for_all is_binder_annot bs  in
          if uu____2881
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2896 -> (true, (l + Prims.int_one))  in
    let uu____2901 = all_binders e Prims.int_zero  in
    match uu____2901 with
    | (b,l) -> if b && (l > Prims.int_one) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____2940 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____2940
  
let (comment_stack :
  (Prims.string * FStar_Range.range) Prims.list FStar_ST.ref) =
  FStar_Util.mk_ref [] 
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  -> match projectee with | { r; has_qs; has_attrs;_} -> r 
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with | { r; has_qs; has_attrs;_} -> has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with | { r; has_qs; has_attrs;_} -> has_attrs
  
let (dummy_meta : decl_meta) =
  { r = FStar_Range.dummyRange; has_qs = false; has_attrs = false } 
let with_comment :
  'Auu____3029 .
    ('Auu____3029 -> FStar_Pprint.document) ->
      'Auu____3029 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3071 = FStar_ST.op_Bang comment_stack  in
          match uu____3071 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3142 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3142 FStar_Pprint.hardline  in
              let uu____3143 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3143
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3185 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3185 print_pos lookahead_pos))
              else
                (let uu____3188 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3188))
           in
        let uu____3191 =
          let uu____3197 =
            let uu____3198 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3198  in
          let uu____3199 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3197 uu____3199  in
        match uu____3191 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3208 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3208
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3220 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3220)
  
let with_comment_sep :
  'Auu____3232 'Auu____3233 .
    ('Auu____3232 -> 'Auu____3233) ->
      'Auu____3232 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3233)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3279 = FStar_ST.op_Bang comment_stack  in
          match uu____3279 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3350 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3350
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3392 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3396 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3396)
                     in
                  comments_before_pos uu____3392 print_pos lookahead_pos))
              else
                (let uu____3399 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3399))
           in
        let uu____3402 =
          let uu____3408 =
            let uu____3409 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3409  in
          let uu____3410 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3408 uu____3410  in
        match uu____3402 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3423 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3423
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
          fun doc  ->
            fun r  ->
              fun init1  ->
                let uu____3476 = FStar_ST.op_Bang comment_stack  in
                match uu____3476 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3570 =
                          let uu____3572 =
                            let uu____3574 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3574  in
                          uu____3572 - lbegin  in
                        max k uu____3570  in
                      let lnum1 = min (Prims.of_int (2)) lnum  in
                      let doc1 =
                        let uu____3579 =
                          let uu____3580 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3581 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3580 uu____3581  in
                        FStar_Pprint.op_Hat_Hat doc uu____3579  in
                      let uu____3582 =
                        let uu____3584 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3584  in
                      place_comments_until_pos Prims.int_one uu____3582 pos
                        meta_decl doc1 true init1))
                | uu____3587 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3600 = FStar_Range.line_of_pos pos  in
                         uu____3600 - lbegin  in
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
                         if init1 then (Prims.of_int (2)) else lnum4  in
                       let uu____3628 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc uu____3628)
  
let separate_map_with_comments :
  'Auu____3642 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3642 -> FStar_Pprint.document) ->
          'Auu____3642 Prims.list ->
            ('Auu____3642 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3701 x =
              match uu____3701 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3720 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3720 meta_decl doc false false
                     in
                  let uu____3724 =
                    let uu____3726 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3726  in
                  let uu____3727 =
                    let uu____3728 =
                      let uu____3729 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3729  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3728  in
                  (uu____3724, uu____3727)
               in
            let uu____3731 =
              let uu____3738 = FStar_List.hd xs  in
              let uu____3739 = FStar_List.tl xs  in (uu____3738, uu____3739)
               in
            match uu____3731 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3757 =
                    let uu____3759 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3759  in
                  let uu____3760 =
                    let uu____3761 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3761  in
                  (uu____3757, uu____3760)  in
                let uu____3763 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3763
  
let separate_map_with_comments_kw :
  'Auu____3790 'Auu____3791 .
    'Auu____3790 ->
      'Auu____3790 ->
        ('Auu____3790 -> 'Auu____3791 -> FStar_Pprint.document) ->
          'Auu____3791 Prims.list ->
            ('Auu____3791 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3855 x =
              match uu____3855 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3874 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3874 meta_decl doc false false
                     in
                  let uu____3878 =
                    let uu____3880 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3880  in
                  let uu____3881 =
                    let uu____3882 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3882  in
                  (uu____3878, uu____3881)
               in
            let uu____3884 =
              let uu____3891 = FStar_List.hd xs  in
              let uu____3892 = FStar_List.tl xs  in (uu____3891, uu____3892)
               in
            match uu____3884 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3910 =
                    let uu____3912 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3912  in
                  let uu____3913 = f prefix1 x  in (uu____3910, uu____3913)
                   in
                let uu____3915 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3915
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4871)) ->
          let uu____4874 =
            let uu____4876 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____4876 FStar_Util.is_upper  in
          if uu____4874
          then
            let uu____4882 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4882 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4885 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4892 = p_attributes d.FStar_Parser_AST.attrs  in
    let uu____4893 =
      let uu____4894 = p_rawDecl d  in
      FStar_Pprint.op_Hat_Hat qualifiers uu____4894  in
    FStar_Pprint.op_Hat_Hat uu____4892 uu____4893

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4896 ->
        let uu____4897 =
          let uu____4898 = str "@ "  in
          let uu____4900 =
            let uu____4901 =
              let uu____4902 =
                let uu____4903 =
                  let uu____4904 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4904  in
                FStar_Pprint.op_Hat_Hat uu____4903 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4902  in
            FStar_Pprint.op_Hat_Hat uu____4901 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4898 uu____4900  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4897

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4910 =
          let uu____4911 = str "val"  in
          let uu____4913 =
            let uu____4914 =
              let uu____4915 = p_lident lid  in
              let uu____4916 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4915 uu____4916  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4914  in
          FStar_Pprint.op_Hat_Hat uu____4911 uu____4913  in
        let uu____4917 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4910 uu____4917
    | FStar_Parser_AST.TopLevelLet (uu____4920,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4945 =
               let uu____4946 = str "let"  in p_letlhs uu____4946 lb false
                in
             FStar_Pprint.group uu____4945) lbs
    | uu____4949 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_4964 =
          match uu___4_4964 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4972 = f x  in
              let uu____4973 =
                let uu____4974 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4974  in
              FStar_Pprint.op_Hat_Hat uu____4972 uu____4973
           in
        let uu____4975 = str "["  in
        let uu____4977 =
          let uu____4978 = p_list' l  in
          let uu____4979 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4978 uu____4979  in
        FStar_Pprint.op_Hat_Hat uu____4975 uu____4977

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4983 =
          let uu____4984 = str "open"  in
          let uu____4986 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4984 uu____4986  in
        FStar_Pprint.group uu____4983
    | FStar_Parser_AST.Include uid ->
        let uu____4988 =
          let uu____4989 = str "include"  in
          let uu____4991 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4989 uu____4991  in
        FStar_Pprint.group uu____4988
    | FStar_Parser_AST.Friend uid ->
        let uu____4993 =
          let uu____4994 = str "friend"  in
          let uu____4996 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4994 uu____4996  in
        FStar_Pprint.group uu____4993
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4999 =
          let uu____5000 = str "module"  in
          let uu____5002 =
            let uu____5003 =
              let uu____5004 = p_uident uid1  in
              let uu____5005 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5004 uu____5005  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5003  in
          FStar_Pprint.op_Hat_Hat uu____5000 uu____5002  in
        let uu____5006 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4999 uu____5006
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5008 =
          let uu____5009 = str "module"  in
          let uu____5011 =
            let uu____5012 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5012  in
          FStar_Pprint.op_Hat_Hat uu____5009 uu____5011  in
        FStar_Pprint.group uu____5008
    | FStar_Parser_AST.Tycon
        (true ,uu____5013,(FStar_Parser_AST.TyconAbbrev
         (uid,tpars,FStar_Pervasives_Native.None ,t))::[])
        ->
        let effect_prefix_doc =
          let uu____5030 = str "effect"  in
          let uu____5032 =
            let uu____5033 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5033  in
          FStar_Pprint.op_Hat_Hat uu____5030 uu____5032  in
        let uu____5034 =
          let uu____5035 = p_typars tpars  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5035 FStar_Pprint.equals
           in
        let uu____5038 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5034 uu____5038
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5057 =
          let uu____5058 = FStar_List.hd tcdefs  in
          p_typeDeclWithKw s uu____5058  in
        let uu____5059 =
          let uu____5060 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5068 =
                    let uu____5069 = str "and"  in
                    p_typeDeclWithKw uu____5069 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5068)) uu____5060
           in
        FStar_Pprint.op_Hat_Hat uu____5057 uu____5059
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5086 = str "let"  in
          let uu____5088 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5086 uu____5088  in
        let uu____5089 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5089 p_letbinding lbs
          (fun uu____5099  ->
             match uu____5099 with
             | (p,t) ->
                 let uu____5106 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 { r = uu____5106; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5111 =
          let uu____5112 = str "val"  in
          let uu____5114 =
            let uu____5115 =
              let uu____5116 = p_lident lid  in
              let uu____5117 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5116 uu____5117  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5115  in
          FStar_Pprint.op_Hat_Hat uu____5112 uu____5114  in
        FStar_All.pipe_left FStar_Pprint.group uu____5111
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5122 =
            let uu____5124 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5124 FStar_Util.is_upper  in
          if uu____5122
          then FStar_Pprint.empty
          else
            (let uu____5132 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5132 FStar_Pprint.space)
           in
        let uu____5134 =
          let uu____5135 = p_ident id1  in
          let uu____5136 =
            let uu____5137 =
              let uu____5138 =
                let uu____5139 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5139  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5138  in
            FStar_Pprint.group uu____5137  in
          FStar_Pprint.op_Hat_Hat uu____5135 uu____5136  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5134
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5148 = str "exception"  in
        let uu____5150 =
          let uu____5151 =
            let uu____5152 = p_uident uid  in
            let uu____5153 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5157 =
                     let uu____5158 = str "of"  in
                     let uu____5160 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5158 uu____5160  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5157) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5152 uu____5153  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5151  in
        FStar_Pprint.op_Hat_Hat uu____5148 uu____5150
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5164 = str "new_effect"  in
        let uu____5166 =
          let uu____5167 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5167  in
        FStar_Pprint.op_Hat_Hat uu____5164 uu____5166
    | FStar_Parser_AST.SubEffect se ->
        let uu____5169 = str "sub_effect"  in
        let uu____5171 =
          let uu____5172 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5172  in
        FStar_Pprint.op_Hat_Hat uu____5169 uu____5171
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Main uu____5174 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5176,uu____5177) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5193 = str "%splice"  in
        let uu____5195 =
          let uu____5196 =
            let uu____5197 = str ";"  in p_list p_uident uu____5197 ids  in
          let uu____5199 =
            let uu____5200 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5200  in
          FStar_Pprint.op_Hat_Hat uu____5196 uu____5199  in
        FStar_Pprint.op_Hat_Hat uu____5193 uu____5195

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5203  ->
    match uu___5_5203 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5206 = str "#set-options"  in
        let uu____5208 =
          let uu____5209 =
            let uu____5210 = str s  in FStar_Pprint.dquotes uu____5210  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5209  in
        FStar_Pprint.op_Hat_Hat uu____5206 uu____5208
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5215 = str "#reset-options"  in
        let uu____5217 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5223 =
                 let uu____5224 = str s  in FStar_Pprint.dquotes uu____5224
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5223) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5215 uu____5217
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5229 = str "#push-options"  in
        let uu____5231 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5237 =
                 let uu____5238 = str s  in FStar_Pprint.dquotes uu____5238
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5237) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5229 uu____5231
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.RestartSolver  -> str "#restart-solver"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_typeDeclWithKw :
  FStar_Pprint.document -> FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun kw  ->
    fun typedecl  ->
      let uu____5271 = p_typeDecl kw typedecl  in
      match uu____5271 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5294 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5294
          else
            (let uu____5297 =
               let uu____5298 =
                 let uu____5299 =
                   let uu____5300 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5300 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5299  in
               let uu____5301 =
                 let uu____5302 =
                   let uu____5303 =
                     let uu____5304 =
                       let uu____5305 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5305  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5304
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5303  in
                 FStar_Pprint.op_Hat_Hat decl uu____5302  in
               FStar_Pprint.ifflat uu____5298 uu____5301  in
             FStar_All.pipe_left FStar_Pprint.group uu____5297)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5308  ->
      match uu___6_5308 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5331 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5331, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5348 = p_typ_sep false false t  in
          (match uu____5348 with
           | (comm,doc) ->
               let uu____5368 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5368, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5412 =
            match uu____5412 with
            | (lid1,t) ->
                let uu____5420 =
                  let uu____5425 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5425
                   in
                (match uu____5420 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5437 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5437  in
          let uu____5442 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5442, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5497 =
            match uu____5497 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5517 =
                    let uu____5518 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5518  in
                  FStar_Range.extend_to_end_of_line uu____5517  in
                let uu____5523 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5523 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5552 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5552, datacon_doc, jump2)

and (p_typeDeclPrefix :
  FStar_Pprint.document ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun kw  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            let with_kw cont =
              let lid_doc = p_ident lid  in
              let kw_lid =
                let uu____5580 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5580  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq1 then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5587 =
                    let uu____5588 =
                      let uu____5589 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5589 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5588  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5587
               in
            if bs = []
            then with_kw (fun n1  -> prefix2 n1 typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n1  ->
                    let uu____5609 =
                      let uu____5610 = FStar_Pprint.flow break1 binders  in
                      prefix2 n1 uu____5610  in
                    prefix2 uu____5609 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5612  ->
      match uu____5612 with
      | (lid,t) ->
          let uu____5620 =
            let uu____5621 = p_lident lid  in
            let uu____5622 =
              let uu____5623 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5623  in
            FStar_Pprint.op_Hat_Hat uu____5621 uu____5622  in
          FStar_Pprint.group uu____5620

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5625  ->
    match uu____5625 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5650 =
            let uu____5651 =
              let uu____5652 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5652  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5651  in
          FStar_Pprint.group uu____5650  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5656 =
               let uu____5657 =
                 let uu____5658 =
                   let uu____5659 =
                     let uu____5660 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5660
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5659  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5658  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5657  in
             FStar_Pprint.group uu____5656) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5664  ->
      fun inner_let  ->
        match uu____5664 with
        | (pat,uu____5672) ->
            let uu____5673 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5725 =
                    let uu____5732 =
                      let uu____5737 =
                        let uu____5738 =
                          let uu____5739 =
                            let uu____5740 = str "by"  in
                            let uu____5742 =
                              let uu____5743 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5743
                               in
                            FStar_Pprint.op_Hat_Hat uu____5740 uu____5742  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5739
                           in
                        FStar_Pprint.group uu____5738  in
                      (t, uu____5737)  in
                    FStar_Pervasives_Native.Some uu____5732  in
                  (pat1, uu____5725)
              | uu____5754 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5673 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5780);
                         FStar_Parser_AST.prange = uu____5781;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5798 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5798 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5804 =
                        if inner_let
                        then
                          let uu____5818 = pats_as_binders_if_possible pats
                             in
                          match uu____5818 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5841 = pats_as_binders_if_possible pats
                              in
                           match uu____5841 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5804 with
                       | (terms,style) ->
                           let uu____5868 =
                             let uu____5869 =
                               let uu____5870 =
                                 let uu____5871 = p_lident lid  in
                                 let uu____5872 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5871
                                   uu____5872
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5870
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5869  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5868)
                  | uu____5875 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5883 =
                              let uu____5884 =
                                let uu____5885 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5885
                                 in
                              FStar_Pprint.group uu____5884  in
                            FStar_Pprint.op_Hat_Hat uu____5883 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5896 =
                        let uu____5897 =
                          let uu____5898 =
                            let uu____5899 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5899  in
                          FStar_Pprint.group uu____5898  in
                        FStar_Pprint.op_Hat_Hat uu____5897 ascr_doc  in
                      FStar_Pprint.group uu____5896))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5901  ->
      match uu____5901 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5910 = p_term_sep false false e  in
          (match uu____5910 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5920 =
                 let uu____5921 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5921  in
               let uu____5922 =
                 let uu____5923 =
                   let uu____5924 =
                     let uu____5925 =
                       let uu____5926 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5926
                        in
                     FStar_Pprint.group uu____5925  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5924  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5923  in
               FStar_Pprint.ifflat uu____5920 uu____5922)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5927  ->
    match uu___7_5927 with
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
        let uu____5952 = p_uident uid  in
        let uu____5953 = p_binders true bs  in
        let uu____5955 =
          let uu____5956 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5956  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5952
          uu____5953 uu____5955

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
          let uu____5971 =
            let uu____5972 =
              let uu____5973 =
                let uu____5974 = p_uident uid  in
                let uu____5975 = p_binders true bs  in
                let uu____5977 =
                  let uu____5978 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5978  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____5974 uu____5975 uu____5977
                 in
              FStar_Pprint.group uu____5973  in
            let uu____5983 =
              let uu____5984 = str "with"  in
              let uu____5986 =
                let uu____5987 =
                  let uu____5988 =
                    let uu____5989 =
                      let uu____5990 =
                        let uu____5991 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5991
                         in
                      separate_map_last uu____5990 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5989  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5988  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5987  in
              FStar_Pprint.op_Hat_Hat uu____5984 uu____5986  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5972 uu____5983  in
          braces_with_nesting uu____5971

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____5995,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6008 =
            let uu____6009 = p_lident lid  in
            let uu____6010 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6009 uu____6010  in
          let uu____6011 = p_simpleTerm ps false e  in
          prefix2 uu____6008 uu____6011
      | uu____6013 ->
          let uu____6014 =
            let uu____6016 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6016
             in
          failwith uu____6014

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6099 =
        match uu____6099 with
        | (kwd,t) ->
            let uu____6110 =
              let uu____6111 = str kwd  in
              let uu____6112 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6111 uu____6112  in
            let uu____6113 = p_simpleTerm ps false t  in
            prefix2 uu____6110 uu____6113
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6120 =
      let uu____6121 =
        let uu____6122 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6123 =
          let uu____6124 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6124  in
        FStar_Pprint.op_Hat_Hat uu____6122 uu____6123  in
      let uu____6126 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6121 uu____6126  in
    let uu____6127 =
      let uu____6128 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6128  in
    FStar_Pprint.op_Hat_Hat uu____6120 uu____6127

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6129  ->
    match uu___8_6129 with
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
        let uu____6149 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6149 FStar_Pprint.hardline
    | uu____6150 ->
        let uu____6151 =
          let uu____6152 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6152  in
        FStar_Pprint.op_Hat_Hat uu____6151 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6155  ->
    match uu___9_6155 with
    | FStar_Parser_AST.Rec  ->
        let uu____6156 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6156
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6158  ->
    match uu___10_6158 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_tac t) ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6163,e) -> e
          | uu____6169 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6170 = str "#["  in
        let uu____6172 =
          let uu____6173 = p_term false false t1  in
          let uu____6176 =
            let uu____6177 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6177 break1  in
          FStar_Pprint.op_Hat_Hat uu____6173 uu____6176  in
        FStar_Pprint.op_Hat_Hat uu____6170 uu____6172
    | FStar_Parser_AST.Meta (FStar_Parser_AST.Arg_qualifier_meta_attr t) ->
        let uu____6180 = str "#[@"  in
        let uu____6182 =
          let uu____6183 = p_term false false t  in
          let uu____6186 =
            let uu____6187 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6187 break1  in
          FStar_Pprint.op_Hat_Hat uu____6183 uu____6186  in
        FStar_Pprint.op_Hat_Hat uu____6180 uu____6182

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6193 =
          let uu____6194 =
            let uu____6195 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6195  in
          FStar_Pprint.separate_map uu____6194 p_tuplePattern pats  in
        FStar_Pprint.group uu____6193
    | uu____6196 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6205 =
          let uu____6206 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6206 p_constructorPattern pats  in
        FStar_Pprint.group uu____6205
    | uu____6207 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6210;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6215 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6216 = p_constructorPattern hd1  in
        let uu____6217 = p_constructorPattern tl1  in
        infix0 uu____6215 uu____6216 uu____6217
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6219;_},pats)
        ->
        let uu____6225 = p_quident uid  in
        let uu____6226 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6225 uu____6226
    | uu____6227 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6243;
               FStar_Parser_AST.blevel = uu____6244;
               FStar_Parser_AST.aqual = uu____6245;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6254 =
               let uu____6255 = p_ident lid  in
               p_refinement aqual uu____6255 t1 phi  in
             soft_parens_with_nesting uu____6254
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6258;
               FStar_Parser_AST.blevel = uu____6259;
               FStar_Parser_AST.aqual = uu____6260;_},phi))
             ->
             let uu____6266 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6266
         | uu____6267 ->
             let uu____6272 =
               let uu____6273 = p_tuplePattern pat  in
               let uu____6274 =
                 let uu____6275 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6275
                  in
               FStar_Pprint.op_Hat_Hat uu____6273 uu____6274  in
             soft_parens_with_nesting uu____6272)
    | FStar_Parser_AST.PatList pats ->
        let uu____6279 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6279 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6298 =
          match uu____6298 with
          | (lid,pat) ->
              let uu____6305 = p_qlident lid  in
              let uu____6306 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6305 uu____6306
           in
        let uu____6307 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6307
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6319 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6320 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6321 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6319
          uu____6320 uu____6321
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6332 =
          let uu____6333 =
            let uu____6334 =
              let uu____6335 = FStar_Ident.text_of_id op  in str uu____6335
               in
            let uu____6337 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6334 uu____6337  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6333  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6332
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6341 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6341 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6349 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6350 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6349 uu____6350
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6352 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6356;
           FStar_Parser_AST.prange = uu____6357;_},uu____6358)
        ->
        let uu____6363 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6363
    | FStar_Parser_AST.PatTuple (uu____6364,false ) ->
        let uu____6371 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6371
    | uu____6372 ->
        let uu____6373 =
          let uu____6375 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6375  in
        failwith uu____6373

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6380;_},uu____6381)
        -> true
    | uu____6388 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6394) -> true
    | uu____6396 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6403 = p_binder' is_atomic b  in
      match uu____6403 with
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
          let uu____6440 =
            let uu____6441 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6442 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6441 uu____6442  in
          (uu____6440, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6448 = p_lident lid  in
          (uu____6448, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6455 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6466;
                   FStar_Parser_AST.blevel = uu____6467;
                   FStar_Parser_AST.aqual = uu____6468;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6473 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6473 t1 phi
            | uu____6474 ->
                let t' =
                  let uu____6476 = is_typ_tuple t  in
                  if uu____6476
                  then
                    let uu____6479 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6479
                  else p_tmFormula t  in
                let uu____6482 =
                  let uu____6483 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6484 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6483 uu____6484  in
                (uu____6482, t')
             in
          (match uu____6455 with
           | (b',t') ->
               let catf =
                 let uu____6502 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6502
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6509 =
                         let uu____6510 =
                           let uu____6511 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6511
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6510
                          in
                       FStar_Pprint.group uu____6509
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6516 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6516)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____6521 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6549;
                  FStar_Parser_AST.blevel = uu____6550;
                  FStar_Parser_AST.aqual = uu____6551;_},phi)
               ->
               let uu____6555 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6555 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6576 ->
               if is_atomic
               then
                 let uu____6588 = p_atomicTerm t  in
                 (uu____6588, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6595 = p_appTerm t  in
                  (uu____6595, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6606 = p_refinement' aqual_opt binder t phi  in
          match uu____6606 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____6622 -> false
            | FStar_Parser_AST.App uu____6634 -> false
            | FStar_Parser_AST.Op uu____6642 -> false
            | uu____6650 -> true  in
          let uu____6652 = p_noSeqTerm false false phi  in
          match uu____6652 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6669 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6669)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____6678 =
                let uu____6679 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6679 binder  in
              let uu____6680 =
                let uu____6681 = p_appTerm t  in
                let uu____6682 =
                  let uu____6683 =
                    let uu____6684 =
                      let uu____6685 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6686 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6685 uu____6686  in
                    FStar_Pprint.group uu____6684  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6683
                   in
                FStar_Pprint.op_Hat_Hat uu____6681 uu____6682  in
              (uu____6678, uu____6680)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6700 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6700

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6704 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6707 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6707)
       in
    if uu____6704
    then FStar_Pprint.underscore
    else (let uu____6712 = FStar_Ident.text_of_id lid  in str uu____6712)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6715 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6718 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6718)
       in
    if uu____6715
    then FStar_Pprint.underscore
    else (let uu____6723 = FStar_Ident.text_of_lid lid  in str uu____6723)

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
    fun doc  ->
      fun sep  ->
        if comm = FStar_Pprint.empty
        then
          let uu____6744 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6744
        else
          (let uu____6747 =
             let uu____6748 =
               let uu____6749 =
                 let uu____6750 =
                   let uu____6751 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6751  in
                 FStar_Pprint.op_Hat_Hat doc uu____6750  in
               FStar_Pprint.group uu____6749  in
             let uu____6752 =
               let uu____6753 =
                 let uu____6754 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6754  in
               FStar_Pprint.op_Hat_Hat comm uu____6753  in
             FStar_Pprint.ifflat uu____6748 uu____6752  in
           FStar_All.pipe_left FStar_Pprint.group uu____6747)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6762 = p_noSeqTerm true false e1  in
            (match uu____6762 with
             | (comm,t1) ->
                 let uu____6771 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6772 =
                   let uu____6773 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6773
                    in
                 FStar_Pprint.op_Hat_Hat uu____6771 uu____6772)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6777 =
              let uu____6778 =
                let uu____6779 =
                  let uu____6780 = p_lident x  in
                  let uu____6781 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6780 uu____6781  in
                let uu____6782 =
                  let uu____6783 = p_noSeqTermAndComment true false e1  in
                  let uu____6786 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6783 uu____6786  in
                op_Hat_Slash_Plus_Hat uu____6779 uu____6782  in
              FStar_Pprint.group uu____6778  in
            let uu____6787 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6777 uu____6787
        | uu____6788 ->
            let uu____6789 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6789

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
            let uu____6801 = p_noSeqTerm true false e1  in
            (match uu____6801 with
             | (comm,t1) ->
                 let uu____6814 =
                   let uu____6815 =
                     let uu____6816 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6816  in
                   let uu____6817 =
                     let uu____6818 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6818
                      in
                   FStar_Pprint.op_Hat_Hat uu____6815 uu____6817  in
                 (comm, uu____6814))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6822 =
              let uu____6823 =
                let uu____6824 =
                  let uu____6825 =
                    let uu____6826 = p_lident x  in
                    let uu____6827 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6826 uu____6827  in
                  let uu____6828 =
                    let uu____6829 = p_noSeqTermAndComment true false e1  in
                    let uu____6832 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6829 uu____6832  in
                  op_Hat_Slash_Plus_Hat uu____6825 uu____6828  in
                FStar_Pprint.group uu____6824  in
              let uu____6833 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6823 uu____6833  in
            (FStar_Pprint.empty, uu____6822)
        | uu____6834 -> p_noSeqTerm ps pb e

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
            let uu____6854 =
              let uu____6855 = p_tmIff e1  in
              let uu____6856 =
                let uu____6857 =
                  let uu____6858 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6858
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6857  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6855 uu____6856  in
            FStar_Pprint.group uu____6854
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6864 =
              let uu____6865 = p_tmIff e1  in
              let uu____6866 =
                let uu____6867 =
                  let uu____6868 =
                    let uu____6869 = p_typ false false t  in
                    let uu____6872 =
                      let uu____6873 = str "by"  in
                      let uu____6875 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6873 uu____6875  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6869 uu____6872  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6868
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6867  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6865 uu____6866  in
            FStar_Pprint.group uu____6864
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____6876;_},e1::e2::e3::[])
            ->
            let uu____6883 =
              let uu____6884 =
                let uu____6885 =
                  let uu____6886 = p_atomicTermNotQUident e1  in
                  let uu____6887 =
                    let uu____6888 =
                      let uu____6889 =
                        let uu____6890 = p_term false false e2  in
                        soft_parens_with_nesting uu____6890  in
                      let uu____6893 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6889 uu____6893  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6888  in
                  FStar_Pprint.op_Hat_Hat uu____6886 uu____6887  in
                FStar_Pprint.group uu____6885  in
              let uu____6894 =
                let uu____6895 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6895  in
              FStar_Pprint.op_Hat_Hat uu____6884 uu____6894  in
            FStar_Pprint.group uu____6883
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____6896;_},e1::e2::e3::[])
            ->
            let uu____6903 =
              let uu____6904 =
                let uu____6905 =
                  let uu____6906 = p_atomicTermNotQUident e1  in
                  let uu____6907 =
                    let uu____6908 =
                      let uu____6909 =
                        let uu____6910 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6910  in
                      let uu____6913 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6909 uu____6913  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6908  in
                  FStar_Pprint.op_Hat_Hat uu____6906 uu____6907  in
                FStar_Pprint.group uu____6905  in
              let uu____6914 =
                let uu____6915 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6915  in
              FStar_Pprint.op_Hat_Hat uu____6904 uu____6914  in
            FStar_Pprint.group uu____6903
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6925 =
              let uu____6926 = str "requires"  in
              let uu____6928 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6926 uu____6928  in
            FStar_Pprint.group uu____6925
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6938 =
              let uu____6939 = str "ensures"  in
              let uu____6941 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6939 uu____6941  in
            FStar_Pprint.group uu____6938
        | FStar_Parser_AST.Attributes es ->
            let uu____6945 =
              let uu____6946 = str "attributes"  in
              let uu____6948 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6946 uu____6948  in
            FStar_Pprint.group uu____6945
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____6953 =
                let uu____6954 =
                  let uu____6955 = str "if"  in
                  let uu____6957 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____6955 uu____6957  in
                let uu____6960 =
                  let uu____6961 = str "then"  in
                  let uu____6963 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____6961 uu____6963  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6954 uu____6960  in
              FStar_Pprint.group uu____6953
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____6967,uu____6968,e31) when
                     is_unit e31 ->
                     let uu____6970 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____6970
                 | uu____6973 -> p_noSeqTermAndComment false false e2  in
               let uu____6976 =
                 let uu____6977 =
                   let uu____6978 = str "if"  in
                   let uu____6980 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____6978 uu____6980  in
                 let uu____6983 =
                   let uu____6984 =
                     let uu____6985 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____6985 e2_doc  in
                   let uu____6987 =
                     let uu____6988 = str "else"  in
                     let uu____6990 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____6988 uu____6990  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____6984 uu____6987  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____6977 uu____6983  in
               FStar_Pprint.group uu____6976)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7013 =
              let uu____7014 =
                let uu____7015 =
                  let uu____7016 = str "try"  in
                  let uu____7018 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7016 uu____7018  in
                let uu____7021 =
                  let uu____7022 = str "with"  in
                  let uu____7024 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7022 uu____7024  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7015 uu____7021  in
              FStar_Pprint.group uu____7014  in
            let uu____7033 = paren_if (ps || pb)  in uu____7033 uu____7013
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7060 =
              let uu____7061 =
                let uu____7062 =
                  let uu____7063 = str "match"  in
                  let uu____7065 = p_noSeqTermAndComment false false e1  in
                  let uu____7068 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7063 uu____7065 uu____7068
                   in
                let uu____7072 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7062 uu____7072  in
              FStar_Pprint.group uu____7061  in
            let uu____7081 = paren_if (ps || pb)  in uu____7081 uu____7060
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7088 =
              let uu____7089 =
                let uu____7090 =
                  let uu____7091 = str "let open"  in
                  let uu____7093 = p_quident uid  in
                  let uu____7094 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7091 uu____7093 uu____7094
                   in
                let uu____7098 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7090 uu____7098  in
              FStar_Pprint.group uu____7089  in
            let uu____7100 = paren_if ps  in uu____7100 uu____7088
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7165 is_last =
              match uu____7165 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7199 =
                          let uu____7200 = str "let"  in
                          let uu____7202 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7200 uu____7202
                           in
                        FStar_Pprint.group uu____7199
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7205 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7211 = p_term_sep false false e2  in
                  (match uu____7211 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7221 =
                         if is_last
                         then
                           let uu____7223 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7224 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7223 doc_expr1 uu____7224
                         else
                           (let uu____7230 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7230)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7221)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7281 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7281
                     else
                       (let uu____7286 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7286)) lbs
               in
            let lbs_doc =
              let uu____7290 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7290  in
            let uu____7291 =
              let uu____7292 =
                let uu____7293 =
                  let uu____7294 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7294
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7293  in
              FStar_Pprint.group uu____7292  in
            let uu____7296 = paren_if ps  in uu____7296 uu____7291
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7303;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7306;
                                                             FStar_Parser_AST.level
                                                               = uu____7307;_})
            when matches_var maybe_x x ->
            let uu____7334 =
              let uu____7335 =
                let uu____7336 = str "function"  in
                let uu____7338 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7336 uu____7338  in
              FStar_Pprint.group uu____7335  in
            let uu____7347 = paren_if (ps || pb)  in uu____7347 uu____7334
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7353 =
              let uu____7354 = str "quote"  in
              let uu____7356 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7354 uu____7356  in
            FStar_Pprint.group uu____7353
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7358 =
              let uu____7359 = str "`"  in
              let uu____7361 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7359 uu____7361  in
            FStar_Pprint.group uu____7358
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7363 =
              let uu____7364 = str "`%"  in
              let uu____7366 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7364 uu____7366  in
            FStar_Pprint.group uu____7363
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7368;
              FStar_Parser_AST.level = uu____7369;_}
            ->
            let uu____7370 =
              let uu____7371 = str "`@"  in
              let uu____7373 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7371 uu____7373  in
            FStar_Pprint.group uu____7370
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7375 =
              let uu____7376 = str "`#"  in
              let uu____7378 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7376 uu____7378  in
            FStar_Pprint.group uu____7375
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7387 = str "calc"  in
              let uu____7389 =
                let uu____7390 =
                  let uu____7391 = p_noSeqTermAndComment false false rel  in
                  let uu____7394 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7391 uu____7394  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7390  in
              FStar_Pprint.op_Hat_Hat uu____7387 uu____7389  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7396 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7397 =
              let uu____7398 =
                let uu____7399 =
                  let uu____7400 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7403 =
                    let uu____7404 = str ";"  in
                    let uu____7406 =
                      let uu____7407 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7407
                       in
                    FStar_Pprint.op_Hat_Hat uu____7404 uu____7406  in
                  FStar_Pprint.op_Hat_Hat uu____7400 uu____7403  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7399  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7398
               in
            FStar_Pprint.enclose head1 uu____7396 uu____7397
        | uu____7409 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7410  ->
    fun uu____7411  ->
      match uu____7411 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7416 =
            let uu____7417 = p_noSeqTermAndComment false false rel  in
            let uu____7420 =
              let uu____7421 =
                let uu____7422 =
                  let uu____7423 =
                    let uu____7424 = p_noSeqTermAndComment false false just
                       in
                    let uu____7427 =
                      let uu____7428 =
                        let uu____7429 =
                          let uu____7430 =
                            let uu____7431 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7434 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7431 uu____7434  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7430
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7429
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7428
                       in
                    FStar_Pprint.op_Hat_Hat uu____7424 uu____7427  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7423  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7422  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7421  in
            FStar_Pprint.op_Hat_Hat uu____7417 uu____7420  in
          FStar_Pprint.group uu____7416

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7436  ->
    match uu___11_7436 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7448 =
          let uu____7449 = str "[@"  in
          let uu____7451 =
            let uu____7452 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7453 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7452 uu____7453  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7449 uu____7451  in
        FStar_Pprint.group uu____7448

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
        | FStar_Parser_AST.QForall (bs,(uu____7471,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7505 =
                   let uu____7506 =
                     let uu____7507 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7507 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7506 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7505 term_doc
             | pats ->
                 let uu____7515 =
                   let uu____7516 =
                     let uu____7517 =
                       let uu____7518 =
                         let uu____7519 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7519
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7518 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7522 = p_trigger trigger  in
                     prefix2 uu____7517 uu____7522  in
                   FStar_Pprint.group uu____7516  in
                 prefix2 uu____7515 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7524,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7558 =
                   let uu____7559 =
                     let uu____7560 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7560 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7559 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7558 term_doc
             | pats ->
                 let uu____7568 =
                   let uu____7569 =
                     let uu____7570 =
                       let uu____7571 =
                         let uu____7572 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7572
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7571 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7575 = p_trigger trigger  in
                     prefix2 uu____7570 uu____7575  in
                   FStar_Pprint.group uu____7569  in
                 prefix2 uu____7568 term_doc)
        | uu____7576 -> p_simpleTerm ps pb e

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
      let uu____7597 = all_binders_annot t  in
      if uu____7597
      then
        let uu____7600 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7600
      else
        (let uu____7611 =
           let uu____7612 =
             let uu____7613 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7613  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7612  in
         FStar_Pprint.group uu____7611)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7672 = x  in
      match uu____7672 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____7737 = hd1  in
               (match uu____7737 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____7809 = cb  in
      match uu____7809 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____7828 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7834 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7834) hd1 tl1
                  in
               cat_with_colon uu____7828 typ)
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
                 FStar_Parser_AST.brange = uu____7913;
                 FStar_Parser_AST.blevel = uu____7914;
                 FStar_Parser_AST.aqual = uu____7915;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____7924 =
                 let uu____7929 = p_ident lid  in
                 p_refinement' aqual uu____7929 t1 phi  in
               FStar_Pervasives_Native.Some uu____7924
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7936) ->
               let uu____7941 =
                 let uu____7946 =
                   let uu____7947 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____7948 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____7947 uu____7948  in
                 let uu____7949 = p_tmEqNoRefinement t  in
                 (uu____7946, uu____7949)  in
               FStar_Pervasives_Native.Some uu____7941
           | uu____7954 -> FStar_Pervasives_Native.None)
      | uu____7963 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____7976 -> false
      | uu____7988 -> true  in
    let uu____7990 = map_if_all all_binders pats  in
    match uu____7990 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8022 = collapse_pats bs  in
        (uu____8022, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8039 = FStar_List.map p_atomicPattern pats  in
        (uu____8039, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8051 -> str "forall"
    | FStar_Parser_AST.QExists uu____8071 -> str "exists"
    | uu____8091 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8093  ->
    match uu___12_8093 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8105 =
          let uu____8106 =
            let uu____8107 =
              let uu____8108 = str "pattern"  in
              let uu____8110 =
                let uu____8111 =
                  let uu____8112 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8112
                   in
                FStar_Pprint.op_Hat_Hat uu____8111 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8108 uu____8110  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8107  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8106  in
        FStar_Pprint.group uu____8105

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8120 = str "\\/"  in
    FStar_Pprint.separate_map uu____8120 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8127 =
      let uu____8128 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8128 p_appTerm pats  in
    FStar_Pprint.group uu____8127

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8140 = p_term_sep false pb e1  in
            (match uu____8140 with
             | (comm,doc) ->
                 let prefix1 =
                   let uu____8149 = str "fun"  in
                   let uu____8151 =
                     let uu____8152 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8152
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8149 uu____8151  in
                 let uu____8153 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8155 =
                       let uu____8156 =
                         let uu____8157 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8157  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8156
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8155
                   else
                     (let uu____8160 = op_Hat_Slash_Plus_Hat prefix1 doc  in
                      FStar_Pprint.group uu____8160)
                    in
                 let uu____8161 = paren_if ps  in uu____8161 uu____8153)
        | uu____8166 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8174  ->
      match uu____8174 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8198 =
                    let uu____8199 =
                      let uu____8200 =
                        let uu____8201 = p_tuplePattern p  in
                        let uu____8202 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8201 uu____8202  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8200
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8199  in
                  FStar_Pprint.group uu____8198
              | FStar_Pervasives_Native.Some f ->
                  let uu____8204 =
                    let uu____8205 =
                      let uu____8206 =
                        let uu____8207 =
                          let uu____8208 =
                            let uu____8209 = p_tuplePattern p  in
                            let uu____8210 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8209
                              uu____8210
                             in
                          FStar_Pprint.group uu____8208  in
                        let uu____8212 =
                          let uu____8213 =
                            let uu____8216 = p_tmFormula f  in
                            [uu____8216; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8213  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8207 uu____8212
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8206
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8205  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8204
               in
            let uu____8218 = p_term_sep false pb e  in
            match uu____8218 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8228 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8228
                   else
                     (let uu____8231 =
                        let uu____8232 =
                          let uu____8233 =
                            let uu____8234 =
                              let uu____8235 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8235  in
                            op_Hat_Slash_Plus_Hat branch uu____8234  in
                          FStar_Pprint.group uu____8233  in
                        let uu____8236 =
                          let uu____8237 =
                            let uu____8238 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8238  in
                          FStar_Pprint.op_Hat_Hat branch uu____8237  in
                        FStar_Pprint.ifflat uu____8232 uu____8236  in
                      FStar_Pprint.group uu____8231))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8242 =
                       let uu____8243 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8243  in
                     op_Hat_Slash_Plus_Hat branch uu____8242)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8254 =
                      let uu____8255 =
                        let uu____8256 =
                          let uu____8257 =
                            let uu____8258 =
                              let uu____8259 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8259  in
                            FStar_Pprint.separate_map uu____8258
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8257
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8256
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8255  in
                    FStar_Pprint.group uu____8254
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8261 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8263;_},e1::e2::[])
        ->
        let uu____8269 = str "<==>"  in
        let uu____8271 = p_tmImplies e1  in
        let uu____8272 = p_tmIff e2  in
        infix0 uu____8269 uu____8271 uu____8272
    | uu____8273 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8275;_},e1::e2::[])
        ->
        let uu____8281 = str "==>"  in
        let uu____8283 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8289 = p_tmImplies e2  in
        infix0 uu____8281 uu____8283 uu____8289
    | uu____8290 ->
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
          let uu____8304 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8304 with
          | (terms',last1) ->
              let uu____8324 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8359 =
                      let uu____8360 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8360
                       in
                    let uu____8361 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8359, uu____8361)
                | Binders (n1,ln,parens1) ->
                    let uu____8375 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8383 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8375, break1, uu____8383)
                 in
              (match uu____8324 with
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
                    | _8416 when _8416 = Prims.int_one -> FStar_List.hd terms
                    | uu____8417 ->
                        let uu____8418 =
                          let uu____8419 =
                            let uu____8420 =
                              let uu____8421 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8422 =
                                let uu____8423 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8423
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8421 uu____8422
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8420  in
                          let uu____8424 =
                            let uu____8425 =
                              let uu____8426 =
                                let uu____8427 =
                                  let uu____8428 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8428  in
                                let uu____8429 =
                                  let uu____8430 =
                                    let uu____8431 =
                                      let uu____8432 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8433 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8439 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8439)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8432
                                        uu____8433
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8431
                                     in
                                  jump2 uu____8430  in
                                FStar_Pprint.ifflat uu____8427 uu____8429  in
                              FStar_Pprint.group uu____8426  in
                            let uu____8441 =
                              let uu____8442 =
                                let uu____8443 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8443  in
                              FStar_Pprint.align uu____8442  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8425
                              uu____8441
                             in
                          FStar_Pprint.ifflat uu____8419 uu____8424  in
                        FStar_Pprint.group uu____8418))

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
            | Arrows uu____8457 -> p_tmArrow' p_Tm e
            | Binders uu____8464 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8487 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8493 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8487 uu____8493
      | uu____8496 -> let uu____8497 = p_Tm e  in [uu____8497]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8550 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8576 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8550 uu____8576
        | uu____8599 ->
            let uu____8600 =
              let uu____8611 = p_Tm1 e1  in
              (uu____8611, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8600]
         in
      let fold_fun bs x =
        let uu____8709 = x  in
        match uu____8709 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____8841 = hd1  in
                 (match uu____8841 with
                  | (b2s,t2,uu____8870) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____8972 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9029 = cb  in
        match uu____9029 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9058 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9069 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9075 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9075) hd1 tl1
                         in
                      f uu____9069 typ))
         in
      let binders =
        let uu____9091 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9091  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9154 =
        let uu____9155 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9155 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9154  in
    let disj =
      let uu____9158 =
        let uu____9159 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9159 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9158  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9179;_},e1::e2::[])
        ->
        let uu____9185 = p_tmDisjunction e1  in
        let uu____9190 = let uu____9195 = p_tmConjunction e2  in [uu____9195]
           in
        FStar_List.append uu____9185 uu____9190
    | uu____9204 -> let uu____9205 = p_tmConjunction e  in [uu____9205]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9215;_},e1::e2::[])
        ->
        let uu____9221 = p_tmConjunction e1  in
        let uu____9224 = let uu____9227 = p_tmTuple e2  in [uu____9227]  in
        FStar_List.append uu____9221 uu____9224
    | uu____9228 -> let uu____9229 = p_tmTuple e  in [uu____9229]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9246 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9246
          (fun uu____9254  ->
             match uu____9254 with | (e1,uu____9260) -> p_tmEq e1) args
    | uu____9261 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9270 =
             let uu____9271 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9271  in
           FStar_Pprint.group uu____9270)

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
               (let uu____9290 = FStar_Ident.text_of_id op  in
                uu____9290 = "="))
              ||
              (let uu____9295 = FStar_Ident.text_of_id op  in
               uu____9295 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9301 = levels op1  in
            (match uu____9301 with
             | (left1,mine,right1) ->
                 let uu____9320 =
                   let uu____9321 = FStar_All.pipe_left str op1  in
                   let uu____9323 = p_tmEqWith' p_X left1 e1  in
                   let uu____9324 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9321 uu____9323 uu____9324  in
                 paren_if_gt curr mine uu____9320)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9325;_},e1::e2::[])
            ->
            let uu____9331 =
              let uu____9332 = p_tmEqWith p_X e1  in
              let uu____9333 =
                let uu____9334 =
                  let uu____9335 =
                    let uu____9336 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9336  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9335  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9334  in
              FStar_Pprint.op_Hat_Hat uu____9332 uu____9333  in
            FStar_Pprint.group uu____9331
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9337;_},e1::[])
            ->
            let uu____9342 = levels "-"  in
            (match uu____9342 with
             | (left1,mine,right1) ->
                 let uu____9362 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9362)
        | uu____9363 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9411)::(e2,uu____9413)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9433 = is_list e  in Prims.op_Negation uu____9433)
              ->
              let op = "::"  in
              let uu____9438 = levels op  in
              (match uu____9438 with
               | (left1,mine,right1) ->
                   let uu____9457 =
                     let uu____9458 = str op  in
                     let uu____9459 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9461 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9458 uu____9459 uu____9461  in
                   paren_if_gt curr mine uu____9457)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9480 = levels op  in
              (match uu____9480 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9514 = p_binder false b  in
                         let uu____9516 =
                           let uu____9517 =
                             let uu____9518 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9518 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9517
                            in
                         FStar_Pprint.op_Hat_Hat uu____9514 uu____9516
                     | FStar_Util.Inr t ->
                         let uu____9520 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____9522 =
                           let uu____9523 =
                             let uu____9524 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9524 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9523
                            in
                         FStar_Pprint.op_Hat_Hat uu____9520 uu____9522
                      in
                   let uu____9525 =
                     let uu____9526 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9531 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____9526 uu____9531  in
                   paren_if_gt curr mine uu____9525)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____9533;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____9563 = levels op  in
              (match uu____9563 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____9583 = str op  in
                     let uu____9584 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____9586 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____9583 uu____9584 uu____9586
                   else
                     (let uu____9590 =
                        let uu____9591 = str op  in
                        let uu____9592 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____9594 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____9591 uu____9592 uu____9594  in
                      paren_if_gt curr mine uu____9590))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9603 = levels op1  in
              (match uu____9603 with
               | (left1,mine,right1) ->
                   let uu____9622 =
                     let uu____9623 = str op1  in
                     let uu____9624 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9626 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9623 uu____9624 uu____9626  in
                   paren_if_gt curr mine uu____9622)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9646 =
                let uu____9647 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9648 =
                  let uu____9649 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9649 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9647 uu____9648  in
              braces_with_nesting uu____9646
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____9654;_},e1::[])
              ->
              let uu____9659 =
                let uu____9660 = str "~"  in
                let uu____9662 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9660 uu____9662  in
              FStar_Pprint.group uu____9659
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____9664;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____9673 = levels op  in
                   (match uu____9673 with
                    | (left1,mine,right1) ->
                        let uu____9692 =
                          let uu____9693 = str op  in
                          let uu____9694 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____9696 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____9693 uu____9694 uu____9696  in
                        paren_if_gt curr mine uu____9692)
               | uu____9698 -> p_X e)
          | uu____9699 -> p_X e

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
        let uu____9706 =
          let uu____9707 = p_lident lid  in
          let uu____9708 =
            let uu____9709 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9709  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9707 uu____9708  in
        FStar_Pprint.group uu____9706
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9712 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9714 = p_appTerm e  in
    let uu____9715 =
      let uu____9716 =
        let uu____9717 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9717 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9716  in
    FStar_Pprint.op_Hat_Hat uu____9714 uu____9715

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9723 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9723 t phi
      | FStar_Parser_AST.TAnnotated uu____9724 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9730 ->
          let uu____9731 =
            let uu____9733 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9733
             in
          failwith uu____9731
      | FStar_Parser_AST.TVariable uu____9736 ->
          let uu____9737 =
            let uu____9739 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9739
             in
          failwith uu____9737
      | FStar_Parser_AST.NoName uu____9742 ->
          let uu____9743 =
            let uu____9745 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9745
             in
          failwith uu____9743

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9749  ->
      match uu____9749 with
      | (lid,e) ->
          let uu____9757 =
            let uu____9758 = p_qlident lid  in
            let uu____9759 =
              let uu____9760 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9760
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9758 uu____9759  in
          FStar_Pprint.group uu____9757

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9763 when is_general_application e ->
        let uu____9770 = head_and_args e  in
        (match uu____9770 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9817 = p_argTerm e1  in
                  let uu____9818 =
                    let uu____9819 =
                      let uu____9820 =
                        let uu____9821 = str "`"  in
                        let uu____9823 =
                          let uu____9824 = p_indexingTerm head1  in
                          let uu____9825 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9824 uu____9825  in
                        FStar_Pprint.op_Hat_Hat uu____9821 uu____9823  in
                      FStar_Pprint.group uu____9820  in
                    let uu____9827 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9819 uu____9827  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9817 uu____9818
              | uu____9828 ->
                  let uu____9835 =
                    let uu____9846 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9846
                    then
                      let uu____9880 =
                        FStar_Util.take
                          (fun uu____9904  ->
                             match uu____9904 with
                             | (uu____9910,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9880 with
                      | (fs_typ_args,args1) ->
                          let uu____9948 =
                            let uu____9949 = p_indexingTerm head1  in
                            let uu____9950 =
                              let uu____9951 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____9951
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____9949 uu____9950  in
                          (uu____9948, args1)
                    else
                      (let uu____9966 = p_indexingTerm head1  in
                       (uu____9966, args))
                     in
                  (match uu____9835 with
                   | (head_doc,args1) ->
                       let uu____9987 =
                         let uu____9988 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____9988 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____9987)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10010 =
             (is_dtuple_constructor lid) && (all1_explicit args)  in
           Prims.op_Negation uu____10010)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10029 =
               let uu____10030 = p_quident lid  in
               let uu____10031 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10030 uu____10031  in
             FStar_Pprint.group uu____10029
         | hd1::tl1 ->
             let uu____10048 =
               let uu____10049 =
                 let uu____10050 =
                   let uu____10051 = p_quident lid  in
                   let uu____10052 = p_argTerm hd1  in
                   prefix2 uu____10051 uu____10052  in
                 FStar_Pprint.group uu____10050  in
               let uu____10053 =
                 let uu____10054 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10054  in
               FStar_Pprint.op_Hat_Hat uu____10049 uu____10053  in
             FStar_Pprint.group uu____10048)
    | uu____10059 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10070 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10070 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10074 = str "#"  in
        let uu____10076 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10074 uu____10076
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10079 = str "#["  in
        let uu____10081 =
          let uu____10082 = p_indexingTerm t  in
          let uu____10083 =
            let uu____10084 = str "]"  in
            let uu____10086 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10084 uu____10086  in
          FStar_Pprint.op_Hat_Hat uu____10082 uu____10083  in
        FStar_Pprint.op_Hat_Hat uu____10079 uu____10081
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10089  ->
    match uu____10089 with | (e,uu____10095) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10100;_},e1::e2::[])
          ->
          let uu____10106 =
            let uu____10107 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10108 =
              let uu____10109 =
                let uu____10110 = p_term false false e2  in
                soft_parens_with_nesting uu____10110  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10109  in
            FStar_Pprint.op_Hat_Hat uu____10107 uu____10108  in
          FStar_Pprint.group uu____10106
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10113;_},e1::e2::[])
          ->
          let uu____10119 =
            let uu____10120 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10121 =
              let uu____10122 =
                let uu____10123 = p_term false false e2  in
                soft_brackets_with_nesting uu____10123  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10122  in
            FStar_Pprint.op_Hat_Hat uu____10120 uu____10121  in
          FStar_Pprint.group uu____10119
      | uu____10126 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10131 = p_quident lid  in
        let uu____10132 =
          let uu____10133 =
            let uu____10134 = p_term false false e1  in
            soft_parens_with_nesting uu____10134  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10133  in
        FStar_Pprint.op_Hat_Hat uu____10131 uu____10132
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10142 =
          let uu____10143 = FStar_Ident.text_of_id op  in str uu____10143  in
        let uu____10145 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10142 uu____10145
    | uu____10146 -> p_atomicTermNotQUident e

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
         | uu____10159 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10168 =
          let uu____10169 = FStar_Ident.text_of_id op  in str uu____10169  in
        let uu____10171 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10168 uu____10171
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10175 =
          let uu____10176 =
            let uu____10177 =
              let uu____10178 = FStar_Ident.text_of_id op  in str uu____10178
               in
            let uu____10180 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10177 uu____10180  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10176  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10175
    | FStar_Parser_AST.Construct (lid,args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10195 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____10196 =
          let uu____10197 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____10197
            (fun uu____10205  ->
               match uu____10205 with | (e1,uu____10211) -> p_tmEq e1) args
           in
        let uu____10212 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10195
          uu____10196 uu____10212
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10217 =
          let uu____10218 = p_atomicTermNotQUident e1  in
          let uu____10219 =
            let uu____10220 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10220  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10218
            uu____10219
           in
        FStar_Pprint.group uu____10217
    | uu____10223 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10228 = p_quident constr_lid  in
        let uu____10229 =
          let uu____10230 =
            let uu____10231 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10231  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10230  in
        FStar_Pprint.op_Hat_Hat uu____10228 uu____10229
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10233 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10233 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10235 = p_term_sep false false e1  in
        (match uu____10235 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10248 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10248))
    | uu____10249 when is_array e ->
        let es = extract_from_list e  in
        let uu____10253 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10254 =
          let uu____10255 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10255
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10260 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10253
          uu____10254 uu____10260
    | uu____10263 when is_list e ->
        let uu____10264 =
          let uu____10265 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10266 = extract_from_list e  in
          separate_map_or_flow_last uu____10265
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10266
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10264 FStar_Pprint.rbracket
    | uu____10275 when is_lex_list e ->
        let uu____10276 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10277 =
          let uu____10278 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10279 = extract_from_list e  in
          separate_map_or_flow_last uu____10278
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10279
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10276
          uu____10277 FStar_Pprint.rbracket
    | uu____10288 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10292 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10293 =
          let uu____10294 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10294 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10292
          uu____10293 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10304 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10307 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10304 uu____10307
    | FStar_Parser_AST.Op (op,args) when
        let uu____10316 = handleable_op op args  in
        Prims.op_Negation uu____10316 ->
        let uu____10318 =
          let uu____10320 =
            let uu____10322 = FStar_Ident.text_of_id op  in
            let uu____10324 =
              let uu____10326 =
                let uu____10328 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10328
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10326  in
            Prims.op_Hat uu____10322 uu____10324  in
          Prims.op_Hat "Operation " uu____10320  in
        failwith uu____10318
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10335 = p_term false false e  in
        soft_parens_with_nesting uu____10335
    | FStar_Parser_AST.Const uu____10338 ->
        let uu____10339 = p_term false false e  in
        soft_parens_with_nesting uu____10339
    | FStar_Parser_AST.Op uu____10342 ->
        let uu____10349 = p_term false false e  in
        soft_parens_with_nesting uu____10349
    | FStar_Parser_AST.Tvar uu____10352 ->
        let uu____10353 = p_term false false e  in
        soft_parens_with_nesting uu____10353
    | FStar_Parser_AST.Var uu____10356 ->
        let uu____10357 = p_term false false e  in
        soft_parens_with_nesting uu____10357
    | FStar_Parser_AST.Name uu____10360 ->
        let uu____10361 = p_term false false e  in
        soft_parens_with_nesting uu____10361
    | FStar_Parser_AST.Construct uu____10364 ->
        let uu____10375 = p_term false false e  in
        soft_parens_with_nesting uu____10375
    | FStar_Parser_AST.Abs uu____10378 ->
        let uu____10385 = p_term false false e  in
        soft_parens_with_nesting uu____10385
    | FStar_Parser_AST.App uu____10388 ->
        let uu____10395 = p_term false false e  in
        soft_parens_with_nesting uu____10395
    | FStar_Parser_AST.Let uu____10398 ->
        let uu____10419 = p_term false false e  in
        soft_parens_with_nesting uu____10419
    | FStar_Parser_AST.LetOpen uu____10422 ->
        let uu____10427 = p_term false false e  in
        soft_parens_with_nesting uu____10427
    | FStar_Parser_AST.Seq uu____10430 ->
        let uu____10435 = p_term false false e  in
        soft_parens_with_nesting uu____10435
    | FStar_Parser_AST.Bind uu____10438 ->
        let uu____10445 = p_term false false e  in
        soft_parens_with_nesting uu____10445
    | FStar_Parser_AST.If uu____10448 ->
        let uu____10455 = p_term false false e  in
        soft_parens_with_nesting uu____10455
    | FStar_Parser_AST.Match uu____10458 ->
        let uu____10473 = p_term false false e  in
        soft_parens_with_nesting uu____10473
    | FStar_Parser_AST.TryWith uu____10476 ->
        let uu____10491 = p_term false false e  in
        soft_parens_with_nesting uu____10491
    | FStar_Parser_AST.Ascribed uu____10494 ->
        let uu____10503 = p_term false false e  in
        soft_parens_with_nesting uu____10503
    | FStar_Parser_AST.Record uu____10506 ->
        let uu____10519 = p_term false false e  in
        soft_parens_with_nesting uu____10519
    | FStar_Parser_AST.Project uu____10522 ->
        let uu____10527 = p_term false false e  in
        soft_parens_with_nesting uu____10527
    | FStar_Parser_AST.Product uu____10530 ->
        let uu____10537 = p_term false false e  in
        soft_parens_with_nesting uu____10537
    | FStar_Parser_AST.Sum uu____10540 ->
        let uu____10551 = p_term false false e  in
        soft_parens_with_nesting uu____10551
    | FStar_Parser_AST.QForall uu____10554 ->
        let uu____10573 = p_term false false e  in
        soft_parens_with_nesting uu____10573
    | FStar_Parser_AST.QExists uu____10576 ->
        let uu____10595 = p_term false false e  in
        soft_parens_with_nesting uu____10595
    | FStar_Parser_AST.Refine uu____10598 ->
        let uu____10603 = p_term false false e  in
        soft_parens_with_nesting uu____10603
    | FStar_Parser_AST.NamedTyp uu____10606 ->
        let uu____10611 = p_term false false e  in
        soft_parens_with_nesting uu____10611
    | FStar_Parser_AST.Requires uu____10614 ->
        let uu____10622 = p_term false false e  in
        soft_parens_with_nesting uu____10622
    | FStar_Parser_AST.Ensures uu____10625 ->
        let uu____10633 = p_term false false e  in
        soft_parens_with_nesting uu____10633
    | FStar_Parser_AST.Attributes uu____10636 ->
        let uu____10639 = p_term false false e  in
        soft_parens_with_nesting uu____10639
    | FStar_Parser_AST.Quote uu____10642 ->
        let uu____10647 = p_term false false e  in
        soft_parens_with_nesting uu____10647
    | FStar_Parser_AST.VQuote uu____10650 ->
        let uu____10651 = p_term false false e  in
        soft_parens_with_nesting uu____10651
    | FStar_Parser_AST.Antiquote uu____10654 ->
        let uu____10655 = p_term false false e  in
        soft_parens_with_nesting uu____10655
    | FStar_Parser_AST.CalcProof uu____10658 ->
        let uu____10667 = p_term false false e  in
        soft_parens_with_nesting uu____10667

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10670  ->
    match uu___15_10670 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10682) ->
        let uu____10685 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10685
    | FStar_Const.Const_bytearray (bytes,uu____10687) ->
        let uu____10692 =
          let uu____10693 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10693  in
        let uu____10694 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10692 uu____10694
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10717 =
          match uu___13_10717 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10724 =
          match uu___14_10724 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10739  ->
               match uu____10739 with
               | (s,w) ->
                   let uu____10746 = signedness s  in
                   let uu____10747 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10746 uu____10747)
            sign_width_opt
           in
        let uu____10748 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10748 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10752 = FStar_Range.string_of_range r  in str uu____10752
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10756 = p_quident lid  in
        let uu____10757 =
          let uu____10758 =
            let uu____10759 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10759  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10758  in
        FStar_Pprint.op_Hat_Hat uu____10756 uu____10757

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10762 = str "u#"  in
    let uu____10764 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10762 uu____10764

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10766;_},u1::u2::[])
        ->
        let uu____10772 =
          let uu____10773 = p_universeFrom u1  in
          let uu____10774 =
            let uu____10775 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10775  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10773 uu____10774  in
        FStar_Pprint.group uu____10772
    | FStar_Parser_AST.App uu____10776 ->
        let uu____10783 = head_and_args u  in
        (match uu____10783 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10809 =
                    let uu____10810 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10811 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10819  ->
                           match uu____10819 with
                           | (u1,uu____10825) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10810 uu____10811  in
                  FStar_Pprint.group uu____10809
              | uu____10826 ->
                  let uu____10827 =
                    let uu____10829 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10829
                     in
                  failwith uu____10827))
    | uu____10832 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10858 = FStar_Ident.text_of_id id1  in str uu____10858
    | FStar_Parser_AST.Paren u1 ->
        let uu____10861 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10861
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10862;_},uu____10863::uu____10864::[])
        ->
        let uu____10868 = p_universeFrom u  in
        soft_parens_with_nesting uu____10868
    | FStar_Parser_AST.App uu____10869 ->
        let uu____10876 = p_universeFrom u  in
        soft_parens_with_nesting uu____10876
    | uu____10877 ->
        let uu____10878 =
          let uu____10880 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10880
           in
        failwith uu____10878

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
       | FStar_Parser_AST.Module (uu____10969,decls) ->
           let uu____10975 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____10975
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____10984,decls,uu____10986) ->
           let uu____10993 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____10993
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11053  ->
         match uu____11053 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11075)) -> false
      | ([],uu____11079) -> false
      | uu____11083 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs))
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
        | FStar_Parser_AST.Module (uu____11132,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11138,decls,uu____11140) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11192 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11205;
                 FStar_Parser_AST.quals = uu____11206;
                 FStar_Parser_AST.attrs = uu____11207;_}::uu____11208 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11212 =
                   let uu____11215 =
                     let uu____11218 = FStar_List.tl ds  in d :: uu____11218
                      in
                   d0 :: uu____11215  in
                 (uu____11212, (d0.FStar_Parser_AST.drange))
             | uu____11223 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11192 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11280 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11280 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11389 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11389, comments1))))))
  