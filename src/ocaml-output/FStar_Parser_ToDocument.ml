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
  
let rec p_list :
  'Auu____3937 .
    ('Auu____3937 -> FStar_Pprint.document) ->
      FStar_Pprint.document ->
        'Auu____3937 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_3969 =
          match uu___4_3969 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3977 = f x  in
              let uu____3978 =
                let uu____3979 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3979  in
              FStar_Pprint.op_Hat_Hat uu____3977 uu____3978
           in
        let uu____3980 = str "["  in
        let uu____3982 =
          let uu____3983 = p_list' l  in
          let uu____3984 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3983 uu____3984  in
        FStar_Pprint.op_Hat_Hat uu____3980 uu____3982
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4913)) ->
          let uu____4916 =
            let uu____4918 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____4918 FStar_Util.is_upper  in
          if uu____4916
          then
            let uu____4924 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4924 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4927 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4934 = p_attributes d.FStar_Parser_AST.attrs  in
    let uu____4935 =
      let uu____4936 = p_rawDecl d  in
      FStar_Pprint.op_Hat_Hat qualifiers uu____4936  in
    FStar_Pprint.op_Hat_Hat uu____4934 uu____4935

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

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4952 =
          let uu____4953 = str "val"  in
          let uu____4955 =
            let uu____4956 =
              let uu____4957 = p_lident lid  in
              let uu____4958 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4957 uu____4958  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4956  in
          FStar_Pprint.op_Hat_Hat uu____4953 uu____4955  in
        let uu____4959 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4952 uu____4959
    | FStar_Parser_AST.TopLevelLet (uu____4962,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4987 =
               let uu____4988 = str "let"  in p_letlhs uu____4988 lb false
                in
             FStar_Pprint.group uu____4987) lbs
    | uu____4991 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4994 =
          let uu____4995 = str "open"  in
          let uu____4997 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4995 uu____4997  in
        FStar_Pprint.group uu____4994
    | FStar_Parser_AST.Include uid ->
        let uu____4999 =
          let uu____5000 = str "include"  in
          let uu____5002 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5000 uu____5002  in
        FStar_Pprint.group uu____4999
    | FStar_Parser_AST.Friend uid ->
        let uu____5004 =
          let uu____5005 = str "friend"  in
          let uu____5007 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5005 uu____5007  in
        FStar_Pprint.group uu____5004
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5010 =
          let uu____5011 = str "module"  in
          let uu____5013 =
            let uu____5014 =
              let uu____5015 = p_uident uid1  in
              let uu____5016 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5015 uu____5016  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5014  in
          FStar_Pprint.op_Hat_Hat uu____5011 uu____5013  in
        let uu____5017 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5010 uu____5017
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5019 =
          let uu____5020 = str "module"  in
          let uu____5022 =
            let uu____5023 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5023  in
          FStar_Pprint.op_Hat_Hat uu____5020 uu____5022  in
        FStar_Pprint.group uu____5019
    | FStar_Parser_AST.Tycon
        (true ,uu____5024,(FStar_Parser_AST.TyconAbbrev
         (uid,tpars,FStar_Pervasives_Native.None ,t))::[])
        ->
        let effect_prefix_doc =
          let uu____5041 = str "effect"  in
          let uu____5043 =
            let uu____5044 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5044  in
          FStar_Pprint.op_Hat_Hat uu____5041 uu____5043  in
        let uu____5045 =
          let uu____5046 = p_typars tpars  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5046 FStar_Pprint.equals
           in
        let uu____5049 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5045 uu____5049
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5068 =
          let uu____5069 = FStar_List.hd tcdefs  in
          p_typeDeclWithKw s uu____5069  in
        let uu____5070 =
          let uu____5071 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5079 =
                    let uu____5080 = str "and"  in
                    p_typeDeclWithKw uu____5080 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5079)) uu____5071
           in
        FStar_Pprint.op_Hat_Hat uu____5068 uu____5070
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5097 = str "let"  in
          let uu____5099 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5097 uu____5099  in
        let uu____5100 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5100 p_letbinding lbs
          (fun uu____5110  ->
             match uu____5110 with
             | (p,t) ->
                 let uu____5117 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 { r = uu____5117; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5122 =
          let uu____5123 = str "val"  in
          let uu____5125 =
            let uu____5126 =
              let uu____5127 = p_lident lid  in
              let uu____5128 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5127 uu____5128  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5126  in
          FStar_Pprint.op_Hat_Hat uu____5123 uu____5125  in
        FStar_All.pipe_left FStar_Pprint.group uu____5122
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5133 =
            let uu____5135 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5135 FStar_Util.is_upper  in
          if uu____5133
          then FStar_Pprint.empty
          else
            (let uu____5143 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5143 FStar_Pprint.space)
           in
        let uu____5145 =
          let uu____5146 = p_ident id1  in
          let uu____5147 =
            let uu____5148 =
              let uu____5149 =
                let uu____5150 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5150  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5149  in
            FStar_Pprint.group uu____5148  in
          FStar_Pprint.op_Hat_Hat uu____5146 uu____5147  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5145
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5159 = str "exception"  in
        let uu____5161 =
          let uu____5162 =
            let uu____5163 = p_uident uid  in
            let uu____5164 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5168 =
                     let uu____5169 = str "of"  in
                     let uu____5171 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5169 uu____5171  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5168) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5163 uu____5164  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5162  in
        FStar_Pprint.op_Hat_Hat uu____5159 uu____5161
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5175 = str "new_effect"  in
        let uu____5177 =
          let uu____5178 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5178  in
        FStar_Pprint.op_Hat_Hat uu____5175 uu____5177
    | FStar_Parser_AST.SubEffect se ->
        let uu____5180 = str "sub_effect"  in
        let uu____5182 =
          let uu____5183 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5183  in
        FStar_Pprint.op_Hat_Hat uu____5180 uu____5182
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Main uu____5185 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5187,uu____5188) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5204 = str "%splice"  in
        let uu____5206 =
          let uu____5207 =
            let uu____5208 = str ";"  in p_list p_uident uu____5208 ids  in
          let uu____5210 =
            let uu____5211 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5211  in
          FStar_Pprint.op_Hat_Hat uu____5207 uu____5210  in
        FStar_Pprint.op_Hat_Hat uu____5204 uu____5206
    | FStar_Parser_AST.Fail (errs,lax1,se) ->
        let p_int i =
          let uu____5233 = FStar_Util.string_of_int i  in str uu____5233  in
        let uu____5235 = str (if lax1 then "%FailLax" else "%Fail")  in
        let uu____5242 =
          let uu____5243 =
            let uu____5244 = str ";"  in p_list p_int uu____5244 errs  in
          let uu____5247 =
            let uu____5248 = p_rawDecl se  in
            FStar_Pprint.op_Hat_Hat break1 uu____5248  in
          FStar_Pprint.op_Hat_Hat uu____5243 uu____5247  in
        FStar_Pprint.op_Hat_Hat uu____5235 uu____5242

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5249  ->
    match uu___5_5249 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5252 = str "#set-options"  in
        let uu____5254 =
          let uu____5255 =
            let uu____5256 = str s  in FStar_Pprint.dquotes uu____5256  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5255  in
        FStar_Pprint.op_Hat_Hat uu____5252 uu____5254
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5261 = str "#reset-options"  in
        let uu____5263 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5269 =
                 let uu____5270 = str s  in FStar_Pprint.dquotes uu____5270
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5269) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5261 uu____5263
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5275 = str "#push-options"  in
        let uu____5277 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5283 =
                 let uu____5284 = str s  in FStar_Pprint.dquotes uu____5284
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5283) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5275 uu____5277
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
      let uu____5317 = p_typeDecl kw typedecl  in
      match uu____5317 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5340 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5340
          else
            (let uu____5343 =
               let uu____5344 =
                 let uu____5345 =
                   let uu____5346 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5346 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5345  in
               let uu____5347 =
                 let uu____5348 =
                   let uu____5349 =
                     let uu____5350 =
                       let uu____5351 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5351  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5350
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5349  in
                 FStar_Pprint.op_Hat_Hat decl uu____5348  in
               FStar_Pprint.ifflat uu____5344 uu____5347  in
             FStar_All.pipe_left FStar_Pprint.group uu____5343)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5354  ->
      match uu___6_5354 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5377 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5377, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5394 = p_typ_sep false false t  in
          (match uu____5394 with
           | (comm,doc) ->
               let uu____5414 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5414, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5458 =
            match uu____5458 with
            | (lid1,t) ->
                let uu____5466 =
                  let uu____5471 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5471
                   in
                (match uu____5466 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5483 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5483  in
          let uu____5488 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5488, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5543 =
            match uu____5543 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5563 =
                    let uu____5564 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5564  in
                  FStar_Range.extend_to_end_of_line uu____5563  in
                let uu____5569 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5569 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5598 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5598, datacon_doc, jump2)

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
                let uu____5626 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5626  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq1 then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5633 =
                    let uu____5634 =
                      let uu____5635 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5635 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5634  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5633
               in
            if bs = []
            then with_kw (fun n1  -> prefix2 n1 typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n1  ->
                    let uu____5655 =
                      let uu____5656 = FStar_Pprint.flow break1 binders  in
                      prefix2 n1 uu____5656  in
                    prefix2 uu____5655 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5658  ->
      match uu____5658 with
      | (lid,t) ->
          let uu____5666 =
            let uu____5667 = p_lident lid  in
            let uu____5668 =
              let uu____5669 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5669  in
            FStar_Pprint.op_Hat_Hat uu____5667 uu____5668  in
          FStar_Pprint.group uu____5666

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5671  ->
    match uu____5671 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5696 =
            let uu____5697 =
              let uu____5698 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5698  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5697  in
          FStar_Pprint.group uu____5696  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5702 =
               let uu____5703 =
                 let uu____5704 =
                   let uu____5705 =
                     let uu____5706 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5706
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5705  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5704  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5703  in
             FStar_Pprint.group uu____5702) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5710  ->
      fun inner_let  ->
        match uu____5710 with
        | (pat,uu____5718) ->
            let uu____5719 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5771 =
                    let uu____5778 =
                      let uu____5783 =
                        let uu____5784 =
                          let uu____5785 =
                            let uu____5786 = str "by"  in
                            let uu____5788 =
                              let uu____5789 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5789
                               in
                            FStar_Pprint.op_Hat_Hat uu____5786 uu____5788  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5785
                           in
                        FStar_Pprint.group uu____5784  in
                      (t, uu____5783)  in
                    FStar_Pervasives_Native.Some uu____5778  in
                  (pat1, uu____5771)
              | uu____5800 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5719 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5826);
                         FStar_Parser_AST.prange = uu____5827;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5844 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5844 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5850 =
                        if inner_let
                        then
                          let uu____5864 = pats_as_binders_if_possible pats
                             in
                          match uu____5864 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5887 = pats_as_binders_if_possible pats
                              in
                           match uu____5887 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5850 with
                       | (terms,style) ->
                           let uu____5914 =
                             let uu____5915 =
                               let uu____5916 =
                                 let uu____5917 = p_lident lid  in
                                 let uu____5918 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5917
                                   uu____5918
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5916
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5915  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5914)
                  | uu____5921 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5929 =
                              let uu____5930 =
                                let uu____5931 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5931
                                 in
                              FStar_Pprint.group uu____5930  in
                            FStar_Pprint.op_Hat_Hat uu____5929 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5942 =
                        let uu____5943 =
                          let uu____5944 =
                            let uu____5945 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5945  in
                          FStar_Pprint.group uu____5944  in
                        FStar_Pprint.op_Hat_Hat uu____5943 ascr_doc  in
                      FStar_Pprint.group uu____5942))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5947  ->
      match uu____5947 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5956 = p_term_sep false false e  in
          (match uu____5956 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5966 =
                 let uu____5967 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5967  in
               let uu____5968 =
                 let uu____5969 =
                   let uu____5970 =
                     let uu____5971 =
                       let uu____5972 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5972
                        in
                     FStar_Pprint.group uu____5971  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5970  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5969  in
               FStar_Pprint.ifflat uu____5966 uu____5968)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5973  ->
    match uu___7_5973 with
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
        let uu____5998 = p_uident uid  in
        let uu____5999 = p_binders true bs  in
        let uu____6001 =
          let uu____6002 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6002  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5998
          uu____5999 uu____6001

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
          let uu____6017 =
            let uu____6018 =
              let uu____6019 =
                let uu____6020 = p_uident uid  in
                let uu____6021 = p_binders true bs  in
                let uu____6023 =
                  let uu____6024 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6024  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6020 uu____6021 uu____6023
                 in
              FStar_Pprint.group uu____6019  in
            let uu____6029 =
              let uu____6030 = str "with"  in
              let uu____6032 =
                let uu____6033 =
                  let uu____6034 =
                    let uu____6035 =
                      let uu____6036 =
                        let uu____6037 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6037
                         in
                      separate_map_last uu____6036 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6035  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6034  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6033  in
              FStar_Pprint.op_Hat_Hat uu____6030 uu____6032  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6018 uu____6029  in
          braces_with_nesting uu____6017

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____6041,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6054 =
            let uu____6055 = p_lident lid  in
            let uu____6056 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6055 uu____6056  in
          let uu____6057 = p_simpleTerm ps false e  in
          prefix2 uu____6054 uu____6057
      | uu____6059 ->
          let uu____6060 =
            let uu____6062 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6062
             in
          failwith uu____6060

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6145 =
        match uu____6145 with
        | (kwd,t) ->
            let uu____6156 =
              let uu____6157 = str kwd  in
              let uu____6158 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6157 uu____6158  in
            let uu____6159 = p_simpleTerm ps false t  in
            prefix2 uu____6156 uu____6159
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6166 =
      let uu____6167 =
        let uu____6168 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6169 =
          let uu____6170 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6170  in
        FStar_Pprint.op_Hat_Hat uu____6168 uu____6169  in
      let uu____6172 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6167 uu____6172  in
    let uu____6173 =
      let uu____6174 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6174  in
    FStar_Pprint.op_Hat_Hat uu____6166 uu____6173

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6175  ->
    match uu___8_6175 with
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
        let uu____6195 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6195 FStar_Pprint.hardline
    | uu____6196 ->
        let uu____6197 =
          let uu____6198 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6198  in
        FStar_Pprint.op_Hat_Hat uu____6197 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6201  ->
    match uu___9_6201 with
    | FStar_Parser_AST.Rec  ->
        let uu____6202 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6202
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6204  ->
    match uu___10_6204 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6209,e) -> e
          | uu____6215 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6216 = str "#["  in
        let uu____6218 =
          let uu____6219 = p_term false false t1  in
          let uu____6222 =
            let uu____6223 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6223 break1  in
          FStar_Pprint.op_Hat_Hat uu____6219 uu____6222  in
        FStar_Pprint.op_Hat_Hat uu____6216 uu____6218

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6229 =
          let uu____6230 =
            let uu____6231 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6231  in
          FStar_Pprint.separate_map uu____6230 p_tuplePattern pats  in
        FStar_Pprint.group uu____6229
    | uu____6232 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6241 =
          let uu____6242 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6242 p_constructorPattern pats  in
        FStar_Pprint.group uu____6241
    | uu____6243 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6246;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6251 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6252 = p_constructorPattern hd1  in
        let uu____6253 = p_constructorPattern tl1  in
        infix0 uu____6251 uu____6252 uu____6253
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6255;_},pats)
        ->
        let uu____6261 = p_quident uid  in
        let uu____6262 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6261 uu____6262
    | uu____6263 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6279;
               FStar_Parser_AST.blevel = uu____6280;
               FStar_Parser_AST.aqual = uu____6281;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6290 =
               let uu____6291 = p_ident lid  in
               p_refinement aqual uu____6291 t1 phi  in
             soft_parens_with_nesting uu____6290
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6294;
               FStar_Parser_AST.blevel = uu____6295;
               FStar_Parser_AST.aqual = uu____6296;_},phi))
             ->
             let uu____6302 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6302
         | uu____6303 ->
             let uu____6308 =
               let uu____6309 = p_tuplePattern pat  in
               let uu____6310 =
                 let uu____6311 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6311
                  in
               FStar_Pprint.op_Hat_Hat uu____6309 uu____6310  in
             soft_parens_with_nesting uu____6308)
    | FStar_Parser_AST.PatList pats ->
        let uu____6315 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6315 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6334 =
          match uu____6334 with
          | (lid,pat) ->
              let uu____6341 = p_qlident lid  in
              let uu____6342 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6341 uu____6342
           in
        let uu____6343 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6343
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6355 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6356 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6357 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6355
          uu____6356 uu____6357
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6368 =
          let uu____6369 =
            let uu____6370 =
              let uu____6371 = FStar_Ident.text_of_id op  in str uu____6371
               in
            let uu____6373 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6370 uu____6373  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6369  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6368
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6377 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6377 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6385 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6386 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6385 uu____6386
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6388 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6392;
           FStar_Parser_AST.prange = uu____6393;_},uu____6394)
        ->
        let uu____6399 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6399
    | FStar_Parser_AST.PatTuple (uu____6400,false ) ->
        let uu____6407 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6407
    | uu____6408 ->
        let uu____6409 =
          let uu____6411 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6411  in
        failwith uu____6409

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6416;_},uu____6417)
        -> true
    | uu____6424 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6430) -> true
    | uu____6432 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6439 = p_binder' is_atomic b  in
      match uu____6439 with
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
          let uu____6476 =
            let uu____6477 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6478 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6477 uu____6478  in
          (uu____6476, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6484 = p_lident lid  in
          (uu____6484, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6491 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6502;
                   FStar_Parser_AST.blevel = uu____6503;
                   FStar_Parser_AST.aqual = uu____6504;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6509 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6509 t1 phi
            | uu____6510 ->
                let t' =
                  let uu____6512 = is_typ_tuple t  in
                  if uu____6512
                  then
                    let uu____6515 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6515
                  else p_tmFormula t  in
                let uu____6518 =
                  let uu____6519 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6520 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6519 uu____6520  in
                (uu____6518, t')
             in
          (match uu____6491 with
           | (b',t') ->
               let catf =
                 let uu____6538 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6538
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6545 =
                         let uu____6546 =
                           let uu____6547 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6547
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6546
                          in
                       FStar_Pprint.group uu____6545
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6552 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6552)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____6557 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6585;
                  FStar_Parser_AST.blevel = uu____6586;
                  FStar_Parser_AST.aqual = uu____6587;_},phi)
               ->
               let uu____6591 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6591 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6612 ->
               if is_atomic
               then
                 let uu____6624 = p_atomicTerm t  in
                 (uu____6624, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6631 = p_appTerm t  in
                  (uu____6631, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6642 = p_refinement' aqual_opt binder t phi  in
          match uu____6642 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____6658 -> false
            | FStar_Parser_AST.App uu____6670 -> false
            | FStar_Parser_AST.Op uu____6678 -> false
            | uu____6686 -> true  in
          let uu____6688 = p_noSeqTerm false false phi  in
          match uu____6688 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6705 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6705)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____6714 =
                let uu____6715 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6715 binder  in
              let uu____6716 =
                let uu____6717 = p_appTerm t  in
                let uu____6718 =
                  let uu____6719 =
                    let uu____6720 =
                      let uu____6721 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6722 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6721 uu____6722  in
                    FStar_Pprint.group uu____6720  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6719
                   in
                FStar_Pprint.op_Hat_Hat uu____6717 uu____6718  in
              (uu____6714, uu____6716)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6736 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6736

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6740 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6743 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6743)
       in
    if uu____6740
    then FStar_Pprint.underscore
    else (let uu____6748 = FStar_Ident.text_of_id lid  in str uu____6748)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6751 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6754 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6754)
       in
    if uu____6751
    then FStar_Pprint.underscore
    else (let uu____6759 = FStar_Ident.text_of_lid lid  in str uu____6759)

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
          let uu____6780 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6780
        else
          (let uu____6783 =
             let uu____6784 =
               let uu____6785 =
                 let uu____6786 =
                   let uu____6787 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6787  in
                 FStar_Pprint.op_Hat_Hat doc uu____6786  in
               FStar_Pprint.group uu____6785  in
             let uu____6788 =
               let uu____6789 =
                 let uu____6790 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6790  in
               FStar_Pprint.op_Hat_Hat comm uu____6789  in
             FStar_Pprint.ifflat uu____6784 uu____6788  in
           FStar_All.pipe_left FStar_Pprint.group uu____6783)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6798 = p_noSeqTerm true false e1  in
            (match uu____6798 with
             | (comm,t1) ->
                 let uu____6807 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6808 =
                   let uu____6809 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6809
                    in
                 FStar_Pprint.op_Hat_Hat uu____6807 uu____6808)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6813 =
              let uu____6814 =
                let uu____6815 =
                  let uu____6816 = p_lident x  in
                  let uu____6817 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6816 uu____6817  in
                let uu____6818 =
                  let uu____6819 = p_noSeqTermAndComment true false e1  in
                  let uu____6822 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6819 uu____6822  in
                op_Hat_Slash_Plus_Hat uu____6815 uu____6818  in
              FStar_Pprint.group uu____6814  in
            let uu____6823 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6813 uu____6823
        | uu____6824 ->
            let uu____6825 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6825

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
            let uu____6837 = p_noSeqTerm true false e1  in
            (match uu____6837 with
             | (comm,t1) ->
                 let uu____6850 =
                   let uu____6851 =
                     let uu____6852 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6852  in
                   let uu____6853 =
                     let uu____6854 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6854
                      in
                   FStar_Pprint.op_Hat_Hat uu____6851 uu____6853  in
                 (comm, uu____6850))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6858 =
              let uu____6859 =
                let uu____6860 =
                  let uu____6861 =
                    let uu____6862 = p_lident x  in
                    let uu____6863 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6862 uu____6863  in
                  let uu____6864 =
                    let uu____6865 = p_noSeqTermAndComment true false e1  in
                    let uu____6868 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6865 uu____6868  in
                  op_Hat_Slash_Plus_Hat uu____6861 uu____6864  in
                FStar_Pprint.group uu____6860  in
              let uu____6869 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6859 uu____6869  in
            (FStar_Pprint.empty, uu____6858)
        | uu____6870 -> p_noSeqTerm ps pb e

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
            let uu____6890 =
              let uu____6891 = p_tmIff e1  in
              let uu____6892 =
                let uu____6893 =
                  let uu____6894 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6894
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6893  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6891 uu____6892  in
            FStar_Pprint.group uu____6890
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6900 =
              let uu____6901 = p_tmIff e1  in
              let uu____6902 =
                let uu____6903 =
                  let uu____6904 =
                    let uu____6905 = p_typ false false t  in
                    let uu____6908 =
                      let uu____6909 = str "by"  in
                      let uu____6911 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6909 uu____6911  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6905 uu____6908  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6904
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6903  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6901 uu____6902  in
            FStar_Pprint.group uu____6900
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____6912;_},e1::e2::e3::[])
            ->
            let uu____6919 =
              let uu____6920 =
                let uu____6921 =
                  let uu____6922 = p_atomicTermNotQUident e1  in
                  let uu____6923 =
                    let uu____6924 =
                      let uu____6925 =
                        let uu____6926 = p_term false false e2  in
                        soft_parens_with_nesting uu____6926  in
                      let uu____6929 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6925 uu____6929  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6924  in
                  FStar_Pprint.op_Hat_Hat uu____6922 uu____6923  in
                FStar_Pprint.group uu____6921  in
              let uu____6930 =
                let uu____6931 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6931  in
              FStar_Pprint.op_Hat_Hat uu____6920 uu____6930  in
            FStar_Pprint.group uu____6919
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____6932;_},e1::e2::e3::[])
            ->
            let uu____6939 =
              let uu____6940 =
                let uu____6941 =
                  let uu____6942 = p_atomicTermNotQUident e1  in
                  let uu____6943 =
                    let uu____6944 =
                      let uu____6945 =
                        let uu____6946 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6946  in
                      let uu____6949 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6945 uu____6949  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6944  in
                  FStar_Pprint.op_Hat_Hat uu____6942 uu____6943  in
                FStar_Pprint.group uu____6941  in
              let uu____6950 =
                let uu____6951 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6951  in
              FStar_Pprint.op_Hat_Hat uu____6940 uu____6950  in
            FStar_Pprint.group uu____6939
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6961 =
              let uu____6962 = str "requires"  in
              let uu____6964 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6962 uu____6964  in
            FStar_Pprint.group uu____6961
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6974 =
              let uu____6975 = str "ensures"  in
              let uu____6977 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6975 uu____6977  in
            FStar_Pprint.group uu____6974
        | FStar_Parser_AST.Attributes es ->
            let uu____6981 =
              let uu____6982 = str "attributes"  in
              let uu____6984 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6982 uu____6984  in
            FStar_Pprint.group uu____6981
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____6989 =
                let uu____6990 =
                  let uu____6991 = str "if"  in
                  let uu____6993 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____6991 uu____6993  in
                let uu____6996 =
                  let uu____6997 = str "then"  in
                  let uu____6999 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____6997 uu____6999  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6990 uu____6996  in
              FStar_Pprint.group uu____6989
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7003,uu____7004,e31) when
                     is_unit e31 ->
                     let uu____7006 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7006
                 | uu____7009 -> p_noSeqTermAndComment false false e2  in
               let uu____7012 =
                 let uu____7013 =
                   let uu____7014 = str "if"  in
                   let uu____7016 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7014 uu____7016  in
                 let uu____7019 =
                   let uu____7020 =
                     let uu____7021 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7021 e2_doc  in
                   let uu____7023 =
                     let uu____7024 = str "else"  in
                     let uu____7026 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7024 uu____7026  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7020 uu____7023  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7013 uu____7019  in
               FStar_Pprint.group uu____7012)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7049 =
              let uu____7050 =
                let uu____7051 =
                  let uu____7052 = str "try"  in
                  let uu____7054 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7052 uu____7054  in
                let uu____7057 =
                  let uu____7058 = str "with"  in
                  let uu____7060 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7058 uu____7060  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7051 uu____7057  in
              FStar_Pprint.group uu____7050  in
            let uu____7069 = paren_if (ps || pb)  in uu____7069 uu____7049
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7096 =
              let uu____7097 =
                let uu____7098 =
                  let uu____7099 = str "match"  in
                  let uu____7101 = p_noSeqTermAndComment false false e1  in
                  let uu____7104 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7099 uu____7101 uu____7104
                   in
                let uu____7108 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7098 uu____7108  in
              FStar_Pprint.group uu____7097  in
            let uu____7117 = paren_if (ps || pb)  in uu____7117 uu____7096
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7124 =
              let uu____7125 =
                let uu____7126 =
                  let uu____7127 = str "let open"  in
                  let uu____7129 = p_quident uid  in
                  let uu____7130 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7127 uu____7129 uu____7130
                   in
                let uu____7134 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7126 uu____7134  in
              FStar_Pprint.group uu____7125  in
            let uu____7136 = paren_if ps  in uu____7136 uu____7124
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7201 is_last =
              match uu____7201 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7235 =
                          let uu____7236 = str "let"  in
                          let uu____7238 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7236 uu____7238
                           in
                        FStar_Pprint.group uu____7235
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7241 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7247 = p_term_sep false false e2  in
                  (match uu____7247 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7257 =
                         if is_last
                         then
                           let uu____7259 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7260 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7259 doc_expr1 uu____7260
                         else
                           (let uu____7266 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7266)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7257)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7317 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7317
                     else
                       (let uu____7322 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7322)) lbs
               in
            let lbs_doc =
              let uu____7326 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7326  in
            let uu____7327 =
              let uu____7328 =
                let uu____7329 =
                  let uu____7330 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7330
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7329  in
              FStar_Pprint.group uu____7328  in
            let uu____7332 = paren_if ps  in uu____7332 uu____7327
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7339;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7342;
                                                             FStar_Parser_AST.level
                                                               = uu____7343;_})
            when matches_var maybe_x x ->
            let uu____7370 =
              let uu____7371 =
                let uu____7372 = str "function"  in
                let uu____7374 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7372 uu____7374  in
              FStar_Pprint.group uu____7371  in
            let uu____7383 = paren_if (ps || pb)  in uu____7383 uu____7370
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7389 =
              let uu____7390 = str "quote"  in
              let uu____7392 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7390 uu____7392  in
            FStar_Pprint.group uu____7389
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7394 =
              let uu____7395 = str "`"  in
              let uu____7397 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7395 uu____7397  in
            FStar_Pprint.group uu____7394
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7399 =
              let uu____7400 = str "`%"  in
              let uu____7402 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7400 uu____7402  in
            FStar_Pprint.group uu____7399
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7404;
              FStar_Parser_AST.level = uu____7405;_}
            ->
            let uu____7406 =
              let uu____7407 = str "`@"  in
              let uu____7409 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7407 uu____7409  in
            FStar_Pprint.group uu____7406
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7411 =
              let uu____7412 = str "`#"  in
              let uu____7414 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7412 uu____7414  in
            FStar_Pprint.group uu____7411
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7423 = str "calc"  in
              let uu____7425 =
                let uu____7426 =
                  let uu____7427 = p_noSeqTermAndComment false false rel  in
                  let uu____7430 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7427 uu____7430  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7426  in
              FStar_Pprint.op_Hat_Hat uu____7423 uu____7425  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7432 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7433 =
              let uu____7434 =
                let uu____7435 =
                  let uu____7436 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7439 =
                    let uu____7440 = str ";"  in
                    let uu____7442 =
                      let uu____7443 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7443
                       in
                    FStar_Pprint.op_Hat_Hat uu____7440 uu____7442  in
                  FStar_Pprint.op_Hat_Hat uu____7436 uu____7439  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7435  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7434
               in
            FStar_Pprint.enclose head1 uu____7432 uu____7433
        | uu____7445 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7446  ->
    fun uu____7447  ->
      match uu____7447 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7452 =
            let uu____7453 = p_noSeqTermAndComment false false rel  in
            let uu____7456 =
              let uu____7457 =
                let uu____7458 =
                  let uu____7459 =
                    let uu____7460 = p_noSeqTermAndComment false false just
                       in
                    let uu____7463 =
                      let uu____7464 =
                        let uu____7465 =
                          let uu____7466 =
                            let uu____7467 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7470 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7467 uu____7470  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7466
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7465
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7464
                       in
                    FStar_Pprint.op_Hat_Hat uu____7460 uu____7463  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7459  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7458  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7457  in
            FStar_Pprint.op_Hat_Hat uu____7453 uu____7456  in
          FStar_Pprint.group uu____7452

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7472  ->
    match uu___11_7472 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7484 =
          let uu____7485 = str "[@"  in
          let uu____7487 =
            let uu____7488 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7489 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7488 uu____7489  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7485 uu____7487  in
        FStar_Pprint.group uu____7484

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
        | FStar_Parser_AST.QForall (bs,(uu____7507,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7541 =
                   let uu____7542 =
                     let uu____7543 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7543 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7542 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7541 term_doc
             | pats ->
                 let uu____7551 =
                   let uu____7552 =
                     let uu____7553 =
                       let uu____7554 =
                         let uu____7555 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7555
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7554 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7558 = p_trigger trigger  in
                     prefix2 uu____7553 uu____7558  in
                   FStar_Pprint.group uu____7552  in
                 prefix2 uu____7551 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7560,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7594 =
                   let uu____7595 =
                     let uu____7596 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7596 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7595 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7594 term_doc
             | pats ->
                 let uu____7604 =
                   let uu____7605 =
                     let uu____7606 =
                       let uu____7607 =
                         let uu____7608 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7608
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7607 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7611 = p_trigger trigger  in
                     prefix2 uu____7606 uu____7611  in
                   FStar_Pprint.group uu____7605  in
                 prefix2 uu____7604 term_doc)
        | uu____7612 -> p_simpleTerm ps pb e

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
      let uu____7633 = all_binders_annot t  in
      if uu____7633
      then
        let uu____7636 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7636
      else
        (let uu____7647 =
           let uu____7648 =
             let uu____7649 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7649  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7648  in
         FStar_Pprint.group uu____7647)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7708 = x  in
      match uu____7708 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____7773 = hd1  in
               (match uu____7773 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____7845 = cb  in
      match uu____7845 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____7864 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7870 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7870) hd1 tl1
                  in
               cat_with_colon uu____7864 typ)
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
                 FStar_Parser_AST.brange = uu____7949;
                 FStar_Parser_AST.blevel = uu____7950;
                 FStar_Parser_AST.aqual = uu____7951;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____7960 =
                 let uu____7965 = p_ident lid  in
                 p_refinement' aqual uu____7965 t1 phi  in
               FStar_Pervasives_Native.Some uu____7960
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7972) ->
               let uu____7977 =
                 let uu____7982 =
                   let uu____7983 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____7984 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____7983 uu____7984  in
                 let uu____7985 = p_tmEqNoRefinement t  in
                 (uu____7982, uu____7985)  in
               FStar_Pervasives_Native.Some uu____7977
           | uu____7990 -> FStar_Pervasives_Native.None)
      | uu____7999 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8012 -> false
      | uu____8024 -> true  in
    let uu____8026 = map_if_all all_binders pats  in
    match uu____8026 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8058 = collapse_pats bs  in
        (uu____8058, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8075 = FStar_List.map p_atomicPattern pats  in
        (uu____8075, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8087 -> str "forall"
    | FStar_Parser_AST.QExists uu____8107 -> str "exists"
    | uu____8127 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8129  ->
    match uu___12_8129 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8141 =
          let uu____8142 =
            let uu____8143 =
              let uu____8144 = str "pattern"  in
              let uu____8146 =
                let uu____8147 =
                  let uu____8148 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8148
                   in
                FStar_Pprint.op_Hat_Hat uu____8147 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8144 uu____8146  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8143  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8142  in
        FStar_Pprint.group uu____8141

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8156 = str "\\/"  in
    FStar_Pprint.separate_map uu____8156 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8163 =
      let uu____8164 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8164 p_appTerm pats  in
    FStar_Pprint.group uu____8163

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8176 = p_term_sep false pb e1  in
            (match uu____8176 with
             | (comm,doc) ->
                 let prefix1 =
                   let uu____8185 = str "fun"  in
                   let uu____8187 =
                     let uu____8188 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8188
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8185 uu____8187  in
                 let uu____8189 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8191 =
                       let uu____8192 =
                         let uu____8193 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8193  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8192
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8191
                   else
                     (let uu____8196 = op_Hat_Slash_Plus_Hat prefix1 doc  in
                      FStar_Pprint.group uu____8196)
                    in
                 let uu____8197 = paren_if ps  in uu____8197 uu____8189)
        | uu____8202 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8210  ->
      match uu____8210 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8234 =
                    let uu____8235 =
                      let uu____8236 =
                        let uu____8237 = p_tuplePattern p  in
                        let uu____8238 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8237 uu____8238  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8236
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8235  in
                  FStar_Pprint.group uu____8234
              | FStar_Pervasives_Native.Some f ->
                  let uu____8240 =
                    let uu____8241 =
                      let uu____8242 =
                        let uu____8243 =
                          let uu____8244 =
                            let uu____8245 = p_tuplePattern p  in
                            let uu____8246 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8245
                              uu____8246
                             in
                          FStar_Pprint.group uu____8244  in
                        let uu____8248 =
                          let uu____8249 =
                            let uu____8252 = p_tmFormula f  in
                            [uu____8252; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8249  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8243 uu____8248
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8242
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8241  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8240
               in
            let uu____8254 = p_term_sep false pb e  in
            match uu____8254 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8264 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8264
                   else
                     (let uu____8267 =
                        let uu____8268 =
                          let uu____8269 =
                            let uu____8270 =
                              let uu____8271 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8271  in
                            op_Hat_Slash_Plus_Hat branch uu____8270  in
                          FStar_Pprint.group uu____8269  in
                        let uu____8272 =
                          let uu____8273 =
                            let uu____8274 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8274  in
                          FStar_Pprint.op_Hat_Hat branch uu____8273  in
                        FStar_Pprint.ifflat uu____8268 uu____8272  in
                      FStar_Pprint.group uu____8267))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8278 =
                       let uu____8279 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8279  in
                     op_Hat_Slash_Plus_Hat branch uu____8278)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8290 =
                      let uu____8291 =
                        let uu____8292 =
                          let uu____8293 =
                            let uu____8294 =
                              let uu____8295 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8295  in
                            FStar_Pprint.separate_map uu____8294
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8293
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8292
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8291  in
                    FStar_Pprint.group uu____8290
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8297 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8299;_},e1::e2::[])
        ->
        let uu____8305 = str "<==>"  in
        let uu____8307 = p_tmImplies e1  in
        let uu____8308 = p_tmIff e2  in
        infix0 uu____8305 uu____8307 uu____8308
    | uu____8309 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8311;_},e1::e2::[])
        ->
        let uu____8317 = str "==>"  in
        let uu____8319 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8325 = p_tmImplies e2  in
        infix0 uu____8317 uu____8319 uu____8325
    | uu____8326 ->
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
          let uu____8340 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8340 with
          | (terms',last1) ->
              let uu____8360 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8395 =
                      let uu____8396 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8396
                       in
                    let uu____8397 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8395, uu____8397)
                | Binders (n1,ln,parens1) ->
                    let uu____8411 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8419 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8411, break1, uu____8419)
                 in
              (match uu____8360 with
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
                    | _8452 when _8452 = Prims.int_one -> FStar_List.hd terms
                    | uu____8453 ->
                        let uu____8454 =
                          let uu____8455 =
                            let uu____8456 =
                              let uu____8457 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8458 =
                                let uu____8459 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8459
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8457 uu____8458
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8456  in
                          let uu____8460 =
                            let uu____8461 =
                              let uu____8462 =
                                let uu____8463 =
                                  let uu____8464 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8464  in
                                let uu____8465 =
                                  let uu____8466 =
                                    let uu____8467 =
                                      let uu____8468 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8469 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8475 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8475)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8468
                                        uu____8469
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8467
                                     in
                                  jump2 uu____8466  in
                                FStar_Pprint.ifflat uu____8463 uu____8465  in
                              FStar_Pprint.group uu____8462  in
                            let uu____8477 =
                              let uu____8478 =
                                let uu____8479 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8479  in
                              FStar_Pprint.align uu____8478  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8461
                              uu____8477
                             in
                          FStar_Pprint.ifflat uu____8455 uu____8460  in
                        FStar_Pprint.group uu____8454))

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
            | Arrows uu____8493 -> p_tmArrow' p_Tm e
            | Binders uu____8500 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8523 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8529 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8523 uu____8529
      | uu____8532 -> let uu____8533 = p_Tm e  in [uu____8533]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8586 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8612 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8586 uu____8612
        | uu____8635 ->
            let uu____8636 =
              let uu____8647 = p_Tm1 e1  in
              (uu____8647, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8636]
         in
      let fold_fun bs x =
        let uu____8745 = x  in
        match uu____8745 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____8877 = hd1  in
                 (match uu____8877 with
                  | (b2s,t2,uu____8906) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9008 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9065 = cb  in
        match uu____9065 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9094 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9105 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9111 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9111) hd1 tl1
                         in
                      f uu____9105 typ))
         in
      let binders =
        let uu____9127 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9127  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9190 =
        let uu____9191 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9191 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9190  in
    let disj =
      let uu____9194 =
        let uu____9195 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9195 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9194  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9215;_},e1::e2::[])
        ->
        let uu____9221 = p_tmDisjunction e1  in
        let uu____9226 = let uu____9231 = p_tmConjunction e2  in [uu____9231]
           in
        FStar_List.append uu____9221 uu____9226
    | uu____9240 -> let uu____9241 = p_tmConjunction e  in [uu____9241]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9251;_},e1::e2::[])
        ->
        let uu____9257 = p_tmConjunction e1  in
        let uu____9260 = let uu____9263 = p_tmTuple e2  in [uu____9263]  in
        FStar_List.append uu____9257 uu____9260
    | uu____9264 -> let uu____9265 = p_tmTuple e  in [uu____9265]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9282 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9282
          (fun uu____9290  ->
             match uu____9290 with | (e1,uu____9296) -> p_tmEq e1) args
    | uu____9297 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9306 =
             let uu____9307 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9307  in
           FStar_Pprint.group uu____9306)

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
               (let uu____9326 = FStar_Ident.text_of_id op  in
                uu____9326 = "="))
              ||
              (let uu____9331 = FStar_Ident.text_of_id op  in
               uu____9331 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9337 = levels op1  in
            (match uu____9337 with
             | (left1,mine,right1) ->
                 let uu____9356 =
                   let uu____9357 = FStar_All.pipe_left str op1  in
                   let uu____9359 = p_tmEqWith' p_X left1 e1  in
                   let uu____9360 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9357 uu____9359 uu____9360  in
                 paren_if_gt curr mine uu____9356)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9361;_},e1::e2::[])
            ->
            let uu____9367 =
              let uu____9368 = p_tmEqWith p_X e1  in
              let uu____9369 =
                let uu____9370 =
                  let uu____9371 =
                    let uu____9372 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9372  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9371  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9370  in
              FStar_Pprint.op_Hat_Hat uu____9368 uu____9369  in
            FStar_Pprint.group uu____9367
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9373;_},e1::[])
            ->
            let uu____9378 = levels "-"  in
            (match uu____9378 with
             | (left1,mine,right1) ->
                 let uu____9398 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9398)
        | uu____9399 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9447)::(e2,uu____9449)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9469 = is_list e  in Prims.op_Negation uu____9469)
              ->
              let op = "::"  in
              let uu____9474 = levels op  in
              (match uu____9474 with
               | (left1,mine,right1) ->
                   let uu____9493 =
                     let uu____9494 = str op  in
                     let uu____9495 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9497 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9494 uu____9495 uu____9497  in
                   paren_if_gt curr mine uu____9493)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9516 = levels op  in
              (match uu____9516 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9550 = p_binder false b  in
                         let uu____9552 =
                           let uu____9553 =
                             let uu____9554 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9554 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9553
                            in
                         FStar_Pprint.op_Hat_Hat uu____9550 uu____9552
                     | FStar_Util.Inr t ->
                         let uu____9556 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____9558 =
                           let uu____9559 =
                             let uu____9560 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9560 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9559
                            in
                         FStar_Pprint.op_Hat_Hat uu____9556 uu____9558
                      in
                   let uu____9561 =
                     let uu____9562 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9567 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____9562 uu____9567  in
                   paren_if_gt curr mine uu____9561)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____9569;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____9599 = levels op  in
              (match uu____9599 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____9619 = str op  in
                     let uu____9620 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____9622 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____9619 uu____9620 uu____9622
                   else
                     (let uu____9626 =
                        let uu____9627 = str op  in
                        let uu____9628 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____9630 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____9627 uu____9628 uu____9630  in
                      paren_if_gt curr mine uu____9626))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9639 = levels op1  in
              (match uu____9639 with
               | (left1,mine,right1) ->
                   let uu____9658 =
                     let uu____9659 = str op1  in
                     let uu____9660 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9662 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9659 uu____9660 uu____9662  in
                   paren_if_gt curr mine uu____9658)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9682 =
                let uu____9683 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9684 =
                  let uu____9685 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9685 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9683 uu____9684  in
              braces_with_nesting uu____9682
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____9690;_},e1::[])
              ->
              let uu____9695 =
                let uu____9696 = str "~"  in
                let uu____9698 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9696 uu____9698  in
              FStar_Pprint.group uu____9695
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____9700;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____9709 = levels op  in
                   (match uu____9709 with
                    | (left1,mine,right1) ->
                        let uu____9728 =
                          let uu____9729 = str op  in
                          let uu____9730 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____9732 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____9729 uu____9730 uu____9732  in
                        paren_if_gt curr mine uu____9728)
               | uu____9734 -> p_X e)
          | uu____9735 -> p_X e

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
        let uu____9742 =
          let uu____9743 = p_lident lid  in
          let uu____9744 =
            let uu____9745 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9745  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9743 uu____9744  in
        FStar_Pprint.group uu____9742
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9748 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9750 = p_appTerm e  in
    let uu____9751 =
      let uu____9752 =
        let uu____9753 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9753 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9752  in
    FStar_Pprint.op_Hat_Hat uu____9750 uu____9751

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9759 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9759 t phi
      | FStar_Parser_AST.TAnnotated uu____9760 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9766 ->
          let uu____9767 =
            let uu____9769 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9769
             in
          failwith uu____9767
      | FStar_Parser_AST.TVariable uu____9772 ->
          let uu____9773 =
            let uu____9775 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9775
             in
          failwith uu____9773
      | FStar_Parser_AST.NoName uu____9778 ->
          let uu____9779 =
            let uu____9781 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9781
             in
          failwith uu____9779

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9785  ->
      match uu____9785 with
      | (lid,e) ->
          let uu____9793 =
            let uu____9794 = p_qlident lid  in
            let uu____9795 =
              let uu____9796 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9796
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9794 uu____9795  in
          FStar_Pprint.group uu____9793

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9799 when is_general_application e ->
        let uu____9806 = head_and_args e  in
        (match uu____9806 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9853 = p_argTerm e1  in
                  let uu____9854 =
                    let uu____9855 =
                      let uu____9856 =
                        let uu____9857 = str "`"  in
                        let uu____9859 =
                          let uu____9860 = p_indexingTerm head1  in
                          let uu____9861 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9860 uu____9861  in
                        FStar_Pprint.op_Hat_Hat uu____9857 uu____9859  in
                      FStar_Pprint.group uu____9856  in
                    let uu____9863 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9855 uu____9863  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9853 uu____9854
              | uu____9864 ->
                  let uu____9871 =
                    let uu____9882 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9882
                    then
                      let uu____9916 =
                        FStar_Util.take
                          (fun uu____9940  ->
                             match uu____9940 with
                             | (uu____9946,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9916 with
                      | (fs_typ_args,args1) ->
                          let uu____9984 =
                            let uu____9985 = p_indexingTerm head1  in
                            let uu____9986 =
                              let uu____9987 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____9987
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____9985 uu____9986  in
                          (uu____9984, args1)
                    else
                      (let uu____10002 = p_indexingTerm head1  in
                       (uu____10002, args))
                     in
                  (match uu____9871 with
                   | (head_doc,args1) ->
                       let uu____10023 =
                         let uu____10024 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10024 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10023)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10046 =
             (is_dtuple_constructor lid) && (all1_explicit args)  in
           Prims.op_Negation uu____10046)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10065 =
               let uu____10066 = p_quident lid  in
               let uu____10067 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10066 uu____10067  in
             FStar_Pprint.group uu____10065
         | hd1::tl1 ->
             let uu____10084 =
               let uu____10085 =
                 let uu____10086 =
                   let uu____10087 = p_quident lid  in
                   let uu____10088 = p_argTerm hd1  in
                   prefix2 uu____10087 uu____10088  in
                 FStar_Pprint.group uu____10086  in
               let uu____10089 =
                 let uu____10090 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10090  in
               FStar_Pprint.op_Hat_Hat uu____10085 uu____10089  in
             FStar_Pprint.group uu____10084)
    | uu____10095 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10106 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10106 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10110 = str "#"  in
        let uu____10112 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10110 uu____10112
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10115 = str "#["  in
        let uu____10117 =
          let uu____10118 = p_indexingTerm t  in
          let uu____10119 =
            let uu____10120 = str "]"  in
            let uu____10122 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10120 uu____10122  in
          FStar_Pprint.op_Hat_Hat uu____10118 uu____10119  in
        FStar_Pprint.op_Hat_Hat uu____10115 uu____10117
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10125  ->
    match uu____10125 with | (e,uu____10131) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10136;_},e1::e2::[])
          ->
          let uu____10142 =
            let uu____10143 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10144 =
              let uu____10145 =
                let uu____10146 = p_term false false e2  in
                soft_parens_with_nesting uu____10146  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10145  in
            FStar_Pprint.op_Hat_Hat uu____10143 uu____10144  in
          FStar_Pprint.group uu____10142
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10149;_},e1::e2::[])
          ->
          let uu____10155 =
            let uu____10156 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10157 =
              let uu____10158 =
                let uu____10159 = p_term false false e2  in
                soft_brackets_with_nesting uu____10159  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10158  in
            FStar_Pprint.op_Hat_Hat uu____10156 uu____10157  in
          FStar_Pprint.group uu____10155
      | uu____10162 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10167 = p_quident lid  in
        let uu____10168 =
          let uu____10169 =
            let uu____10170 = p_term false false e1  in
            soft_parens_with_nesting uu____10170  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10169  in
        FStar_Pprint.op_Hat_Hat uu____10167 uu____10168
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10178 =
          let uu____10179 = FStar_Ident.text_of_id op  in str uu____10179  in
        let uu____10181 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10178 uu____10181
    | uu____10182 -> p_atomicTermNotQUident e

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
         | uu____10195 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10204 =
          let uu____10205 = FStar_Ident.text_of_id op  in str uu____10205  in
        let uu____10207 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10204 uu____10207
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10211 =
          let uu____10212 =
            let uu____10213 =
              let uu____10214 = FStar_Ident.text_of_id op  in str uu____10214
               in
            let uu____10216 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10213 uu____10216  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10212  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10211
    | FStar_Parser_AST.Construct (lid,args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10231 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____10232 =
          let uu____10233 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____10233
            (fun uu____10241  ->
               match uu____10241 with | (e1,uu____10247) -> p_tmEq e1) args
           in
        let uu____10248 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10231
          uu____10232 uu____10248
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10253 =
          let uu____10254 = p_atomicTermNotQUident e1  in
          let uu____10255 =
            let uu____10256 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10256  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10254
            uu____10255
           in
        FStar_Pprint.group uu____10253
    | uu____10259 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10264 = p_quident constr_lid  in
        let uu____10265 =
          let uu____10266 =
            let uu____10267 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10267  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10266  in
        FStar_Pprint.op_Hat_Hat uu____10264 uu____10265
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10269 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10269 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10271 = p_term_sep false false e1  in
        (match uu____10271 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10284 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10284))
    | uu____10285 when is_array e ->
        let es = extract_from_list e  in
        let uu____10289 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10290 =
          let uu____10291 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10291
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10296 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10289
          uu____10290 uu____10296
    | uu____10299 when is_list e ->
        let uu____10300 =
          let uu____10301 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10302 = extract_from_list e  in
          separate_map_or_flow_last uu____10301
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10302
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10300 FStar_Pprint.rbracket
    | uu____10311 when is_lex_list e ->
        let uu____10312 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10313 =
          let uu____10314 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10315 = extract_from_list e  in
          separate_map_or_flow_last uu____10314
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10315
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10312
          uu____10313 FStar_Pprint.rbracket
    | uu____10324 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10328 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10329 =
          let uu____10330 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10330 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10328
          uu____10329 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10340 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10343 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10340 uu____10343
    | FStar_Parser_AST.Op (op,args) when
        let uu____10352 = handleable_op op args  in
        Prims.op_Negation uu____10352 ->
        let uu____10354 =
          let uu____10356 =
            let uu____10358 = FStar_Ident.text_of_id op  in
            let uu____10360 =
              let uu____10362 =
                let uu____10364 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10364
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10362  in
            Prims.op_Hat uu____10358 uu____10360  in
          Prims.op_Hat "Operation " uu____10356  in
        failwith uu____10354
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10371 = p_term false false e  in
        soft_parens_with_nesting uu____10371
    | FStar_Parser_AST.Const uu____10374 ->
        let uu____10375 = p_term false false e  in
        soft_parens_with_nesting uu____10375
    | FStar_Parser_AST.Op uu____10378 ->
        let uu____10385 = p_term false false e  in
        soft_parens_with_nesting uu____10385
    | FStar_Parser_AST.Tvar uu____10388 ->
        let uu____10389 = p_term false false e  in
        soft_parens_with_nesting uu____10389
    | FStar_Parser_AST.Var uu____10392 ->
        let uu____10393 = p_term false false e  in
        soft_parens_with_nesting uu____10393
    | FStar_Parser_AST.Name uu____10396 ->
        let uu____10397 = p_term false false e  in
        soft_parens_with_nesting uu____10397
    | FStar_Parser_AST.Construct uu____10400 ->
        let uu____10411 = p_term false false e  in
        soft_parens_with_nesting uu____10411
    | FStar_Parser_AST.Abs uu____10414 ->
        let uu____10421 = p_term false false e  in
        soft_parens_with_nesting uu____10421
    | FStar_Parser_AST.App uu____10424 ->
        let uu____10431 = p_term false false e  in
        soft_parens_with_nesting uu____10431
    | FStar_Parser_AST.Let uu____10434 ->
        let uu____10455 = p_term false false e  in
        soft_parens_with_nesting uu____10455
    | FStar_Parser_AST.LetOpen uu____10458 ->
        let uu____10463 = p_term false false e  in
        soft_parens_with_nesting uu____10463
    | FStar_Parser_AST.Seq uu____10466 ->
        let uu____10471 = p_term false false e  in
        soft_parens_with_nesting uu____10471
    | FStar_Parser_AST.Bind uu____10474 ->
        let uu____10481 = p_term false false e  in
        soft_parens_with_nesting uu____10481
    | FStar_Parser_AST.If uu____10484 ->
        let uu____10491 = p_term false false e  in
        soft_parens_with_nesting uu____10491
    | FStar_Parser_AST.Match uu____10494 ->
        let uu____10509 = p_term false false e  in
        soft_parens_with_nesting uu____10509
    | FStar_Parser_AST.TryWith uu____10512 ->
        let uu____10527 = p_term false false e  in
        soft_parens_with_nesting uu____10527
    | FStar_Parser_AST.Ascribed uu____10530 ->
        let uu____10539 = p_term false false e  in
        soft_parens_with_nesting uu____10539
    | FStar_Parser_AST.Record uu____10542 ->
        let uu____10555 = p_term false false e  in
        soft_parens_with_nesting uu____10555
    | FStar_Parser_AST.Project uu____10558 ->
        let uu____10563 = p_term false false e  in
        soft_parens_with_nesting uu____10563
    | FStar_Parser_AST.Product uu____10566 ->
        let uu____10573 = p_term false false e  in
        soft_parens_with_nesting uu____10573
    | FStar_Parser_AST.Sum uu____10576 ->
        let uu____10587 = p_term false false e  in
        soft_parens_with_nesting uu____10587
    | FStar_Parser_AST.QForall uu____10590 ->
        let uu____10609 = p_term false false e  in
        soft_parens_with_nesting uu____10609
    | FStar_Parser_AST.QExists uu____10612 ->
        let uu____10631 = p_term false false e  in
        soft_parens_with_nesting uu____10631
    | FStar_Parser_AST.Refine uu____10634 ->
        let uu____10639 = p_term false false e  in
        soft_parens_with_nesting uu____10639
    | FStar_Parser_AST.NamedTyp uu____10642 ->
        let uu____10647 = p_term false false e  in
        soft_parens_with_nesting uu____10647
    | FStar_Parser_AST.Requires uu____10650 ->
        let uu____10658 = p_term false false e  in
        soft_parens_with_nesting uu____10658
    | FStar_Parser_AST.Ensures uu____10661 ->
        let uu____10669 = p_term false false e  in
        soft_parens_with_nesting uu____10669
    | FStar_Parser_AST.Attributes uu____10672 ->
        let uu____10675 = p_term false false e  in
        soft_parens_with_nesting uu____10675
    | FStar_Parser_AST.Quote uu____10678 ->
        let uu____10683 = p_term false false e  in
        soft_parens_with_nesting uu____10683
    | FStar_Parser_AST.VQuote uu____10686 ->
        let uu____10687 = p_term false false e  in
        soft_parens_with_nesting uu____10687
    | FStar_Parser_AST.Antiquote uu____10690 ->
        let uu____10691 = p_term false false e  in
        soft_parens_with_nesting uu____10691
    | FStar_Parser_AST.CalcProof uu____10694 ->
        let uu____10703 = p_term false false e  in
        soft_parens_with_nesting uu____10703

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10706  ->
    match uu___15_10706 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10718) ->
        let uu____10721 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10721
    | FStar_Const.Const_bytearray (bytes,uu____10723) ->
        let uu____10728 =
          let uu____10729 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10729  in
        let uu____10730 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10728 uu____10730
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10753 =
          match uu___13_10753 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10760 =
          match uu___14_10760 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10775  ->
               match uu____10775 with
               | (s,w) ->
                   let uu____10782 = signedness s  in
                   let uu____10783 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10782 uu____10783)
            sign_width_opt
           in
        let uu____10784 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10784 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10788 = FStar_Range.string_of_range r  in str uu____10788
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10792 = p_quident lid  in
        let uu____10793 =
          let uu____10794 =
            let uu____10795 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10795  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10794  in
        FStar_Pprint.op_Hat_Hat uu____10792 uu____10793

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10798 = str "u#"  in
    let uu____10800 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10798 uu____10800

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10802;_},u1::u2::[])
        ->
        let uu____10808 =
          let uu____10809 = p_universeFrom u1  in
          let uu____10810 =
            let uu____10811 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10811  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10809 uu____10810  in
        FStar_Pprint.group uu____10808
    | FStar_Parser_AST.App uu____10812 ->
        let uu____10819 = head_and_args u  in
        (match uu____10819 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10845 =
                    let uu____10846 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10847 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10855  ->
                           match uu____10855 with
                           | (u1,uu____10861) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10846 uu____10847  in
                  FStar_Pprint.group uu____10845
              | uu____10862 ->
                  let uu____10863 =
                    let uu____10865 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10865
                     in
                  failwith uu____10863))
    | uu____10868 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10894 = FStar_Ident.text_of_id id1  in str uu____10894
    | FStar_Parser_AST.Paren u1 ->
        let uu____10897 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10897
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10898;_},uu____10899::uu____10900::[])
        ->
        let uu____10904 = p_universeFrom u  in
        soft_parens_with_nesting uu____10904
    | FStar_Parser_AST.App uu____10905 ->
        let uu____10912 = p_universeFrom u  in
        soft_parens_with_nesting uu____10912
    | uu____10913 ->
        let uu____10914 =
          let uu____10916 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10916
           in
        failwith uu____10914

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
       | FStar_Parser_AST.Module (uu____11005,decls) ->
           let uu____11011 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11011
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11020,decls,uu____11022) ->
           let uu____11029 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11029
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11089  ->
         match uu____11089 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11111)) -> false
      | ([],uu____11115) -> false
      | uu____11119 -> true  in
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
        | FStar_Parser_AST.Module (uu____11168,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11174,decls,uu____11176) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11228 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11241;
                 FStar_Parser_AST.quals = uu____11242;
                 FStar_Parser_AST.attrs = uu____11243;_}::uu____11244 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11248 =
                   let uu____11251 =
                     let uu____11254 = FStar_List.tl ds  in d :: uu____11254
                      in
                   d0 :: uu____11251  in
                 (uu____11248, (d0.FStar_Parser_AST.drange))
             | uu____11259 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11228 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11316 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11316 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11425 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11425, comments1))))))
  