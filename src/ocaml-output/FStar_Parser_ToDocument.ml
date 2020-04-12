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
  'uuuuuu311 'uuuuuu312 .
    Prims.bool -> ('uuuuuu311 -> 'uuuuuu312) -> 'uuuuuu311 -> 'uuuuuu312
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
  'uuuuuu422 'uuuuuu423 .
    'uuuuuu422 ->
      ('uuuuuu423 -> 'uuuuuu422) ->
        'uuuuuu423 FStar_Pervasives_Native.option -> 'uuuuuu422
  =
  fun n  ->
    fun f  ->
      fun x  ->
        match x with
        | FStar_Pervasives_Native.None  -> n
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
  'uuuuuu536 .
    FStar_Pprint.document ->
      ('uuuuuu536 -> FStar_Pprint.document) ->
        'uuuuuu536 Prims.list -> FStar_Pprint.document
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
  'uuuuuu575 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu575 -> FStar_Pprint.document) ->
          'uuuuuu575 Prims.list -> FStar_Pprint.document
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
  'uuuuuu626 .
    ('uuuuuu626 -> FStar_Pprint.document) ->
      'uuuuuu626 Prims.list -> FStar_Pprint.document
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
  'uuuuuu728 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu728 -> FStar_Pprint.document) ->
        'uuuuuu728 Prims.list -> FStar_Pprint.document
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
  'uuuuuu780 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu780 -> FStar_Pprint.document) ->
        'uuuuuu780 Prims.list -> FStar_Pprint.document
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
  'uuuuuu824 .
    FStar_Pprint.document ->
      ('uuuuuu824 -> FStar_Pprint.document) ->
        'uuuuuu824 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'uuuuuu862 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu862 -> FStar_Pprint.document) ->
        'uuuuuu862 Prims.list -> FStar_Pprint.document
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
  'uuuuuu914 .
    FStar_Pprint.document ->
      (Prims.bool -> 'uuuuuu914 -> FStar_Pprint.document) ->
        'uuuuuu914 Prims.list -> FStar_Pprint.document
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
  fun n  ->
    fun b  ->
      fun doc1  ->
        fun doc2  ->
          fun doc3  ->
            if doc2 = FStar_Pprint.empty
            then
              let uu____996 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____996
            else FStar_Pprint.surround n b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'uuuuuu1018 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu1018 -> FStar_Pprint.document) ->
                  'uuuuuu1018 Prims.list -> FStar_Pprint.document
  =
  fun n  ->
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
                     FStar_Pprint.soft_surround n b opening uu____1077
                       closing)
  
let soft_surround_map_or_flow :
  'uuuuuu1097 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('uuuuuu1097 -> FStar_Pprint.document) ->
                  'uuuuuu1097 Prims.list -> FStar_Pprint.document
  =
  fun n  ->
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
                     FStar_Pprint.soft_surround n b opening uu____1156
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
  fun cons_lid  ->
    fun nil_lid  ->
      let rec aux e =
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid
        | FStar_Parser_AST.Construct (lid,uu____1236::(e2,uu____1238)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
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
      | FStar_Parser_AST.App (head,arg,imp) -> aux head ((arg, imp) :: acc)
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
  'uuuuuu1649 .
    Prims.string ->
      ('uuuuuu1649 * (FStar_Char.char,Prims.string) FStar_Util.either
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
         | (assoc,tokens) -> ((levels_from_associativity i assoc), tokens))
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
  'uuuuuu2125 . ('uuuuuu2125 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n level =
      let uu____2174 =
        FStar_List.tryFind
          (fun uu____2210  ->
             match uu____2210 with
             | (uu____2227,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2174 with
      | FStar_Pervasives_Native.Some ((uu____2256,l1,uu____2258),uu____2259)
          -> max n l1
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
    | (left,mine,right) ->
        if op = "*"
        then ((left - Prims.int_one), mine, right)
        else (left, mine, right)
  
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
  'uuuuuu2641 . FStar_Ident.ident -> 'uuuuuu2641 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | uu____2657 when uu____2657 = Prims.int_zero -> true
      | uu____2659 when uu____2659 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2661 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2661 ["-"; "~"])
      | uu____2669 when uu____2669 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2671 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2671
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | uu____2693 when uu____2693 = (Prims.of_int (3)) ->
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
  'uuuuuu3029 .
    ('uuuuuu3029 -> FStar_Pprint.document) ->
      'uuuuuu3029 -> FStar_Range.range -> FStar_Pprint.document
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
  'uuuuuu3232 'uuuuuu3233 .
    ('uuuuuu3232 -> 'uuuuuu3233) ->
      'uuuuuu3232 ->
        FStar_Range.range -> (FStar_Pprint.document * 'uuuuuu3233)
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
              fun init  ->
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
                        meta_decl doc1 true init))
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
                       let lnum5 = if init then (Prims.of_int (2)) else lnum4
                          in
                       let uu____3628 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc uu____3628)
  
let separate_map_with_comments :
  'uuuuuu3642 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu3642 -> FStar_Pprint.document) ->
          'uuuuuu3642 Prims.list ->
            ('uuuuuu3642 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix  ->
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
                let init =
                  let meta_decl = extract_meta x  in
                  let uu____3757 =
                    let uu____3759 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3759  in
                  let uu____3760 =
                    let uu____3761 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix uu____3761  in
                  (uu____3757, uu____3760)  in
                let uu____3763 = FStar_List.fold_left fold_fun init xs1  in
                FStar_Pervasives_Native.snd uu____3763
  
let separate_map_with_comments_kw :
  'uuuuuu3790 'uuuuuu3791 .
    'uuuuuu3790 ->
      'uuuuuu3790 ->
        ('uuuuuu3790 -> 'uuuuuu3791 -> FStar_Pprint.document) ->
          'uuuuuu3791 Prims.list ->
            ('uuuuuu3791 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix  ->
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
                let init =
                  let meta_decl = extract_meta x  in
                  let uu____3910 =
                    let uu____3912 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3912  in
                  let uu____3913 = f prefix x  in (uu____3910, uu____3913)
                   in
                let uu____3915 = FStar_List.fold_left fold_fun init xs1  in
                FStar_Pervasives_Native.snd uu____3915
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id,uu____4871)) ->
          let uu____4874 =
            let uu____4876 =
              FStar_Util.char_at id.FStar_Ident.idText Prims.int_zero  in
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
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____5122 =
            let uu____5124 =
              FStar_Util.char_at id.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5124 FStar_Util.is_upper  in
          if uu____5122
          then FStar_Pprint.empty
          else
            (let uu____5132 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5132 FStar_Pprint.space)
           in
        let uu____5134 =
          let uu____5135 = p_ident id  in
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
    | FStar_Parser_AST.LayeredEffect ne ->
        let uu____5174 = str "layered_effect"  in
        let uu____5176 =
          let uu____5177 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5177  in
        FStar_Pprint.op_Hat_Hat uu____5174 uu____5176
    | FStar_Parser_AST.Polymonadic_bind (l1,l2,l3,t) ->
        let uu____5182 = str "polymonadic_bind"  in
        let uu____5184 =
          let uu____5185 =
            let uu____5186 = p_quident l1  in
            let uu____5187 =
              let uu____5188 =
                let uu____5189 =
                  let uu____5190 = p_quident l2  in
                  let uu____5191 =
                    let uu____5192 =
                      let uu____5193 = str "|>"  in
                      let uu____5195 =
                        let uu____5196 = p_quident l3  in
                        let uu____5197 =
                          let uu____5198 = p_simpleTerm false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                            uu____5198
                           in
                        FStar_Pprint.op_Hat_Hat uu____5196 uu____5197  in
                      FStar_Pprint.op_Hat_Hat uu____5193 uu____5195  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu____5192
                     in
                  FStar_Pprint.op_Hat_Hat uu____5190 uu____5191  in
                FStar_Pprint.op_Hat_Hat break1 uu____5189  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu____5188  in
            FStar_Pprint.op_Hat_Hat uu____5186 uu____5187  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5185  in
        FStar_Pprint.op_Hat_Hat uu____5182 uu____5184
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Main uu____5202 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5204,uu____5205) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5221 = str "%splice"  in
        let uu____5223 =
          let uu____5224 =
            let uu____5225 = str ";"  in p_list p_uident uu____5225 ids  in
          let uu____5227 =
            let uu____5228 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5228  in
          FStar_Pprint.op_Hat_Hat uu____5224 uu____5227  in
        FStar_Pprint.op_Hat_Hat uu____5221 uu____5223

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5231  ->
    match uu___5_5231 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5234 = str "#set-options"  in
        let uu____5236 =
          let uu____5237 =
            let uu____5238 = str s  in FStar_Pprint.dquotes uu____5238  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5237  in
        FStar_Pprint.op_Hat_Hat uu____5234 uu____5236
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5243 = str "#reset-options"  in
        let uu____5245 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5251 =
                 let uu____5252 = str s  in FStar_Pprint.dquotes uu____5252
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5251) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5243 uu____5245
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5257 = str "#push-options"  in
        let uu____5259 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5265 =
                 let uu____5266 = str s  in FStar_Pprint.dquotes uu____5266
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5265) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5257 uu____5259
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
      let uu____5299 = p_typeDecl kw typedecl  in
      match uu____5299 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5322 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5322
          else
            (let uu____5325 =
               let uu____5326 =
                 let uu____5327 =
                   let uu____5328 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5328 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5327  in
               let uu____5329 =
                 let uu____5330 =
                   let uu____5331 =
                     let uu____5332 =
                       let uu____5333 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5333  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5332
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5331  in
                 FStar_Pprint.op_Hat_Hat decl uu____5330  in
               FStar_Pprint.ifflat uu____5326 uu____5329  in
             FStar_All.pipe_left FStar_Pprint.group uu____5325)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5336  ->
      match uu___6_5336 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5359 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5359, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5376 = p_typ_sep false false t  in
          (match uu____5376 with
           | (comm,doc) ->
               let uu____5396 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5396, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5440 =
            match uu____5440 with
            | (lid1,t) ->
                let uu____5448 =
                  let uu____5453 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5453
                   in
                (match uu____5448 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5465 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5465  in
          let uu____5470 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5470, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5525 =
            match uu____5525 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5545 =
                    let uu____5546 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5546  in
                  FStar_Range.extend_to_end_of_line uu____5545  in
                let uu____5551 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5551 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5580 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5580, datacon_doc, jump2)

and (p_typeDeclPrefix :
  FStar_Pprint.document ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun kw  ->
    fun eq  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            let with_kw cont =
              let lid_doc = p_ident lid  in
              let kw_lid =
                let uu____5608 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5608  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5615 =
                    let uu____5616 =
                      let uu____5617 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5617 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5616  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5615
               in
            if bs = []
            then with_kw (fun n  -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n  ->
                    let uu____5637 =
                      let uu____5638 = FStar_Pprint.flow break1 binders  in
                      prefix2 n uu____5638  in
                    prefix2 uu____5637 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5640  ->
      match uu____5640 with
      | (lid,t) ->
          let uu____5648 =
            let uu____5649 = p_lident lid  in
            let uu____5650 =
              let uu____5651 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5651  in
            FStar_Pprint.op_Hat_Hat uu____5649 uu____5650  in
          FStar_Pprint.group uu____5648

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5653  ->
    match uu____5653 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5678 =
            let uu____5679 =
              let uu____5680 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5680  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5679  in
          FStar_Pprint.group uu____5678  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5684 =
               let uu____5685 =
                 let uu____5686 =
                   let uu____5687 =
                     let uu____5688 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5688
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5687  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5686  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5685  in
             FStar_Pprint.group uu____5684) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5692  ->
      fun inner_let  ->
        match uu____5692 with
        | (pat,uu____5700) ->
            let uu____5701 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5753 =
                    let uu____5760 =
                      let uu____5765 =
                        let uu____5766 =
                          let uu____5767 =
                            let uu____5768 = str "by"  in
                            let uu____5770 =
                              let uu____5771 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5771
                               in
                            FStar_Pprint.op_Hat_Hat uu____5768 uu____5770  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5767
                           in
                        FStar_Pprint.group uu____5766  in
                      (t, uu____5765)  in
                    FStar_Pervasives_Native.Some uu____5760  in
                  (pat1, uu____5753)
              | uu____5782 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5701 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5808);
                         FStar_Parser_AST.prange = uu____5809;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5826 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5826 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5832 =
                        if inner_let
                        then
                          let uu____5846 = pats_as_binders_if_possible pats
                             in
                          match uu____5846 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5869 = pats_as_binders_if_possible pats
                              in
                           match uu____5869 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5832 with
                       | (terms,style) ->
                           let uu____5896 =
                             let uu____5897 =
                               let uu____5898 =
                                 let uu____5899 = p_lident lid  in
                                 let uu____5900 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5899
                                   uu____5900
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5898
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5897  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5896)
                  | uu____5903 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5911 =
                              let uu____5912 =
                                let uu____5913 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5913
                                 in
                              FStar_Pprint.group uu____5912  in
                            FStar_Pprint.op_Hat_Hat uu____5911 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5924 =
                        let uu____5925 =
                          let uu____5926 =
                            let uu____5927 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5927  in
                          FStar_Pprint.group uu____5926  in
                        FStar_Pprint.op_Hat_Hat uu____5925 ascr_doc  in
                      FStar_Pprint.group uu____5924))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5929  ->
      match uu____5929 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5938 = p_term_sep false false e  in
          (match uu____5938 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5948 =
                 let uu____5949 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5949  in
               let uu____5950 =
                 let uu____5951 =
                   let uu____5952 =
                     let uu____5953 =
                       let uu____5954 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5954
                        in
                     FStar_Pprint.group uu____5953  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5952  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5951  in
               FStar_Pprint.ifflat uu____5948 uu____5950)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5955  ->
    match uu___7_5955 with
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
        let uu____5980 = p_uident uid  in
        let uu____5981 = p_binders true bs  in
        let uu____5983 =
          let uu____5984 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5984  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5980
          uu____5981 uu____5983

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
          let uu____5999 =
            let uu____6000 =
              let uu____6001 =
                let uu____6002 = p_uident uid  in
                let uu____6003 = p_binders true bs  in
                let uu____6005 =
                  let uu____6006 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6006  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6002 uu____6003 uu____6005
                 in
              FStar_Pprint.group uu____6001  in
            let uu____6011 =
              let uu____6012 = str "with"  in
              let uu____6014 =
                let uu____6015 =
                  let uu____6016 =
                    let uu____6017 =
                      let uu____6018 =
                        let uu____6019 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6019
                         in
                      separate_map_last uu____6018 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6017  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6016  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6015  in
              FStar_Pprint.op_Hat_Hat uu____6012 uu____6014  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6000 uu____6011  in
          braces_with_nesting uu____5999

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____6023,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6036 =
            let uu____6037 = p_lident lid  in
            let uu____6038 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6037 uu____6038  in
          let uu____6039 = p_simpleTerm ps false e  in
          prefix2 uu____6036 uu____6039
      | uu____6041 ->
          let uu____6042 =
            let uu____6044 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6044
             in
          failwith uu____6042

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6127 =
        match uu____6127 with
        | (kwd,t) ->
            let uu____6138 =
              let uu____6139 = str kwd  in
              let uu____6140 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6139 uu____6140  in
            let uu____6141 = p_simpleTerm ps false t  in
            prefix2 uu____6138 uu____6141
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6148 =
      let uu____6149 =
        let uu____6150 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6151 =
          let uu____6152 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6152  in
        FStar_Pprint.op_Hat_Hat uu____6150 uu____6151  in
      let uu____6154 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6149 uu____6154  in
    let uu____6155 =
      let uu____6156 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6156  in
    FStar_Pprint.op_Hat_Hat uu____6148 uu____6155

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6157  ->
    match uu___8_6157 with
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
        let uu____6177 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6177 FStar_Pprint.hardline
    | uu____6178 ->
        let uu____6179 =
          let uu____6180 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6180  in
        FStar_Pprint.op_Hat_Hat uu____6179 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6183  ->
    match uu___9_6183 with
    | FStar_Parser_AST.Rec  ->
        let uu____6184 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6184
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6186  ->
    match uu___10_6186 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6191,e) -> e
          | uu____6197 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6198 = str "#["  in
        let uu____6200 =
          let uu____6201 = p_term false false t1  in
          let uu____6204 =
            let uu____6205 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6205 break1  in
          FStar_Pprint.op_Hat_Hat uu____6201 uu____6204  in
        FStar_Pprint.op_Hat_Hat uu____6198 uu____6200

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6211 =
          let uu____6212 =
            let uu____6213 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6213  in
          FStar_Pprint.separate_map uu____6212 p_tuplePattern pats  in
        FStar_Pprint.group uu____6211
    | uu____6214 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6223 =
          let uu____6224 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6224 p_constructorPattern pats  in
        FStar_Pprint.group uu____6223
    | uu____6225 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6228;_},hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6233 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6234 = p_constructorPattern hd  in
        let uu____6235 = p_constructorPattern tl  in
        infix0 uu____6233 uu____6234 uu____6235
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6237;_},pats)
        ->
        let uu____6243 = p_quident uid  in
        let uu____6244 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6243 uu____6244
    | uu____6245 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6261;
               FStar_Parser_AST.blevel = uu____6262;
               FStar_Parser_AST.aqual = uu____6263;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6272 =
               let uu____6273 = p_ident lid  in
               p_refinement aqual uu____6273 t1 phi  in
             soft_parens_with_nesting uu____6272
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6276;
               FStar_Parser_AST.blevel = uu____6277;
               FStar_Parser_AST.aqual = uu____6278;_},phi))
             ->
             let uu____6284 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6284
         | uu____6285 ->
             let uu____6290 =
               let uu____6291 = p_tuplePattern pat  in
               let uu____6292 =
                 let uu____6293 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6293
                  in
               FStar_Pprint.op_Hat_Hat uu____6291 uu____6292  in
             soft_parens_with_nesting uu____6290)
    | FStar_Parser_AST.PatList pats ->
        let uu____6297 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6297 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6316 =
          match uu____6316 with
          | (lid,pat) ->
              let uu____6323 = p_qlident lid  in
              let uu____6324 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6323 uu____6324
           in
        let uu____6325 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6325
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6337 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6338 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6339 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6337
          uu____6338 uu____6339
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6350 =
          let uu____6351 =
            let uu____6352 =
              let uu____6353 = FStar_Ident.text_of_id op  in str uu____6353
               in
            let uu____6355 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6352 uu____6355  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6351  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6350
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6359 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6359 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6367 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6368 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6367 uu____6368
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6370 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6374;
           FStar_Parser_AST.prange = uu____6375;_},uu____6376)
        ->
        let uu____6381 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6381
    | FStar_Parser_AST.PatTuple (uu____6382,false ) ->
        let uu____6389 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6389
    | uu____6390 ->
        let uu____6391 =
          let uu____6393 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6393  in
        failwith uu____6391

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6398;_},uu____6399)
        -> true
    | uu____6406 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6412) -> true
    | uu____6414 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6421 = p_binder' is_atomic b  in
      match uu____6421 with
      | (b',t',catf1) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf1 b' typ
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
          let uu____6458 =
            let uu____6459 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6460 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6459 uu____6460  in
          (uu____6458, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6466 = p_lident lid  in
          (uu____6466, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6473 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6484;
                   FStar_Parser_AST.blevel = uu____6485;
                   FStar_Parser_AST.aqual = uu____6486;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6491 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6491 t1 phi
            | uu____6492 ->
                let t' =
                  let uu____6494 = is_typ_tuple t  in
                  if uu____6494
                  then
                    let uu____6497 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6497
                  else p_tmFormula t  in
                let uu____6500 =
                  let uu____6501 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6502 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6501 uu____6502  in
                (uu____6500, t')
             in
          (match uu____6473 with
           | (b',t') ->
               let catf1 =
                 let uu____6520 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6520
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6527 =
                         let uu____6528 =
                           let uu____6529 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6529
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6528
                          in
                       FStar_Pprint.group uu____6527
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6534 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6534)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf1))
      | FStar_Parser_AST.TAnnotated uu____6539 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6567;
                  FStar_Parser_AST.blevel = uu____6568;
                  FStar_Parser_AST.aqual = uu____6569;_},phi)
               ->
               let uu____6573 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6573 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6594 ->
               if is_atomic
               then
                 let uu____6606 = p_atomicTerm t  in
                 (uu____6606, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6613 = p_appTerm t  in
                  (uu____6613, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6624 = p_refinement' aqual_opt binder t phi  in
          match uu____6624 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____6640 -> false
            | FStar_Parser_AST.App uu____6652 -> false
            | FStar_Parser_AST.Op uu____6660 -> false
            | uu____6668 -> true  in
          let uu____6670 = p_noSeqTerm false false phi  in
          match uu____6670 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6687 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6687)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____6696 =
                let uu____6697 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6697 binder  in
              let uu____6698 =
                let uu____6699 = p_appTerm t  in
                let uu____6700 =
                  let uu____6701 =
                    let uu____6702 =
                      let uu____6703 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6704 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6703 uu____6704  in
                    FStar_Pprint.group uu____6702  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6701
                   in
                FStar_Pprint.op_Hat_Hat uu____6699 uu____6700  in
              (uu____6696, uu____6698)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6718 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6718

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6722 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6725 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6725)
       in
    if uu____6722
    then FStar_Pprint.underscore
    else (let uu____6730 = FStar_Ident.text_of_id lid  in str uu____6730)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6733 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6736 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6736)
       in
    if uu____6733
    then FStar_Pprint.underscore
    else (let uu____6741 = FStar_Ident.text_of_lid lid  in str uu____6741)

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
          let uu____6762 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6762
        else
          (let uu____6765 =
             let uu____6766 =
               let uu____6767 =
                 let uu____6768 =
                   let uu____6769 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6769  in
                 FStar_Pprint.op_Hat_Hat doc uu____6768  in
               FStar_Pprint.group uu____6767  in
             let uu____6770 =
               let uu____6771 =
                 let uu____6772 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6772  in
               FStar_Pprint.op_Hat_Hat comm uu____6771  in
             FStar_Pprint.ifflat uu____6766 uu____6770  in
           FStar_All.pipe_left FStar_Pprint.group uu____6765)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6780 = p_noSeqTerm true false e1  in
            (match uu____6780 with
             | (comm,t1) ->
                 let uu____6789 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6790 =
                   let uu____6791 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6791
                    in
                 FStar_Pprint.op_Hat_Hat uu____6789 uu____6790)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6795 =
              let uu____6796 =
                let uu____6797 =
                  let uu____6798 = p_lident x  in
                  let uu____6799 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6798 uu____6799  in
                let uu____6800 =
                  let uu____6801 = p_noSeqTermAndComment true false e1  in
                  let uu____6804 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6801 uu____6804  in
                op_Hat_Slash_Plus_Hat uu____6797 uu____6800  in
              FStar_Pprint.group uu____6796  in
            let uu____6805 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6795 uu____6805
        | uu____6806 ->
            let uu____6807 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6807

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
            let uu____6819 = p_noSeqTerm true false e1  in
            (match uu____6819 with
             | (comm,t1) ->
                 let uu____6832 =
                   let uu____6833 =
                     let uu____6834 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6834  in
                   let uu____6835 =
                     let uu____6836 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6836
                      in
                   FStar_Pprint.op_Hat_Hat uu____6833 uu____6835  in
                 (comm, uu____6832))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6840 =
              let uu____6841 =
                let uu____6842 =
                  let uu____6843 =
                    let uu____6844 = p_lident x  in
                    let uu____6845 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6844 uu____6845  in
                  let uu____6846 =
                    let uu____6847 = p_noSeqTermAndComment true false e1  in
                    let uu____6850 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6847 uu____6850  in
                  op_Hat_Slash_Plus_Hat uu____6843 uu____6846  in
                FStar_Pprint.group uu____6842  in
              let uu____6851 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6841 uu____6851  in
            (FStar_Pprint.empty, uu____6840)
        | uu____6852 -> p_noSeqTerm ps pb e

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
            let uu____6872 =
              let uu____6873 = p_tmIff e1  in
              let uu____6874 =
                let uu____6875 =
                  let uu____6876 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6876
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6875  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6873 uu____6874  in
            FStar_Pprint.group uu____6872
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6882 =
              let uu____6883 = p_tmIff e1  in
              let uu____6884 =
                let uu____6885 =
                  let uu____6886 =
                    let uu____6887 = p_typ false false t  in
                    let uu____6890 =
                      let uu____6891 = str "by"  in
                      let uu____6893 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6891 uu____6893  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6887 uu____6890  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6886
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6885  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6883 uu____6884  in
            FStar_Pprint.group uu____6882
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____6894;_},e1::e2::e3::[])
            ->
            let uu____6901 =
              let uu____6902 =
                let uu____6903 =
                  let uu____6904 = p_atomicTermNotQUident e1  in
                  let uu____6905 =
                    let uu____6906 =
                      let uu____6907 =
                        let uu____6908 = p_term false false e2  in
                        soft_parens_with_nesting uu____6908  in
                      let uu____6911 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6907 uu____6911  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6906  in
                  FStar_Pprint.op_Hat_Hat uu____6904 uu____6905  in
                FStar_Pprint.group uu____6903  in
              let uu____6912 =
                let uu____6913 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6913  in
              FStar_Pprint.op_Hat_Hat uu____6902 uu____6912  in
            FStar_Pprint.group uu____6901
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____6914;_},e1::e2::e3::[])
            ->
            let uu____6921 =
              let uu____6922 =
                let uu____6923 =
                  let uu____6924 = p_atomicTermNotQUident e1  in
                  let uu____6925 =
                    let uu____6926 =
                      let uu____6927 =
                        let uu____6928 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6928  in
                      let uu____6931 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6927 uu____6931  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6926  in
                  FStar_Pprint.op_Hat_Hat uu____6924 uu____6925  in
                FStar_Pprint.group uu____6923  in
              let uu____6932 =
                let uu____6933 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6933  in
              FStar_Pprint.op_Hat_Hat uu____6922 uu____6932  in
            FStar_Pprint.group uu____6921
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6943 =
              let uu____6944 = str "requires"  in
              let uu____6946 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6944 uu____6946  in
            FStar_Pprint.group uu____6943
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6956 =
              let uu____6957 = str "ensures"  in
              let uu____6959 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6957 uu____6959  in
            FStar_Pprint.group uu____6956
        | FStar_Parser_AST.Attributes es ->
            let uu____6963 =
              let uu____6964 = str "attributes"  in
              let uu____6966 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6964 uu____6966  in
            FStar_Pprint.group uu____6963
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____6971 =
                let uu____6972 =
                  let uu____6973 = str "if"  in
                  let uu____6975 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____6973 uu____6975  in
                let uu____6978 =
                  let uu____6979 = str "then"  in
                  let uu____6981 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____6979 uu____6981  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6972 uu____6978  in
              FStar_Pprint.group uu____6971
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____6985,uu____6986,e31) when
                     is_unit e31 ->
                     let uu____6988 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____6988
                 | uu____6991 -> p_noSeqTermAndComment false false e2  in
               let uu____6994 =
                 let uu____6995 =
                   let uu____6996 = str "if"  in
                   let uu____6998 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____6996 uu____6998  in
                 let uu____7001 =
                   let uu____7002 =
                     let uu____7003 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7003 e2_doc  in
                   let uu____7005 =
                     let uu____7006 = str "else"  in
                     let uu____7008 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7006 uu____7008  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7002 uu____7005  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____6995 uu____7001  in
               FStar_Pprint.group uu____6994)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7031 =
              let uu____7032 =
                let uu____7033 =
                  let uu____7034 = str "try"  in
                  let uu____7036 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7034 uu____7036  in
                let uu____7039 =
                  let uu____7040 = str "with"  in
                  let uu____7042 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7040 uu____7042  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7033 uu____7039  in
              FStar_Pprint.group uu____7032  in
            let uu____7051 = paren_if (ps || pb)  in uu____7051 uu____7031
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7078 =
              let uu____7079 =
                let uu____7080 =
                  let uu____7081 = str "match"  in
                  let uu____7083 = p_noSeqTermAndComment false false e1  in
                  let uu____7086 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7081 uu____7083 uu____7086
                   in
                let uu____7090 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7080 uu____7090  in
              FStar_Pprint.group uu____7079  in
            let uu____7099 = paren_if (ps || pb)  in uu____7099 uu____7078
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7106 =
              let uu____7107 =
                let uu____7108 =
                  let uu____7109 = str "let open"  in
                  let uu____7111 = p_quident uid  in
                  let uu____7112 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7109 uu____7111 uu____7112
                   in
                let uu____7116 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7108 uu____7116  in
              FStar_Pprint.group uu____7107  in
            let uu____7118 = paren_if ps  in uu____7118 uu____7106
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7183 is_last =
              match uu____7183 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7217 =
                          let uu____7218 = str "let"  in
                          let uu____7220 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7218 uu____7220
                           in
                        FStar_Pprint.group uu____7217
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7223 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7229 = p_term_sep false false e2  in
                  (match uu____7229 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7239 =
                         if is_last
                         then
                           let uu____7241 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7242 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7241 doc_expr1 uu____7242
                         else
                           (let uu____7248 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7248)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7239)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7299 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7299
                     else
                       (let uu____7304 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7304)) lbs
               in
            let lbs_doc =
              let uu____7308 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7308  in
            let uu____7309 =
              let uu____7310 =
                let uu____7311 =
                  let uu____7312 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7312
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7311  in
              FStar_Pprint.group uu____7310  in
            let uu____7314 = paren_if ps  in uu____7314 uu____7309
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7321;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7324;
                                                             FStar_Parser_AST.level
                                                               = uu____7325;_})
            when matches_var maybe_x x ->
            let uu____7352 =
              let uu____7353 =
                let uu____7354 = str "function"  in
                let uu____7356 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7354 uu____7356  in
              FStar_Pprint.group uu____7353  in
            let uu____7365 = paren_if (ps || pb)  in uu____7365 uu____7352
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7371 =
              let uu____7372 = str "quote"  in
              let uu____7374 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7372 uu____7374  in
            FStar_Pprint.group uu____7371
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7376 =
              let uu____7377 = str "`"  in
              let uu____7379 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7377 uu____7379  in
            FStar_Pprint.group uu____7376
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7381 =
              let uu____7382 = str "`%"  in
              let uu____7384 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7382 uu____7384  in
            FStar_Pprint.group uu____7381
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7386;
              FStar_Parser_AST.level = uu____7387;_}
            ->
            let uu____7388 =
              let uu____7389 = str "`@"  in
              let uu____7391 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7389 uu____7391  in
            FStar_Pprint.group uu____7388
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7393 =
              let uu____7394 = str "`#"  in
              let uu____7396 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7394 uu____7396  in
            FStar_Pprint.group uu____7393
        | FStar_Parser_AST.CalcProof (rel,init,steps) ->
            let head =
              let uu____7405 = str "calc"  in
              let uu____7407 =
                let uu____7408 =
                  let uu____7409 = p_noSeqTermAndComment false false rel  in
                  let uu____7412 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7409 uu____7412  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7408  in
              FStar_Pprint.op_Hat_Hat uu____7405 uu____7407  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7414 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7415 =
              let uu____7416 =
                let uu____7417 =
                  let uu____7418 = p_noSeqTermAndComment false false init  in
                  let uu____7421 =
                    let uu____7422 = str ";"  in
                    let uu____7424 =
                      let uu____7425 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7425
                       in
                    FStar_Pprint.op_Hat_Hat uu____7422 uu____7424  in
                  FStar_Pprint.op_Hat_Hat uu____7418 uu____7421  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7417  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7416
               in
            FStar_Pprint.enclose head uu____7414 uu____7415
        | uu____7427 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7428  ->
    fun uu____7429  ->
      match uu____7429 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7434 =
            let uu____7435 = p_noSeqTermAndComment false false rel  in
            let uu____7438 =
              let uu____7439 =
                let uu____7440 =
                  let uu____7441 =
                    let uu____7442 = p_noSeqTermAndComment false false just
                       in
                    let uu____7445 =
                      let uu____7446 =
                        let uu____7447 =
                          let uu____7448 =
                            let uu____7449 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7452 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7449 uu____7452  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7448
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7447
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7446
                       in
                    FStar_Pprint.op_Hat_Hat uu____7442 uu____7445  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7441  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7440  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7439  in
            FStar_Pprint.op_Hat_Hat uu____7435 uu____7438  in
          FStar_Pprint.group uu____7434

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7454  ->
    match uu___11_7454 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7466 =
          let uu____7467 = str "[@"  in
          let uu____7469 =
            let uu____7470 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7471 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7470 uu____7471  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7467 uu____7469  in
        FStar_Pprint.group uu____7466

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
        | FStar_Parser_AST.QForall (bs,(uu____7489,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7523 =
                   let uu____7524 =
                     let uu____7525 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7525 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7524 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7523 term_doc
             | pats ->
                 let uu____7533 =
                   let uu____7534 =
                     let uu____7535 =
                       let uu____7536 =
                         let uu____7537 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7537
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7536 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7540 = p_trigger trigger  in
                     prefix2 uu____7535 uu____7540  in
                   FStar_Pprint.group uu____7534  in
                 prefix2 uu____7533 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7542,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7576 =
                   let uu____7577 =
                     let uu____7578 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7578 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7577 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7576 term_doc
             | pats ->
                 let uu____7586 =
                   let uu____7587 =
                     let uu____7588 =
                       let uu____7589 =
                         let uu____7590 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7590
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7589 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7593 = p_trigger trigger  in
                     prefix2 uu____7588 uu____7593  in
                   FStar_Pprint.group uu____7587  in
                 prefix2 uu____7586 term_doc)
        | uu____7594 -> p_simpleTerm ps pb e

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
      let uu____7615 = all_binders_annot t  in
      if uu____7615
      then
        let uu____7618 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7618
      else
        (let uu____7629 =
           let uu____7630 =
             let uu____7631 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7631  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7630  in
         FStar_Pprint.group uu____7629)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7690 = x  in
      match uu____7690 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu____7755 = hd  in
               (match uu____7755 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl))
       in
    let p_collapsed_binder cb =
      let uu____7827 = cb  in
      match uu____7827 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu____7846 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7852 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7852) hd tl
                  in
               cat_with_colon uu____7846 typ)
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
                 FStar_Parser_AST.brange = uu____7931;
                 FStar_Parser_AST.blevel = uu____7932;
                 FStar_Parser_AST.aqual = uu____7933;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____7942 =
                 let uu____7947 = p_ident lid  in
                 p_refinement' aqual uu____7947 t1 phi  in
               FStar_Pervasives_Native.Some uu____7942
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7954) ->
               let uu____7959 =
                 let uu____7964 =
                   let uu____7965 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____7966 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____7965 uu____7966  in
                 let uu____7967 = p_tmEqNoRefinement t  in
                 (uu____7964, uu____7967)  in
               FStar_Pervasives_Native.Some uu____7959
           | uu____7972 -> FStar_Pervasives_Native.None)
      | uu____7981 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____7994 -> false
      | uu____8006 -> true  in
    let uu____8008 = map_if_all all_binders pats  in
    match uu____8008 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8040 = collapse_pats bs  in
        (uu____8040, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8057 = FStar_List.map p_atomicPattern pats  in
        (uu____8057, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8069 -> str "forall"
    | FStar_Parser_AST.QExists uu____8089 -> str "exists"
    | uu____8109 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8111  ->
    match uu___12_8111 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8123 =
          let uu____8124 =
            let uu____8125 =
              let uu____8126 = str "pattern"  in
              let uu____8128 =
                let uu____8129 =
                  let uu____8130 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8130
                   in
                FStar_Pprint.op_Hat_Hat uu____8129 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8126 uu____8128  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8125  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8124  in
        FStar_Pprint.group uu____8123

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8138 = str "\\/"  in
    FStar_Pprint.separate_map uu____8138 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8145 =
      let uu____8146 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8146 p_appTerm pats  in
    FStar_Pprint.group uu____8145

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8158 = p_term_sep false pb e1  in
            (match uu____8158 with
             | (comm,doc) ->
                 let prefix =
                   let uu____8167 = str "fun"  in
                   let uu____8169 =
                     let uu____8170 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8170
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8167 uu____8169  in
                 let uu____8171 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8173 =
                       let uu____8174 =
                         let uu____8175 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8175  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8174
                        in
                     FStar_Pprint.op_Hat_Hat prefix uu____8173
                   else
                     (let uu____8178 = op_Hat_Slash_Plus_Hat prefix doc  in
                      FStar_Pprint.group uu____8178)
                    in
                 let uu____8179 = paren_if ps  in uu____8179 uu____8171)
        | uu____8184 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8192  ->
      match uu____8192 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8216 =
                    let uu____8217 =
                      let uu____8218 =
                        let uu____8219 = p_tuplePattern p  in
                        let uu____8220 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8219 uu____8220  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8218
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8217  in
                  FStar_Pprint.group uu____8216
              | FStar_Pervasives_Native.Some f ->
                  let uu____8222 =
                    let uu____8223 =
                      let uu____8224 =
                        let uu____8225 =
                          let uu____8226 =
                            let uu____8227 = p_tuplePattern p  in
                            let uu____8228 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8227
                              uu____8228
                             in
                          FStar_Pprint.group uu____8226  in
                        let uu____8230 =
                          let uu____8231 =
                            let uu____8234 = p_tmFormula f  in
                            [uu____8234; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8231  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8225 uu____8230
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8224
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8223  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8222
               in
            let uu____8236 = p_term_sep false pb e  in
            match uu____8236 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8246 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8246
                   else
                     (let uu____8249 =
                        let uu____8250 =
                          let uu____8251 =
                            let uu____8252 =
                              let uu____8253 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8253  in
                            op_Hat_Slash_Plus_Hat branch uu____8252  in
                          FStar_Pprint.group uu____8251  in
                        let uu____8254 =
                          let uu____8255 =
                            let uu____8256 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8256  in
                          FStar_Pprint.op_Hat_Hat branch uu____8255  in
                        FStar_Pprint.ifflat uu____8250 uu____8254  in
                      FStar_Pprint.group uu____8249))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8260 =
                       let uu____8261 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8261  in
                     op_Hat_Slash_Plus_Hat branch uu____8260)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd  in
                    let uu____8272 =
                      let uu____8273 =
                        let uu____8274 =
                          let uu____8275 =
                            let uu____8276 =
                              let uu____8277 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8277  in
                            FStar_Pprint.separate_map uu____8276
                              p_tuplePattern (FStar_List.rev tl)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8275
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8274
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8273  in
                    FStar_Pprint.group uu____8272
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8279 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8281;_},e1::e2::[])
        ->
        let uu____8287 = str "<==>"  in
        let uu____8289 = p_tmImplies e1  in
        let uu____8290 = p_tmIff e2  in
        infix0 uu____8287 uu____8289 uu____8290
    | uu____8291 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8293;_},e1::e2::[])
        ->
        let uu____8299 = str "==>"  in
        let uu____8301 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8307 = p_tmImplies e2  in
        infix0 uu____8299 uu____8301 uu____8307
    | uu____8308 ->
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
          let uu____8322 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8322 with
          | (terms',last) ->
              let uu____8342 =
                match style with
                | Arrows (n,ln) ->
                    let uu____8377 =
                      let uu____8378 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8378
                       in
                    let uu____8379 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n, ln, terms', uu____8377, uu____8379)
                | Binders (n,ln,parens) ->
                    let uu____8393 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8401 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n, ln, uu____8393, break1, uu____8401)
                 in
              (match uu____8342 with
               | (n,last_n,terms'1,sep,last_op) ->
                   let last1 = FStar_List.hd last  in
                   let last_op1 =
                     if
                       ((FStar_List.length terms) > Prims.int_one) &&
                         (Prims.op_Negation no_last_op)
                     then last_op
                     else FStar_Pprint.empty  in
                   let one_line_space =
                     if
                       (Prims.op_Negation (last1 = FStar_Pprint.empty)) ||
                         (Prims.op_Negation no_last_op)
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   let single_line_arg_indent =
                     FStar_Pprint.repeat n FStar_Pprint.space  in
                   let fs =
                     if flat_space
                     then FStar_Pprint.space
                     else FStar_Pprint.empty  in
                   (match FStar_List.length terms with
                    | uu____8434 when uu____8434 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu____8435 ->
                        let uu____8436 =
                          let uu____8437 =
                            let uu____8438 =
                              let uu____8439 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8440 =
                                let uu____8441 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8441
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8439 uu____8440
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8438  in
                          let uu____8442 =
                            let uu____8443 =
                              let uu____8444 =
                                let uu____8445 =
                                  let uu____8446 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8446  in
                                let uu____8447 =
                                  let uu____8448 =
                                    let uu____8449 =
                                      let uu____8450 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8451 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8457 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8457)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8450
                                        uu____8451
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8449
                                     in
                                  jump2 uu____8448  in
                                FStar_Pprint.ifflat uu____8445 uu____8447  in
                              FStar_Pprint.group uu____8444  in
                            let uu____8459 =
                              let uu____8460 =
                                let uu____8461 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.hang last_n uu____8461  in
                              FStar_Pprint.align uu____8460  in
                            FStar_Pprint.prefix n Prims.int_one uu____8443
                              uu____8459
                             in
                          FStar_Pprint.ifflat uu____8437 uu____8442  in
                        FStar_Pprint.group uu____8436))

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
            | Arrows uu____8475 -> p_tmArrow' p_Tm e
            | Binders uu____8482 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8505 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8511 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8505 uu____8511
      | uu____8514 -> let uu____8515 = p_Tm e  in [uu____8515]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8568 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8594 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8568 uu____8594
        | uu____8617 ->
            let uu____8618 =
              let uu____8629 = p_Tm1 e1  in
              (uu____8629, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8618]
         in
      let fold_fun bs x =
        let uu____8727 = x  in
        match uu____8727 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu____8859 = hd  in
                 (match uu____8859 with
                  | (b2s,t2,uu____8888) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu____8990 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9047 = cb  in
        match uu____9047 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9076 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu____9087 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9093 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9093) hd tl
                         in
                      f uu____9087 typ))
         in
      let binders =
        let uu____9109 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9109  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9172 =
        let uu____9173 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9173 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9172  in
    let disj =
      let uu____9176 =
        let uu____9177 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9177 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9176  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9197;_},e1::e2::[])
        ->
        let uu____9203 = p_tmDisjunction e1  in
        let uu____9208 = let uu____9213 = p_tmConjunction e2  in [uu____9213]
           in
        FStar_List.append uu____9203 uu____9208
    | uu____9222 -> let uu____9223 = p_tmConjunction e  in [uu____9223]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9233;_},e1::e2::[])
        ->
        let uu____9239 = p_tmConjunction e1  in
        let uu____9242 = let uu____9245 = p_tmTuple e2  in [uu____9245]  in
        FStar_List.append uu____9239 uu____9242
    | uu____9246 -> let uu____9247 = p_tmTuple e  in [uu____9247]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9264 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9264
          (fun uu____9272  ->
             match uu____9272 with | (e1,uu____9278) -> p_tmEq e1) args
    | uu____9279 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9288 =
             let uu____9289 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9289  in
           FStar_Pprint.group uu____9288)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n =
        max_level
          (FStar_List.append [colon_equals; pipe_right] operatorInfix0ad12)
         in
      p_tmEqWith' p_X n e

and (p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            (let uu____9309 =
               (let uu____9313 = FStar_Ident.text_of_id op  in
                uu____9313 = "==>") ||
                 (let uu____9318 = FStar_Ident.text_of_id op  in
                  uu____9318 = "<==>")
                in
             Prims.op_Negation uu____9309) &&
              (((is_operatorInfix0ad12 op) ||
                  (let uu____9323 = FStar_Ident.text_of_id op  in
                   uu____9323 = "="))
                 ||
                 (let uu____9328 = FStar_Ident.text_of_id op  in
                  uu____9328 = "|>"))
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9334 = levels op1  in
            (match uu____9334 with
             | (left,mine,right) ->
                 let uu____9353 =
                   let uu____9354 = FStar_All.pipe_left str op1  in
                   let uu____9356 = p_tmEqWith' p_X left e1  in
                   let uu____9357 = p_tmEqWith' p_X right e2  in
                   infix0 uu____9354 uu____9356 uu____9357  in
                 paren_if_gt curr mine uu____9353)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9358;_},e1::e2::[])
            ->
            let uu____9364 =
              let uu____9365 = p_tmEqWith p_X e1  in
              let uu____9366 =
                let uu____9367 =
                  let uu____9368 =
                    let uu____9369 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9369  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9368  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9367  in
              FStar_Pprint.op_Hat_Hat uu____9365 uu____9366  in
            FStar_Pprint.group uu____9364
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9370;_},e1::[])
            ->
            let uu____9375 = levels "-"  in
            (match uu____9375 with
             | (left,mine,right) ->
                 let uu____9395 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9395)
        | uu____9396 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' false p_X n e

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
              (lid,(e1,uu____9444)::(e2,uu____9446)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9466 = is_list e  in Prims.op_Negation uu____9466)
              ->
              let op = "::"  in
              let uu____9471 = levels op  in
              (match uu____9471 with
               | (left,mine,right) ->
                   let uu____9490 =
                     let uu____9491 = str op  in
                     let uu____9492 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9494 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9491 uu____9492 uu____9494  in
                   paren_if_gt curr mine uu____9490)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9513 = levels op  in
              (match uu____9513 with
               | (left,mine,right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9547 = p_binder false b  in
                         let uu____9549 =
                           let uu____9550 =
                             let uu____9551 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9551 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9550
                            in
                         FStar_Pprint.op_Hat_Hat uu____9547 uu____9549
                     | FStar_Util.Inr t ->
                         let uu____9553 = p_tmNoEqWith' false p_X left t  in
                         let uu____9555 =
                           let uu____9556 =
                             let uu____9557 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9557 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9556
                            in
                         FStar_Pprint.op_Hat_Hat uu____9553 uu____9555
                      in
                   let uu____9558 =
                     let uu____9559 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9564 = p_tmNoEqWith' false p_X right res  in
                     FStar_Pprint.op_Hat_Hat uu____9559 uu____9564  in
                   paren_if_gt curr mine uu____9558)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____9566;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____9596 = levels op  in
              (match uu____9596 with
               | (left,mine,right) ->
                   if inside_tuple
                   then
                     let uu____9616 = str op  in
                     let uu____9617 = p_tmNoEqWith' true p_X left e1  in
                     let uu____9619 = p_tmNoEqWith' true p_X right e2  in
                     infix0 uu____9616 uu____9617 uu____9619
                   else
                     (let uu____9623 =
                        let uu____9624 = str op  in
                        let uu____9625 = p_tmNoEqWith' true p_X left e1  in
                        let uu____9627 = p_tmNoEqWith' true p_X right e2  in
                        infix0 uu____9624 uu____9625 uu____9627  in
                      paren_if_gt curr mine uu____9623))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9636 = levels op1  in
              (match uu____9636 with
               | (left,mine,right) ->
                   let uu____9655 =
                     let uu____9656 = str op1  in
                     let uu____9657 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9659 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9656 uu____9657 uu____9659  in
                   paren_if_gt curr mine uu____9655)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9679 =
                let uu____9680 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9681 =
                  let uu____9682 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9682 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9680 uu____9681  in
              braces_with_nesting uu____9679
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____9687;_},e1::[])
              ->
              let uu____9692 =
                let uu____9693 = str "~"  in
                let uu____9695 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9693 uu____9695  in
              FStar_Pprint.group uu____9692
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____9697;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____9706 = levels op  in
                   (match uu____9706 with
                    | (left,mine,right) ->
                        let uu____9725 =
                          let uu____9726 = str op  in
                          let uu____9727 = p_tmNoEqWith' true p_X left e1  in
                          let uu____9729 = p_tmNoEqWith' true p_X right e2
                             in
                          infix0 uu____9726 uu____9727 uu____9729  in
                        paren_if_gt curr mine uu____9725)
               | uu____9731 -> p_X e)
          | uu____9732 -> p_X e

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
        let uu____9739 =
          let uu____9740 = p_lident lid  in
          let uu____9741 =
            let uu____9742 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9742  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9740 uu____9741  in
        FStar_Pprint.group uu____9739
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9745 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9747 = p_appTerm e  in
    let uu____9748 =
      let uu____9749 =
        let uu____9750 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9750 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9749  in
    FStar_Pprint.op_Hat_Hat uu____9747 uu____9748

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9756 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9756 t phi
      | FStar_Parser_AST.TAnnotated uu____9757 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9763 ->
          let uu____9764 =
            let uu____9766 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9766
             in
          failwith uu____9764
      | FStar_Parser_AST.TVariable uu____9769 ->
          let uu____9770 =
            let uu____9772 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9772
             in
          failwith uu____9770
      | FStar_Parser_AST.NoName uu____9775 ->
          let uu____9776 =
            let uu____9778 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9778
             in
          failwith uu____9776

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9782  ->
      match uu____9782 with
      | (lid,e) ->
          let uu____9790 =
            let uu____9791 = p_qlident lid  in
            let uu____9792 =
              let uu____9793 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9793
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9791 uu____9792  in
          FStar_Pprint.group uu____9790

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9796 when is_general_application e ->
        let uu____9803 = head_and_args e  in
        (match uu____9803 with
         | (head,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9850 = p_argTerm e1  in
                  let uu____9851 =
                    let uu____9852 =
                      let uu____9853 =
                        let uu____9854 = str "`"  in
                        let uu____9856 =
                          let uu____9857 = p_indexingTerm head  in
                          let uu____9858 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9857 uu____9858  in
                        FStar_Pprint.op_Hat_Hat uu____9854 uu____9856  in
                      FStar_Pprint.group uu____9853  in
                    let uu____9860 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9852 uu____9860  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9850 uu____9851
              | uu____9861 ->
                  let uu____9868 =
                    let uu____9879 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9879
                    then
                      let uu____9913 =
                        FStar_Util.take
                          (fun uu____9937  ->
                             match uu____9937 with
                             | (uu____9943,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9913 with
                      | (fs_typ_args,args1) ->
                          let uu____9981 =
                            let uu____9982 = p_indexingTerm head  in
                            let uu____9983 =
                              let uu____9984 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____9984
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____9982 uu____9983  in
                          (uu____9981, args1)
                    else
                      (let uu____9999 = p_indexingTerm head  in
                       (uu____9999, args))
                     in
                  (match uu____9868 with
                   | (head_doc,args1) ->
                       let uu____10020 =
                         let uu____10021 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10021 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10020)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10043 =
             (is_dtuple_constructor lid) && (all1_explicit args)  in
           Prims.op_Negation uu____10043)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10062 =
               let uu____10063 = p_quident lid  in
               let uu____10064 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10063 uu____10064  in
             FStar_Pprint.group uu____10062
         | hd::tl ->
             let uu____10081 =
               let uu____10082 =
                 let uu____10083 =
                   let uu____10084 = p_quident lid  in
                   let uu____10085 = p_argTerm hd  in
                   prefix2 uu____10084 uu____10085  in
                 FStar_Pprint.group uu____10083  in
               let uu____10086 =
                 let uu____10087 =
                   FStar_Pprint.separate_map break1 p_argTerm tl  in
                 jump2 uu____10087  in
               FStar_Pprint.op_Hat_Hat uu____10082 uu____10086  in
             FStar_Pprint.group uu____10081)
    | uu____10092 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10103 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10103 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10107 = str "#"  in
        let uu____10109 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10107 uu____10109
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10112 = str "#["  in
        let uu____10114 =
          let uu____10115 = p_indexingTerm t  in
          let uu____10116 =
            let uu____10117 = str "]"  in
            let uu____10119 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10117 uu____10119  in
          FStar_Pprint.op_Hat_Hat uu____10115 uu____10116  in
        FStar_Pprint.op_Hat_Hat uu____10112 uu____10114
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10122  ->
    match uu____10122 with | (e,uu____10128) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10133;_},e1::e2::[])
          ->
          let uu____10139 =
            let uu____10140 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10141 =
              let uu____10142 =
                let uu____10143 = p_term false false e2  in
                soft_parens_with_nesting uu____10143  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10142  in
            FStar_Pprint.op_Hat_Hat uu____10140 uu____10141  in
          FStar_Pprint.group uu____10139
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10146;_},e1::e2::[])
          ->
          let uu____10152 =
            let uu____10153 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10154 =
              let uu____10155 =
                let uu____10156 = p_term false false e2  in
                soft_brackets_with_nesting uu____10156  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10155  in
            FStar_Pprint.op_Hat_Hat uu____10153 uu____10154  in
          FStar_Pprint.group uu____10152
      | uu____10159 -> exit e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10164 = p_quident lid  in
        let uu____10165 =
          let uu____10166 =
            let uu____10167 = p_term false false e1  in
            soft_parens_with_nesting uu____10167  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10166  in
        FStar_Pprint.op_Hat_Hat uu____10164 uu____10165
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10175 =
          let uu____10176 = FStar_Ident.text_of_id op  in str uu____10176  in
        let uu____10178 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10175 uu____10178
    | uu____10179 -> p_atomicTermNotQUident e

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
         | uu____10192 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10201 =
          let uu____10202 = FStar_Ident.text_of_id op  in str uu____10202  in
        let uu____10204 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10201 uu____10204
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10208 =
          let uu____10209 =
            let uu____10210 =
              let uu____10211 = FStar_Ident.text_of_id op  in str uu____10211
               in
            let uu____10213 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10210 uu____10213  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10209  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10208
    | FStar_Parser_AST.Construct (lid,args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10228 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____10229 =
          let uu____10230 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____10230
            (fun uu____10238  ->
               match uu____10238 with | (e1,uu____10244) -> p_tmEq e1) args
           in
        let uu____10245 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10228
          uu____10229 uu____10245
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10250 =
          let uu____10251 = p_atomicTermNotQUident e1  in
          let uu____10252 =
            let uu____10253 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10253  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10251
            uu____10252
           in
        FStar_Pprint.group uu____10250
    | uu____10256 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10261 = p_quident constr_lid  in
        let uu____10262 =
          let uu____10263 =
            let uu____10264 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10264  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10263  in
        FStar_Pprint.op_Hat_Hat uu____10261 uu____10262
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10266 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10266 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10268 = p_term_sep false false e1  in
        (match uu____10268 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10281 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10281))
    | uu____10282 when is_array e ->
        let es = extract_from_list e  in
        let uu____10286 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10287 =
          let uu____10288 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10288
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10293 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10286
          uu____10287 uu____10293
    | uu____10296 when is_list e ->
        let uu____10297 =
          let uu____10298 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10299 = extract_from_list e  in
          separate_map_or_flow_last uu____10298
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10299
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10297 FStar_Pprint.rbracket
    | uu____10308 when is_lex_list e ->
        let uu____10309 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10310 =
          let uu____10311 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10312 = extract_from_list e  in
          separate_map_or_flow_last uu____10311
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10312
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10309
          uu____10310 FStar_Pprint.rbracket
    | uu____10321 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10325 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10326 =
          let uu____10327 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10327 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10325
          uu____10326 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10337 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10340 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10337 uu____10340
    | FStar_Parser_AST.Op (op,args) when
        let uu____10349 = handleable_op op args  in
        Prims.op_Negation uu____10349 ->
        let uu____10351 =
          let uu____10353 =
            let uu____10355 = FStar_Ident.text_of_id op  in
            let uu____10357 =
              let uu____10359 =
                let uu____10361 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10361
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10359  in
            Prims.op_Hat uu____10355 uu____10357  in
          Prims.op_Hat "Operation " uu____10353  in
        failwith uu____10351
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10368 = p_term false false e  in
        soft_parens_with_nesting uu____10368
    | FStar_Parser_AST.Const uu____10371 ->
        let uu____10372 = p_term false false e  in
        soft_parens_with_nesting uu____10372
    | FStar_Parser_AST.Op uu____10375 ->
        let uu____10382 = p_term false false e  in
        soft_parens_with_nesting uu____10382
    | FStar_Parser_AST.Tvar uu____10385 ->
        let uu____10386 = p_term false false e  in
        soft_parens_with_nesting uu____10386
    | FStar_Parser_AST.Var uu____10389 ->
        let uu____10390 = p_term false false e  in
        soft_parens_with_nesting uu____10390
    | FStar_Parser_AST.Name uu____10393 ->
        let uu____10394 = p_term false false e  in
        soft_parens_with_nesting uu____10394
    | FStar_Parser_AST.Construct uu____10397 ->
        let uu____10408 = p_term false false e  in
        soft_parens_with_nesting uu____10408
    | FStar_Parser_AST.Abs uu____10411 ->
        let uu____10418 = p_term false false e  in
        soft_parens_with_nesting uu____10418
    | FStar_Parser_AST.App uu____10421 ->
        let uu____10428 = p_term false false e  in
        soft_parens_with_nesting uu____10428
    | FStar_Parser_AST.Let uu____10431 ->
        let uu____10452 = p_term false false e  in
        soft_parens_with_nesting uu____10452
    | FStar_Parser_AST.LetOpen uu____10455 ->
        let uu____10460 = p_term false false e  in
        soft_parens_with_nesting uu____10460
    | FStar_Parser_AST.Seq uu____10463 ->
        let uu____10468 = p_term false false e  in
        soft_parens_with_nesting uu____10468
    | FStar_Parser_AST.Bind uu____10471 ->
        let uu____10478 = p_term false false e  in
        soft_parens_with_nesting uu____10478
    | FStar_Parser_AST.If uu____10481 ->
        let uu____10488 = p_term false false e  in
        soft_parens_with_nesting uu____10488
    | FStar_Parser_AST.Match uu____10491 ->
        let uu____10506 = p_term false false e  in
        soft_parens_with_nesting uu____10506
    | FStar_Parser_AST.TryWith uu____10509 ->
        let uu____10524 = p_term false false e  in
        soft_parens_with_nesting uu____10524
    | FStar_Parser_AST.Ascribed uu____10527 ->
        let uu____10536 = p_term false false e  in
        soft_parens_with_nesting uu____10536
    | FStar_Parser_AST.Record uu____10539 ->
        let uu____10552 = p_term false false e  in
        soft_parens_with_nesting uu____10552
    | FStar_Parser_AST.Project uu____10555 ->
        let uu____10560 = p_term false false e  in
        soft_parens_with_nesting uu____10560
    | FStar_Parser_AST.Product uu____10563 ->
        let uu____10570 = p_term false false e  in
        soft_parens_with_nesting uu____10570
    | FStar_Parser_AST.Sum uu____10573 ->
        let uu____10584 = p_term false false e  in
        soft_parens_with_nesting uu____10584
    | FStar_Parser_AST.QForall uu____10587 ->
        let uu____10606 = p_term false false e  in
        soft_parens_with_nesting uu____10606
    | FStar_Parser_AST.QExists uu____10609 ->
        let uu____10628 = p_term false false e  in
        soft_parens_with_nesting uu____10628
    | FStar_Parser_AST.Refine uu____10631 ->
        let uu____10636 = p_term false false e  in
        soft_parens_with_nesting uu____10636
    | FStar_Parser_AST.NamedTyp uu____10639 ->
        let uu____10644 = p_term false false e  in
        soft_parens_with_nesting uu____10644
    | FStar_Parser_AST.Requires uu____10647 ->
        let uu____10655 = p_term false false e  in
        soft_parens_with_nesting uu____10655
    | FStar_Parser_AST.Ensures uu____10658 ->
        let uu____10666 = p_term false false e  in
        soft_parens_with_nesting uu____10666
    | FStar_Parser_AST.Attributes uu____10669 ->
        let uu____10672 = p_term false false e  in
        soft_parens_with_nesting uu____10672
    | FStar_Parser_AST.Quote uu____10675 ->
        let uu____10680 = p_term false false e  in
        soft_parens_with_nesting uu____10680
    | FStar_Parser_AST.VQuote uu____10683 ->
        let uu____10684 = p_term false false e  in
        soft_parens_with_nesting uu____10684
    | FStar_Parser_AST.Antiquote uu____10687 ->
        let uu____10688 = p_term false false e  in
        soft_parens_with_nesting uu____10688
    | FStar_Parser_AST.CalcProof uu____10691 ->
        let uu____10700 = p_term false false e  in
        soft_parens_with_nesting uu____10700

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10703  ->
    match uu___15_10703 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10715) ->
        let uu____10718 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10718
    | FStar_Const.Const_bytearray (bytes,uu____10720) ->
        let uu____10727 =
          let uu____10728 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10728  in
        let uu____10729 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10727 uu____10729
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10752 =
          match uu___13_10752 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10759 =
          match uu___14_10759 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10774  ->
               match uu____10774 with
               | (s,w) ->
                   let uu____10781 = signedness s  in
                   let uu____10782 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10781 uu____10782)
            sign_width_opt
           in
        let uu____10783 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10783 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10787 = FStar_Range.string_of_range r  in str uu____10787
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10791 = p_quident lid  in
        let uu____10792 =
          let uu____10793 =
            let uu____10794 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10794  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10793  in
        FStar_Pprint.op_Hat_Hat uu____10791 uu____10792

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10797 = str "u#"  in
    let uu____10799 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10797 uu____10799

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10801;_},u1::u2::[])
        ->
        let uu____10807 =
          let uu____10808 = p_universeFrom u1  in
          let uu____10809 =
            let uu____10810 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10810  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10808 uu____10809  in
        FStar_Pprint.group uu____10807
    | FStar_Parser_AST.App uu____10811 ->
        let uu____10818 = head_and_args u  in
        (match uu____10818 with
         | (head,args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10844 =
                    let uu____10845 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10846 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10854  ->
                           match uu____10854 with
                           | (u1,uu____10860) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10845 uu____10846  in
                  FStar_Pprint.group uu____10844
              | uu____10861 ->
                  let uu____10862 =
                    let uu____10864 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10864
                     in
                  failwith uu____10862))
    | uu____10867 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu____10893 = FStar_Ident.text_of_id id  in str uu____10893
    | FStar_Parser_AST.Paren u1 ->
        let uu____10896 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10896
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10897;_},uu____10898::uu____10899::[])
        ->
        let uu____10903 = p_universeFrom u  in
        soft_parens_with_nesting uu____10903
    | FStar_Parser_AST.App uu____10904 ->
        let uu____10911 = p_universeFrom u  in
        soft_parens_with_nesting uu____10911
    | uu____10912 ->
        let uu____10913 =
          let uu____10915 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10915
           in
        failwith uu____10913

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
       | FStar_Parser_AST.Module (uu____11004,decls) ->
           let uu____11010 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11010
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11019,decls,uu____11021) ->
           let uu____11028 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11028
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11088  ->
         match uu____11088 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id,uu____11110)) -> false
      | ([],uu____11114) -> false
      | uu____11118 -> true  in
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
        | FStar_Parser_AST.Module (uu____11167,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11173,decls,uu____11175) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11227 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11240;
                 FStar_Parser_AST.quals = uu____11241;
                 FStar_Parser_AST.attrs = uu____11242;_}::uu____11243 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11247 =
                   let uu____11250 =
                     let uu____11253 = FStar_List.tl ds  in d :: uu____11253
                      in
                   d0 :: uu____11250  in
                 (uu____11247, (d0.FStar_Parser_AST.drange))
             | uu____11258 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11227 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11315 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11315 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11424 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11424, comments1))))))
  