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
          let uu____1182 = FStar_Ident.text_of_id x  in
          let uu____1184 = FStar_Ident.string_of_lid y  in
          uu____1182 = uu____1184
      | uu____1187 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1238::(e2,uu____1240)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid) && (aux e2)
        | uu____1263 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1287,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1298,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1319 = extract_from_list e2  in e1 :: uu____1319
    | uu____1322 ->
        let uu____1323 =
          let uu____1325 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1325  in
        failwith uu____1323
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1339;
           FStar_Parser_AST.level = uu____1340;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1342 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1354;
           FStar_Parser_AST.level = uu____1355;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1357;
                                                         FStar_Parser_AST.level
                                                           = uu____1358;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1360;
                                                    FStar_Parser_AST.level =
                                                      uu____1361;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1363;
                FStar_Parser_AST.level = uu____1364;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1366;
           FStar_Parser_AST.level = uu____1367;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1369 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1381 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1382;
           FStar_Parser_AST.range = uu____1383;
           FStar_Parser_AST.level = uu____1384;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1385;
                                                         FStar_Parser_AST.range
                                                           = uu____1386;
                                                         FStar_Parser_AST.level
                                                           = uu____1387;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1389;
                                                    FStar_Parser_AST.level =
                                                      uu____1390;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1391;
                FStar_Parser_AST.range = uu____1392;
                FStar_Parser_AST.level = uu____1393;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1395;
           FStar_Parser_AST.level = uu____1396;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1398 = extract_from_ref_set e1  in
        let uu____1401 = extract_from_ref_set e2  in
        FStar_List.append uu____1398 uu____1401
    | uu____1404 ->
        let uu____1405 =
          let uu____1407 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1407  in
        failwith uu____1405
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1419 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1419
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1428 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1428
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1439 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1439 Prims.int_zero  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1449 = FStar_Ident.text_of_id op  in uu____1449 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head,arg,imp) -> aux head ((arg, imp) :: acc)
      | uu____1519 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1539 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1550 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1561 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1587  ->
    match uu___1_1587 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1622  ->
      match uu___2_1622 with
      | FStar_Util.Inl c ->
          let uu____1635 = FStar_String.get s Prims.int_zero  in
          uu____1635 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'uuuuuu1651 .
    Prims.string ->
      ('uuuuuu1651 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1675  ->
      match uu____1675 with
      | (assoc_levels,tokens) ->
          let uu____1707 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1707 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_1879 =
    match uu___3_1879 with
    | Left  -> (l, l, (l - Prims.int_one))
    | Right  -> ((l - Prims.int_one), l, l)
    | NonAssoc  -> ((l - Prims.int_one), l, (l - Prims.int_one))  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1929  ->
         match uu____1929 with
         | (assoc,tokens) -> ((levels_from_associativity i assoc), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2004 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2004 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2056) ->
          assoc_levels
      | uu____2094 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'uuuuuu2127 . ('uuuuuu2127 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n level =
      let uu____2176 =
        FStar_List.tryFind
          (fun uu____2212  ->
             match uu____2212 with
             | (uu____2229,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2176 with
      | FStar_Pervasives_Native.Some ((uu____2258,l1,uu____2260),uu____2261)
          -> max n l1
      | FStar_Pervasives_Native.None  ->
          let uu____2311 =
            let uu____2313 =
              let uu____2315 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2315  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2313
             in
          failwith uu____2311
       in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2350 = assign_levels level_associativity_spec op  in
    match uu____2350 with
    | (left,mine,right) ->
        if op = "*"
        then ((left - Prims.int_one), mine, right)
        else (left, mine, right)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2409 =
      let uu____2412 =
        let uu____2418 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2418  in
      FStar_List.tryFind uu____2412 operatorInfix0ad12  in
    uu____2409 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2485 =
      let uu____2500 =
        let uu____2518 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2518  in
      FStar_List.tryFind uu____2500 opinfix34  in
    uu____2485 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2584 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2584
    then Prims.int_one
    else
      (let uu____2597 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2597
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
  
let handleable_op :
  'uuuuuu2643 . FStar_Ident.ident -> 'uuuuuu2643 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | uu____2659 when uu____2659 = Prims.int_zero -> true
      | uu____2661 when uu____2661 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2663 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2663 ["-"; "~"])
      | uu____2671 when uu____2671 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2673 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2673
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | uu____2695 when uu____2695 = (Prims.of_int (3)) ->
          let uu____2696 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2696 [".()<-"; ".[]<-"]
      | uu____2704 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2750 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2802 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2844 -> true
      | uu____2850 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2883 = FStar_List.for_all is_binder_annot bs  in
          if uu____2883
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2898 -> (true, (l + Prims.int_one))  in
    let uu____2903 = all_binders e Prims.int_zero  in
    match uu____2903 with
    | (b,l) -> if b && (l > Prims.int_one) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____2942 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____2942
  
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
  'uuuuuu3031 .
    ('uuuuuu3031 -> FStar_Pprint.document) ->
      'uuuuuu3031 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3073 = FStar_ST.op_Bang comment_stack  in
          match uu____3073 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3144 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3144 FStar_Pprint.hardline  in
              let uu____3145 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3145
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3187 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3187 print_pos lookahead_pos))
              else
                (let uu____3190 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3190))
           in
        let uu____3193 =
          let uu____3199 =
            let uu____3200 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3200  in
          let uu____3201 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3199 uu____3201  in
        match uu____3193 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3210 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3210
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3222 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3222)
  
let with_comment_sep :
  'uuuuuu3234 'uuuuuu3235 .
    ('uuuuuu3234 -> 'uuuuuu3235) ->
      'uuuuuu3234 ->
        FStar_Range.range -> (FStar_Pprint.document * 'uuuuuu3235)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3281 = FStar_ST.op_Bang comment_stack  in
          match uu____3281 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3352 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3352
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3394 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3398 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3398)
                     in
                  comments_before_pos uu____3394 print_pos lookahead_pos))
              else
                (let uu____3401 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3401))
           in
        let uu____3404 =
          let uu____3410 =
            let uu____3411 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3411  in
          let uu____3412 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3410 uu____3412  in
        match uu____3404 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3425 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3425
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
                let uu____3478 = FStar_ST.op_Bang comment_stack  in
                match uu____3478 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3572 =
                          let uu____3574 =
                            let uu____3576 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3576  in
                          uu____3574 - lbegin  in
                        max k uu____3572  in
                      let lnum1 = min (Prims.of_int (2)) lnum  in
                      let doc1 =
                        let uu____3581 =
                          let uu____3582 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3583 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3582 uu____3583  in
                        FStar_Pprint.op_Hat_Hat doc uu____3581  in
                      let uu____3584 =
                        let uu____3586 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3586  in
                      place_comments_until_pos Prims.int_one uu____3584 pos
                        meta_decl doc1 true init))
                | uu____3589 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3602 = FStar_Range.line_of_pos pos  in
                         uu____3602 - lbegin  in
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
                       let uu____3630 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc uu____3630)
  
let separate_map_with_comments :
  'uuuuuu3644 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('uuuuuu3644 -> FStar_Pprint.document) ->
          'uuuuuu3644 Prims.list ->
            ('uuuuuu3644 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3703 x =
              match uu____3703 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3722 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3722 meta_decl doc false false
                     in
                  let uu____3726 =
                    let uu____3728 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3728  in
                  let uu____3729 =
                    let uu____3730 =
                      let uu____3731 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3731  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3730  in
                  (uu____3726, uu____3729)
               in
            let uu____3733 =
              let uu____3740 = FStar_List.hd xs  in
              let uu____3741 = FStar_List.tl xs  in (uu____3740, uu____3741)
               in
            match uu____3733 with
            | (x,xs1) ->
                let init =
                  let meta_decl = extract_meta x  in
                  let uu____3759 =
                    let uu____3761 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3761  in
                  let uu____3762 =
                    let uu____3763 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix uu____3763  in
                  (uu____3759, uu____3762)  in
                let uu____3765 = FStar_List.fold_left fold_fun init xs1  in
                FStar_Pervasives_Native.snd uu____3765
  
let separate_map_with_comments_kw :
  'uuuuuu3792 'uuuuuu3793 .
    'uuuuuu3792 ->
      'uuuuuu3792 ->
        ('uuuuuu3792 -> 'uuuuuu3793 -> FStar_Pprint.document) ->
          'uuuuuu3793 Prims.list ->
            ('uuuuuu3793 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3857 x =
              match uu____3857 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3876 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3876 meta_decl doc false false
                     in
                  let uu____3880 =
                    let uu____3882 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3882  in
                  let uu____3883 =
                    let uu____3884 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3884  in
                  (uu____3880, uu____3883)
               in
            let uu____3886 =
              let uu____3893 = FStar_List.hd xs  in
              let uu____3894 = FStar_List.tl xs  in (uu____3893, uu____3894)
               in
            match uu____3886 with
            | (x,xs1) ->
                let init =
                  let meta_decl = extract_meta x  in
                  let uu____3912 =
                    let uu____3914 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3914  in
                  let uu____3915 = f prefix x  in (uu____3912, uu____3915)
                   in
                let uu____3917 = FStar_List.fold_left fold_fun init xs1  in
                FStar_Pervasives_Native.snd uu____3917
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id,uu____4873)) ->
          let uu____4876 =
            let uu____4878 =
              let uu____4880 = FStar_Ident.text_of_id id  in
              FStar_Util.char_at uu____4880 Prims.int_zero  in
            FStar_All.pipe_right uu____4878 FStar_Util.is_upper  in
          if uu____4876
          then
            let uu____4886 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4886 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4889 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4896 = p_attributes d.FStar_Parser_AST.attrs  in
    let uu____4897 =
      let uu____4898 = p_rawDecl d  in
      FStar_Pprint.op_Hat_Hat qualifiers uu____4898  in
    FStar_Pprint.op_Hat_Hat uu____4896 uu____4897

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4900 ->
        let uu____4901 =
          let uu____4902 = str "@ "  in
          let uu____4904 =
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4908  in
                FStar_Pprint.op_Hat_Hat uu____4907 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4906  in
            FStar_Pprint.op_Hat_Hat uu____4905 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4902 uu____4904  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4901

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4914 =
          let uu____4915 = str "val"  in
          let uu____4917 =
            let uu____4918 =
              let uu____4919 = p_lident lid  in
              let uu____4920 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4919 uu____4920  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4918  in
          FStar_Pprint.op_Hat_Hat uu____4915 uu____4917  in
        let uu____4921 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4914 uu____4921
    | FStar_Parser_AST.TopLevelLet (uu____4924,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4949 =
               let uu____4950 = str "let"  in p_letlhs uu____4950 lb false
                in
             FStar_Pprint.group uu____4949) lbs
    | uu____4953 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_4968 =
          match uu___4_4968 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4976 = f x  in
              let uu____4977 =
                let uu____4978 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4978  in
              FStar_Pprint.op_Hat_Hat uu____4976 uu____4977
           in
        let uu____4979 = str "["  in
        let uu____4981 =
          let uu____4982 = p_list' l  in
          let uu____4983 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4982 uu____4983  in
        FStar_Pprint.op_Hat_Hat uu____4979 uu____4981

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4987 =
          let uu____4988 = str "open"  in
          let uu____4990 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4988 uu____4990  in
        FStar_Pprint.group uu____4987
    | FStar_Parser_AST.Include uid ->
        let uu____4992 =
          let uu____4993 = str "include"  in
          let uu____4995 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4993 uu____4995  in
        FStar_Pprint.group uu____4992
    | FStar_Parser_AST.Friend uid ->
        let uu____4997 =
          let uu____4998 = str "friend"  in
          let uu____5000 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4998 uu____5000  in
        FStar_Pprint.group uu____4997
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5003 =
          let uu____5004 = str "module"  in
          let uu____5006 =
            let uu____5007 =
              let uu____5008 = p_uident uid1  in
              let uu____5009 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5008 uu____5009  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5007  in
          FStar_Pprint.op_Hat_Hat uu____5004 uu____5006  in
        let uu____5010 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5003 uu____5010
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5012 =
          let uu____5013 = str "module"  in
          let uu____5015 =
            let uu____5016 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5016  in
          FStar_Pprint.op_Hat_Hat uu____5013 uu____5015  in
        FStar_Pprint.group uu____5012
    | FStar_Parser_AST.Tycon
        (true ,uu____5017,(FStar_Parser_AST.TyconAbbrev
         (uid,tpars,FStar_Pervasives_Native.None ,t))::[])
        ->
        let effect_prefix_doc =
          let uu____5034 = str "effect"  in
          let uu____5036 =
            let uu____5037 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5037  in
          FStar_Pprint.op_Hat_Hat uu____5034 uu____5036  in
        let uu____5038 =
          let uu____5039 = p_typars tpars  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5039 FStar_Pprint.equals
           in
        let uu____5042 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5038 uu____5042
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5061 =
          let uu____5062 = FStar_List.hd tcdefs  in
          p_typeDeclWithKw s uu____5062  in
        let uu____5063 =
          let uu____5064 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5072 =
                    let uu____5073 = str "and"  in
                    p_typeDeclWithKw uu____5073 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5072)) uu____5064
           in
        FStar_Pprint.op_Hat_Hat uu____5061 uu____5063
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5090 = str "let"  in
          let uu____5092 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5090 uu____5092  in
        let uu____5093 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5093 p_letbinding lbs
          (fun uu____5103  ->
             match uu____5103 with
             | (p,t) ->
                 let uu____5110 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 { r = uu____5110; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5115 =
          let uu____5116 = str "val"  in
          let uu____5118 =
            let uu____5119 =
              let uu____5120 = p_lident lid  in
              let uu____5121 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5120 uu____5121  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5119  in
          FStar_Pprint.op_Hat_Hat uu____5116 uu____5118  in
        FStar_All.pipe_left FStar_Pprint.group uu____5115
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____5126 =
            let uu____5128 =
              let uu____5130 = FStar_Ident.text_of_id id  in
              FStar_Util.char_at uu____5130 Prims.int_zero  in
            FStar_All.pipe_right uu____5128 FStar_Util.is_upper  in
          if uu____5126
          then FStar_Pprint.empty
          else
            (let uu____5138 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5138 FStar_Pprint.space)
           in
        let uu____5140 =
          let uu____5141 = p_ident id  in
          let uu____5142 =
            let uu____5143 =
              let uu____5144 =
                let uu____5145 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5145  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5144  in
            FStar_Pprint.group uu____5143  in
          FStar_Pprint.op_Hat_Hat uu____5141 uu____5142  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5140
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5154 = str "exception"  in
        let uu____5156 =
          let uu____5157 =
            let uu____5158 = p_uident uid  in
            let uu____5159 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5163 =
                     let uu____5164 = str "of"  in
                     let uu____5166 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5164 uu____5166  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5163) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5158 uu____5159  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5157  in
        FStar_Pprint.op_Hat_Hat uu____5154 uu____5156
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5170 = str "new_effect"  in
        let uu____5172 =
          let uu____5173 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5173  in
        FStar_Pprint.op_Hat_Hat uu____5170 uu____5172
    | FStar_Parser_AST.SubEffect se ->
        let uu____5175 = str "sub_effect"  in
        let uu____5177 =
          let uu____5178 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5178  in
        FStar_Pprint.op_Hat_Hat uu____5175 uu____5177
    | FStar_Parser_AST.LayeredEffect ne ->
        let uu____5180 = str "layered_effect"  in
        let uu____5182 =
          let uu____5183 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5183  in
        FStar_Pprint.op_Hat_Hat uu____5180 uu____5182
    | FStar_Parser_AST.Polymonadic_bind (l1,l2,l3,t) ->
        let uu____5188 = str "polymonadic_bind"  in
        let uu____5190 =
          let uu____5191 =
            let uu____5192 = p_quident l1  in
            let uu____5193 =
              let uu____5194 =
                let uu____5195 =
                  let uu____5196 = p_quident l2  in
                  let uu____5197 =
                    let uu____5198 =
                      let uu____5199 = str "|>"  in
                      let uu____5201 =
                        let uu____5202 = p_quident l3  in
                        let uu____5203 =
                          let uu____5204 = p_simpleTerm false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals
                            uu____5204
                           in
                        FStar_Pprint.op_Hat_Hat uu____5202 uu____5203  in
                      FStar_Pprint.op_Hat_Hat uu____5199 uu____5201  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen uu____5198
                     in
                  FStar_Pprint.op_Hat_Hat uu____5196 uu____5197  in
                FStar_Pprint.op_Hat_Hat break1 uu____5195  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma uu____5194  in
            FStar_Pprint.op_Hat_Hat uu____5192 uu____5193  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5191  in
        FStar_Pprint.op_Hat_Hat uu____5188 uu____5190
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Main uu____5208 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5210,uu____5211) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5227 = str "%splice"  in
        let uu____5229 =
          let uu____5230 =
            let uu____5231 = str ";"  in p_list p_uident uu____5231 ids  in
          let uu____5233 =
            let uu____5234 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5234  in
          FStar_Pprint.op_Hat_Hat uu____5230 uu____5233  in
        FStar_Pprint.op_Hat_Hat uu____5227 uu____5229

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5237  ->
    match uu___5_5237 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5240 = str "#set-options"  in
        let uu____5242 =
          let uu____5243 =
            let uu____5244 = str s  in FStar_Pprint.dquotes uu____5244  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5243  in
        FStar_Pprint.op_Hat_Hat uu____5240 uu____5242
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5249 = str "#reset-options"  in
        let uu____5251 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5257 =
                 let uu____5258 = str s  in FStar_Pprint.dquotes uu____5258
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5257) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5249 uu____5251
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5263 = str "#push-options"  in
        let uu____5265 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5271 =
                 let uu____5272 = str s  in FStar_Pprint.dquotes uu____5272
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5271) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5263 uu____5265
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
      let uu____5305 = p_typeDecl kw typedecl  in
      match uu____5305 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5328 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5328
          else
            (let uu____5331 =
               let uu____5332 =
                 let uu____5333 =
                   let uu____5334 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5334 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5333  in
               let uu____5335 =
                 let uu____5336 =
                   let uu____5337 =
                     let uu____5338 =
                       let uu____5339 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5339  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5338
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5337  in
                 FStar_Pprint.op_Hat_Hat decl uu____5336  in
               FStar_Pprint.ifflat uu____5332 uu____5335  in
             FStar_All.pipe_left FStar_Pprint.group uu____5331)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5342  ->
      match uu___6_5342 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5365 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5365, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5382 = p_typ_sep false false t  in
          (match uu____5382 with
           | (comm,doc) ->
               let uu____5402 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5402, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5446 =
            match uu____5446 with
            | (lid1,t) ->
                let uu____5454 =
                  let uu____5459 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5459
                   in
                (match uu____5454 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5471 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5471  in
          let uu____5476 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5476, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5531 =
            match uu____5531 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5551 =
                    let uu____5552 = FStar_Ident.range_of_id uid  in
                    let uu____5553 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uu____5552 uu____5553  in
                  FStar_Range.extend_to_end_of_line uu____5551  in
                let uu____5558 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5558 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5587 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5587, datacon_doc, jump2)

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
                let uu____5615 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5615  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5622 =
                    let uu____5623 =
                      let uu____5624 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5624 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5623  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5622
               in
            if bs = []
            then with_kw (fun n  -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n  ->
                    let uu____5644 =
                      let uu____5645 = FStar_Pprint.flow break1 binders  in
                      prefix2 n uu____5645  in
                    prefix2 uu____5644 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5647  ->
      match uu____5647 with
      | (lid,t) ->
          let uu____5655 =
            let uu____5656 = p_lident lid  in
            let uu____5657 =
              let uu____5658 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5658  in
            FStar_Pprint.op_Hat_Hat uu____5656 uu____5657  in
          FStar_Pprint.group uu____5655

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5660  ->
    match uu____5660 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5685 =
            let uu____5686 =
              let uu____5687 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5687  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5686  in
          FStar_Pprint.group uu____5685  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5691 =
               let uu____5692 =
                 let uu____5693 =
                   let uu____5694 =
                     let uu____5695 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5695
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5694  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5693  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5692  in
             FStar_Pprint.group uu____5691) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5699  ->
      fun inner_let  ->
        match uu____5699 with
        | (pat,uu____5707) ->
            let uu____5708 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5760 =
                    let uu____5767 =
                      let uu____5772 =
                        let uu____5773 =
                          let uu____5774 =
                            let uu____5775 = str "by"  in
                            let uu____5777 =
                              let uu____5778 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5778
                               in
                            FStar_Pprint.op_Hat_Hat uu____5775 uu____5777  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5774
                           in
                        FStar_Pprint.group uu____5773  in
                      (t, uu____5772)  in
                    FStar_Pervasives_Native.Some uu____5767  in
                  (pat1, uu____5760)
              | uu____5789 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5708 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5815);
                         FStar_Parser_AST.prange = uu____5816;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5833 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5833 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5839 =
                        if inner_let
                        then
                          let uu____5853 = pats_as_binders_if_possible pats
                             in
                          match uu____5853 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5876 = pats_as_binders_if_possible pats
                              in
                           match uu____5876 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5839 with
                       | (terms,style) ->
                           let uu____5903 =
                             let uu____5904 =
                               let uu____5905 =
                                 let uu____5906 = p_lident lid  in
                                 let uu____5907 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5906
                                   uu____5907
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5905
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5904  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5903)
                  | uu____5910 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5918 =
                              let uu____5919 =
                                let uu____5920 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5920
                                 in
                              FStar_Pprint.group uu____5919  in
                            FStar_Pprint.op_Hat_Hat uu____5918 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5931 =
                        let uu____5932 =
                          let uu____5933 =
                            let uu____5934 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5934  in
                          FStar_Pprint.group uu____5933  in
                        FStar_Pprint.op_Hat_Hat uu____5932 ascr_doc  in
                      FStar_Pprint.group uu____5931))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5936  ->
      match uu____5936 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5945 = p_term_sep false false e  in
          (match uu____5945 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5955 =
                 let uu____5956 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5956  in
               let uu____5957 =
                 let uu____5958 =
                   let uu____5959 =
                     let uu____5960 =
                       let uu____5961 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5961
                        in
                     FStar_Pprint.group uu____5960  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5959  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5958  in
               FStar_Pprint.ifflat uu____5955 uu____5957)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5962  ->
    match uu___7_5962 with
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
        let uu____5987 = p_uident uid  in
        let uu____5988 = p_binders true bs  in
        let uu____5990 =
          let uu____5991 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5991  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5987
          uu____5988 uu____5990

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
          let uu____6006 =
            let uu____6007 =
              let uu____6008 =
                let uu____6009 = p_uident uid  in
                let uu____6010 = p_binders true bs  in
                let uu____6012 =
                  let uu____6013 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6013  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6009 uu____6010 uu____6012
                 in
              FStar_Pprint.group uu____6008  in
            let uu____6018 =
              let uu____6019 = str "with"  in
              let uu____6021 =
                let uu____6022 =
                  let uu____6023 =
                    let uu____6024 =
                      let uu____6025 =
                        let uu____6026 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6026
                         in
                      separate_map_last uu____6025 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6024  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6023  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6022  in
              FStar_Pprint.op_Hat_Hat uu____6019 uu____6021  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6007 uu____6018  in
          braces_with_nesting uu____6006

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____6030,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6043 =
            let uu____6044 = p_lident lid  in
            let uu____6045 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6044 uu____6045  in
          let uu____6046 = p_simpleTerm ps false e  in
          prefix2 uu____6043 uu____6046
      | uu____6048 ->
          let uu____6049 =
            let uu____6051 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6051
             in
          failwith uu____6049

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6134 =
        match uu____6134 with
        | (kwd,t) ->
            let uu____6145 =
              let uu____6146 = str kwd  in
              let uu____6147 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6146 uu____6147  in
            let uu____6148 = p_simpleTerm ps false t  in
            prefix2 uu____6145 uu____6148
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6155 =
      let uu____6156 =
        let uu____6157 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6158 =
          let uu____6159 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6159  in
        FStar_Pprint.op_Hat_Hat uu____6157 uu____6158  in
      let uu____6161 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6156 uu____6161  in
    let uu____6162 =
      let uu____6163 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6163  in
    FStar_Pprint.op_Hat_Hat uu____6155 uu____6162

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6164  ->
    match uu___8_6164 with
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
        let uu____6184 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6184 FStar_Pprint.hardline
    | uu____6185 ->
        let uu____6186 =
          let uu____6187 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6187  in
        FStar_Pprint.op_Hat_Hat uu____6186 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6190  ->
    match uu___9_6190 with
    | FStar_Parser_AST.Rec  ->
        let uu____6191 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6191
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6193  ->
    match uu___10_6193 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6198,e) -> e
          | uu____6204 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6205 = str "#["  in
        let uu____6207 =
          let uu____6208 = p_term false false t1  in
          let uu____6211 =
            let uu____6212 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6212 break1  in
          FStar_Pprint.op_Hat_Hat uu____6208 uu____6211  in
        FStar_Pprint.op_Hat_Hat uu____6205 uu____6207

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6218 =
          let uu____6219 =
            let uu____6220 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6220  in
          FStar_Pprint.separate_map uu____6219 p_tuplePattern pats  in
        FStar_Pprint.group uu____6218
    | uu____6221 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6230 =
          let uu____6231 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6231 p_constructorPattern pats  in
        FStar_Pprint.group uu____6230
    | uu____6232 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6235;_},hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6240 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6241 = p_constructorPattern hd  in
        let uu____6242 = p_constructorPattern tl  in
        infix0 uu____6240 uu____6241 uu____6242
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6244;_},pats)
        ->
        let uu____6250 = p_quident uid  in
        let uu____6251 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6250 uu____6251
    | uu____6252 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6268;
               FStar_Parser_AST.blevel = uu____6269;
               FStar_Parser_AST.aqual = uu____6270;_},phi))
             when
             let uu____6278 = FStar_Ident.text_of_id lid  in
             let uu____6280 = FStar_Ident.text_of_id lid'  in
             uu____6278 = uu____6280 ->
             let uu____6283 =
               let uu____6284 = p_ident lid  in
               p_refinement aqual uu____6284 t1 phi  in
             soft_parens_with_nesting uu____6283
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6287;
               FStar_Parser_AST.blevel = uu____6288;
               FStar_Parser_AST.aqual = uu____6289;_},phi))
             ->
             let uu____6295 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6295
         | uu____6296 ->
             let uu____6301 =
               let uu____6302 = p_tuplePattern pat  in
               let uu____6303 =
                 let uu____6304 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6304
                  in
               FStar_Pprint.op_Hat_Hat uu____6302 uu____6303  in
             soft_parens_with_nesting uu____6301)
    | FStar_Parser_AST.PatList pats ->
        let uu____6308 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6308 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6327 =
          match uu____6327 with
          | (lid,pat) ->
              let uu____6334 = p_qlident lid  in
              let uu____6335 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6334 uu____6335
           in
        let uu____6336 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6336
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6348 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6349 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6350 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6348
          uu____6349 uu____6350
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6361 =
          let uu____6362 =
            let uu____6363 =
              let uu____6364 = FStar_Ident.text_of_id op  in str uu____6364
               in
            let uu____6366 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6363 uu____6366  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6362  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6361
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6370 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6370 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6378 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6379 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6378 uu____6379
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6381 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6385;
           FStar_Parser_AST.prange = uu____6386;_},uu____6387)
        ->
        let uu____6392 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6392
    | FStar_Parser_AST.PatTuple (uu____6393,false ) ->
        let uu____6400 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6400
    | uu____6401 ->
        let uu____6402 =
          let uu____6404 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6404  in
        failwith uu____6402

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,uu____6410) when
        let uu____6415 = FStar_Ident.text_of_id id  in uu____6415 = "*" ->
        true
    | uu____6420 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6426) -> true
    | uu____6428 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6435 = p_binder' is_atomic b  in
      match uu____6435 with
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
          let uu____6472 =
            let uu____6473 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6474 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6473 uu____6474  in
          (uu____6472, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6480 = p_lident lid  in
          (uu____6480, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6487 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6498;
                   FStar_Parser_AST.blevel = uu____6499;
                   FStar_Parser_AST.aqual = uu____6500;_},phi)
                when
                let uu____6504 = FStar_Ident.text_of_id lid  in
                let uu____6506 = FStar_Ident.text_of_id lid'  in
                uu____6504 = uu____6506 ->
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
          (match uu____6487 with
           | (b',t') ->
               let catf1 =
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
               (b', (FStar_Pervasives_Native.Some t'), catf1))
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
      (let uu____6744 = FStar_Ident.text_of_id lid  in
       FStar_Util.starts_with uu____6744 FStar_Ident.reserved_prefix) &&
        (let uu____6747 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6747)
       in
    if uu____6740
    then FStar_Pprint.underscore
    else (let uu____6752 = FStar_Ident.text_of_id lid  in str uu____6752)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6755 =
      (let uu____6759 =
         let uu____6761 = FStar_Ident.ident_of_lid lid  in
         FStar_Ident.text_of_id uu____6761  in
       FStar_Util.starts_with uu____6759 FStar_Ident.reserved_prefix) &&
        (let uu____6763 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6763)
       in
    if uu____6755
    then FStar_Pprint.underscore
    else (let uu____6768 = FStar_Ident.string_of_lid lid  in str uu____6768)

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
          let uu____6789 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6789
        else
          (let uu____6792 =
             let uu____6793 =
               let uu____6794 =
                 let uu____6795 =
                   let uu____6796 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6796  in
                 FStar_Pprint.op_Hat_Hat doc uu____6795  in
               FStar_Pprint.group uu____6794  in
             let uu____6797 =
               let uu____6798 =
                 let uu____6799 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6799  in
               FStar_Pprint.op_Hat_Hat comm uu____6798  in
             FStar_Pprint.ifflat uu____6793 uu____6797  in
           FStar_All.pipe_left FStar_Pprint.group uu____6792)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6807 = p_noSeqTerm true false e1  in
            (match uu____6807 with
             | (comm,t1) ->
                 let uu____6816 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6817 =
                   let uu____6818 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6818
                    in
                 FStar_Pprint.op_Hat_Hat uu____6816 uu____6817)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6822 =
              let uu____6823 =
                let uu____6824 =
                  let uu____6825 = p_lident x  in
                  let uu____6826 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6825 uu____6826  in
                let uu____6827 =
                  let uu____6828 = p_noSeqTermAndComment true false e1  in
                  let uu____6831 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6828 uu____6831  in
                op_Hat_Slash_Plus_Hat uu____6824 uu____6827  in
              FStar_Pprint.group uu____6823  in
            let uu____6832 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6822 uu____6832
        | uu____6833 ->
            let uu____6834 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6834

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
            let uu____6846 = p_noSeqTerm true false e1  in
            (match uu____6846 with
             | (comm,t1) ->
                 let uu____6859 =
                   let uu____6860 =
                     let uu____6861 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6861  in
                   let uu____6862 =
                     let uu____6863 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6863
                      in
                   FStar_Pprint.op_Hat_Hat uu____6860 uu____6862  in
                 (comm, uu____6859))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6867 =
              let uu____6868 =
                let uu____6869 =
                  let uu____6870 =
                    let uu____6871 = p_lident x  in
                    let uu____6872 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6871 uu____6872  in
                  let uu____6873 =
                    let uu____6874 = p_noSeqTermAndComment true false e1  in
                    let uu____6877 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6874 uu____6877  in
                  op_Hat_Slash_Plus_Hat uu____6870 uu____6873  in
                FStar_Pprint.group uu____6869  in
              let uu____6878 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6868 uu____6878  in
            (FStar_Pprint.empty, uu____6867)
        | uu____6879 -> p_noSeqTerm ps pb e

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
            let uu____6899 =
              let uu____6900 = p_tmIff e1  in
              let uu____6901 =
                let uu____6902 =
                  let uu____6903 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6903
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6902  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6900 uu____6901  in
            FStar_Pprint.group uu____6899
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6909 =
              let uu____6910 = p_tmIff e1  in
              let uu____6911 =
                let uu____6912 =
                  let uu____6913 =
                    let uu____6914 = p_typ false false t  in
                    let uu____6917 =
                      let uu____6918 = str "by"  in
                      let uu____6920 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6918 uu____6920  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6914 uu____6917  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6913
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6912  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6910 uu____6911  in
            FStar_Pprint.group uu____6909
        | FStar_Parser_AST.Op (id,e1::e2::e3::[]) when
            let uu____6927 = FStar_Ident.text_of_id id  in
            uu____6927 = ".()<-" ->
            let uu____6931 =
              let uu____6932 =
                let uu____6933 =
                  let uu____6934 = p_atomicTermNotQUident e1  in
                  let uu____6935 =
                    let uu____6936 =
                      let uu____6937 =
                        let uu____6938 = p_term false false e2  in
                        soft_parens_with_nesting uu____6938  in
                      let uu____6941 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6937 uu____6941  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6936  in
                  FStar_Pprint.op_Hat_Hat uu____6934 uu____6935  in
                FStar_Pprint.group uu____6933  in
              let uu____6942 =
                let uu____6943 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6943  in
              FStar_Pprint.op_Hat_Hat uu____6932 uu____6942  in
            FStar_Pprint.group uu____6931
        | FStar_Parser_AST.Op (id,e1::e2::e3::[]) when
            let uu____6950 = FStar_Ident.text_of_id id  in
            uu____6950 = ".[]<-" ->
            let uu____6954 =
              let uu____6955 =
                let uu____6956 =
                  let uu____6957 = p_atomicTermNotQUident e1  in
                  let uu____6958 =
                    let uu____6959 =
                      let uu____6960 =
                        let uu____6961 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6961  in
                      let uu____6964 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6960 uu____6964  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6959  in
                  FStar_Pprint.op_Hat_Hat uu____6957 uu____6958  in
                FStar_Pprint.group uu____6956  in
              let uu____6965 =
                let uu____6966 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6966  in
              FStar_Pprint.op_Hat_Hat uu____6955 uu____6965  in
            FStar_Pprint.group uu____6954
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6976 =
              let uu____6977 = str "requires"  in
              let uu____6979 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6977 uu____6979  in
            FStar_Pprint.group uu____6976
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6989 =
              let uu____6990 = str "ensures"  in
              let uu____6992 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6990 uu____6992  in
            FStar_Pprint.group uu____6989
        | FStar_Parser_AST.Attributes es ->
            let uu____6996 =
              let uu____6997 = str "attributes"  in
              let uu____6999 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6997 uu____6999  in
            FStar_Pprint.group uu____6996
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7004 =
                let uu____7005 =
                  let uu____7006 = str "if"  in
                  let uu____7008 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7006 uu____7008  in
                let uu____7011 =
                  let uu____7012 = str "then"  in
                  let uu____7014 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7012 uu____7014  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7005 uu____7011  in
              FStar_Pprint.group uu____7004
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7018,uu____7019,e31) when
                     is_unit e31 ->
                     let uu____7021 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7021
                 | uu____7024 -> p_noSeqTermAndComment false false e2  in
               let uu____7027 =
                 let uu____7028 =
                   let uu____7029 = str "if"  in
                   let uu____7031 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7029 uu____7031  in
                 let uu____7034 =
                   let uu____7035 =
                     let uu____7036 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7036 e2_doc  in
                   let uu____7038 =
                     let uu____7039 = str "else"  in
                     let uu____7041 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7039 uu____7041  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7035 uu____7038  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7028 uu____7034  in
               FStar_Pprint.group uu____7027)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7064 =
              let uu____7065 =
                let uu____7066 =
                  let uu____7067 = str "try"  in
                  let uu____7069 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7067 uu____7069  in
                let uu____7072 =
                  let uu____7073 = str "with"  in
                  let uu____7075 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7073 uu____7075  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7066 uu____7072  in
              FStar_Pprint.group uu____7065  in
            let uu____7084 = paren_if (ps || pb)  in uu____7084 uu____7064
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7111 =
              let uu____7112 =
                let uu____7113 =
                  let uu____7114 = str "match"  in
                  let uu____7116 = p_noSeqTermAndComment false false e1  in
                  let uu____7119 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7114 uu____7116 uu____7119
                   in
                let uu____7123 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7113 uu____7123  in
              FStar_Pprint.group uu____7112  in
            let uu____7132 = paren_if (ps || pb)  in uu____7132 uu____7111
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7139 =
              let uu____7140 =
                let uu____7141 =
                  let uu____7142 = str "let open"  in
                  let uu____7144 = p_quident uid  in
                  let uu____7145 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7142 uu____7144 uu____7145
                   in
                let uu____7149 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7141 uu____7149  in
              FStar_Pprint.group uu____7140  in
            let uu____7151 = paren_if ps  in uu____7151 uu____7139
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7216 is_last =
              match uu____7216 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7250 =
                          let uu____7251 = str "let"  in
                          let uu____7253 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7251 uu____7253
                           in
                        FStar_Pprint.group uu____7250
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7256 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7262 = p_term_sep false false e2  in
                  (match uu____7262 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7272 =
                         if is_last
                         then
                           let uu____7274 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7275 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7274 doc_expr1 uu____7275
                         else
                           (let uu____7281 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7281)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7272)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7332 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7332
                     else
                       (let uu____7337 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7337)) lbs
               in
            let lbs_doc =
              let uu____7341 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7341  in
            let uu____7342 =
              let uu____7343 =
                let uu____7344 =
                  let uu____7345 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7345
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7344  in
              FStar_Pprint.group uu____7343  in
            let uu____7347 = paren_if ps  in uu____7347 uu____7342
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7354;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7357;
                                                             FStar_Parser_AST.level
                                                               = uu____7358;_})
            when matches_var maybe_x x ->
            let uu____7385 =
              let uu____7386 =
                let uu____7387 = str "function"  in
                let uu____7389 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7387 uu____7389  in
              FStar_Pprint.group uu____7386  in
            let uu____7398 = paren_if (ps || pb)  in uu____7398 uu____7385
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7404 =
              let uu____7405 = str "quote"  in
              let uu____7407 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7405 uu____7407  in
            FStar_Pprint.group uu____7404
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7409 =
              let uu____7410 = str "`"  in
              let uu____7412 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7410 uu____7412  in
            FStar_Pprint.group uu____7409
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7414 =
              let uu____7415 = str "`%"  in
              let uu____7417 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7415 uu____7417  in
            FStar_Pprint.group uu____7414
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7419;
              FStar_Parser_AST.level = uu____7420;_}
            ->
            let uu____7421 =
              let uu____7422 = str "`@"  in
              let uu____7424 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7422 uu____7424  in
            FStar_Pprint.group uu____7421
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7426 =
              let uu____7427 = str "`#"  in
              let uu____7429 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7427 uu____7429  in
            FStar_Pprint.group uu____7426
        | FStar_Parser_AST.CalcProof (rel,init,steps) ->
            let head =
              let uu____7438 = str "calc"  in
              let uu____7440 =
                let uu____7441 =
                  let uu____7442 = p_noSeqTermAndComment false false rel  in
                  let uu____7445 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7442 uu____7445  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7441  in
              FStar_Pprint.op_Hat_Hat uu____7438 uu____7440  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7447 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7448 =
              let uu____7449 =
                let uu____7450 =
                  let uu____7451 = p_noSeqTermAndComment false false init  in
                  let uu____7454 =
                    let uu____7455 = str ";"  in
                    let uu____7457 =
                      let uu____7458 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7458
                       in
                    FStar_Pprint.op_Hat_Hat uu____7455 uu____7457  in
                  FStar_Pprint.op_Hat_Hat uu____7451 uu____7454  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7450  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7449
               in
            FStar_Pprint.enclose head uu____7447 uu____7448
        | uu____7460 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7461  ->
    fun uu____7462  ->
      match uu____7462 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7467 =
            let uu____7468 = p_noSeqTermAndComment false false rel  in
            let uu____7471 =
              let uu____7472 =
                let uu____7473 =
                  let uu____7474 =
                    let uu____7475 = p_noSeqTermAndComment false false just
                       in
                    let uu____7478 =
                      let uu____7479 =
                        let uu____7480 =
                          let uu____7481 =
                            let uu____7482 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7485 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7482 uu____7485  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7481
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7480
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7479
                       in
                    FStar_Pprint.op_Hat_Hat uu____7475 uu____7478  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7474  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7473  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7472  in
            FStar_Pprint.op_Hat_Hat uu____7468 uu____7471  in
          FStar_Pprint.group uu____7467

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7487  ->
    match uu___11_7487 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7499 =
          let uu____7500 = str "[@"  in
          let uu____7502 =
            let uu____7503 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7504 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7503 uu____7504  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7500 uu____7502  in
        FStar_Pprint.group uu____7499

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
        | FStar_Parser_AST.QForall (bs,(uu____7522,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7556 =
                   let uu____7557 =
                     let uu____7558 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7558 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7557 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7556 term_doc
             | pats ->
                 let uu____7566 =
                   let uu____7567 =
                     let uu____7568 =
                       let uu____7569 =
                         let uu____7570 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7570
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7569 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7573 = p_trigger trigger  in
                     prefix2 uu____7568 uu____7573  in
                   FStar_Pprint.group uu____7567  in
                 prefix2 uu____7566 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7575,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7609 =
                   let uu____7610 =
                     let uu____7611 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7611 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7610 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7609 term_doc
             | pats ->
                 let uu____7619 =
                   let uu____7620 =
                     let uu____7621 =
                       let uu____7622 =
                         let uu____7623 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7623
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7622 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7626 = p_trigger trigger  in
                     prefix2 uu____7621 uu____7626  in
                   FStar_Pprint.group uu____7620  in
                 prefix2 uu____7619 term_doc)
        | uu____7627 -> p_simpleTerm ps pb e

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
      let uu____7648 = all_binders_annot t  in
      if uu____7648
      then
        let uu____7651 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7651
      else
        (let uu____7662 =
           let uu____7663 =
             let uu____7664 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7664  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7663  in
         FStar_Pprint.group uu____7662)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7723 = x  in
      match uu____7723 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu____7788 = hd  in
               (match uu____7788 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl))
       in
    let p_collapsed_binder cb =
      let uu____7860 = cb  in
      match uu____7860 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu____7879 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7885 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7885) hd tl
                  in
               cat_with_colon uu____7879 typ)
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
                 FStar_Parser_AST.brange = uu____7964;
                 FStar_Parser_AST.blevel = uu____7965;
                 FStar_Parser_AST.aqual = uu____7966;_},phi))
               when
               let uu____7974 = FStar_Ident.text_of_id lid  in
               let uu____7976 = FStar_Ident.text_of_id lid'  in
               uu____7974 = uu____7976 ->
               let uu____7979 =
                 let uu____7984 = p_ident lid  in
                 p_refinement' aqual uu____7984 t1 phi  in
               FStar_Pervasives_Native.Some uu____7979
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7991) ->
               let uu____7996 =
                 let uu____8001 =
                   let uu____8002 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8003 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8002 uu____8003  in
                 let uu____8004 = p_tmEqNoRefinement t  in
                 (uu____8001, uu____8004)  in
               FStar_Pervasives_Native.Some uu____7996
           | uu____8009 -> FStar_Pervasives_Native.None)
      | uu____8018 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8031 -> false
      | uu____8043 -> true  in
    let uu____8045 = map_if_all all_binders pats  in
    match uu____8045 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8077 = collapse_pats bs  in
        (uu____8077, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8094 = FStar_List.map p_atomicPattern pats  in
        (uu____8094, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8106 -> str "forall"
    | FStar_Parser_AST.QExists uu____8126 -> str "exists"
    | uu____8146 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8148  ->
    match uu___12_8148 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8160 =
          let uu____8161 =
            let uu____8162 =
              let uu____8163 = str "pattern"  in
              let uu____8165 =
                let uu____8166 =
                  let uu____8167 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8167
                   in
                FStar_Pprint.op_Hat_Hat uu____8166 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8163 uu____8165  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8162  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8161  in
        FStar_Pprint.group uu____8160

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8175 = str "\\/"  in
    FStar_Pprint.separate_map uu____8175 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8182 =
      let uu____8183 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8183 p_appTerm pats  in
    FStar_Pprint.group uu____8182

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8195 = p_term_sep false pb e1  in
            (match uu____8195 with
             | (comm,doc) ->
                 let prefix =
                   let uu____8204 = str "fun"  in
                   let uu____8206 =
                     let uu____8207 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8207
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8204 uu____8206  in
                 let uu____8208 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8210 =
                       let uu____8211 =
                         let uu____8212 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8212  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8211
                        in
                     FStar_Pprint.op_Hat_Hat prefix uu____8210
                   else
                     (let uu____8215 = op_Hat_Slash_Plus_Hat prefix doc  in
                      FStar_Pprint.group uu____8215)
                    in
                 let uu____8216 = paren_if ps  in uu____8216 uu____8208)
        | uu____8221 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8229  ->
      match uu____8229 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8253 =
                    let uu____8254 =
                      let uu____8255 =
                        let uu____8256 = p_tuplePattern p  in
                        let uu____8257 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8256 uu____8257  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8255
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8254  in
                  FStar_Pprint.group uu____8253
              | FStar_Pervasives_Native.Some f ->
                  let uu____8259 =
                    let uu____8260 =
                      let uu____8261 =
                        let uu____8262 =
                          let uu____8263 =
                            let uu____8264 = p_tuplePattern p  in
                            let uu____8265 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8264
                              uu____8265
                             in
                          FStar_Pprint.group uu____8263  in
                        let uu____8267 =
                          let uu____8268 =
                            let uu____8271 = p_tmFormula f  in
                            [uu____8271; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8268  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8262 uu____8267
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8261
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8260  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8259
               in
            let uu____8273 = p_term_sep false pb e  in
            match uu____8273 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8283 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8283
                   else
                     (let uu____8286 =
                        let uu____8287 =
                          let uu____8288 =
                            let uu____8289 =
                              let uu____8290 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8290  in
                            op_Hat_Slash_Plus_Hat branch uu____8289  in
                          FStar_Pprint.group uu____8288  in
                        let uu____8291 =
                          let uu____8292 =
                            let uu____8293 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8293  in
                          FStar_Pprint.op_Hat_Hat branch uu____8292  in
                        FStar_Pprint.ifflat uu____8287 uu____8291  in
                      FStar_Pprint.group uu____8286))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8297 =
                       let uu____8298 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8298  in
                     op_Hat_Slash_Plus_Hat branch uu____8297)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd  in
                    let uu____8309 =
                      let uu____8310 =
                        let uu____8311 =
                          let uu____8312 =
                            let uu____8313 =
                              let uu____8314 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8314  in
                            FStar_Pprint.separate_map uu____8313
                              p_tuplePattern (FStar_List.rev tl)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8312
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8311
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8310  in
                    FStar_Pprint.group uu____8309
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8316 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____8323 = FStar_Ident.text_of_id id  in uu____8323 = "<==>" ->
        let uu____8327 = str "<==>"  in
        let uu____8329 = p_tmImplies e1  in
        let uu____8330 = p_tmIff e2  in
        infix0 uu____8327 uu____8329 uu____8330
    | uu____8331 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____8338 = FStar_Ident.text_of_id id  in uu____8338 = "==>" ->
        let uu____8342 = str "==>"  in
        let uu____8344 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8350 = p_tmImplies e2  in
        infix0 uu____8342 uu____8344 uu____8350
    | uu____8351 ->
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
          let uu____8365 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8365 with
          | (terms',last) ->
              let uu____8385 =
                match style with
                | Arrows (n,ln) ->
                    let uu____8420 =
                      let uu____8421 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8421
                       in
                    let uu____8422 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n, ln, terms', uu____8420, uu____8422)
                | Binders (n,ln,parens) ->
                    let uu____8436 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8444 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n, ln, uu____8436, break1, uu____8444)
                 in
              (match uu____8385 with
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
                    | uu____8477 when uu____8477 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu____8478 ->
                        let uu____8479 =
                          let uu____8480 =
                            let uu____8481 =
                              let uu____8482 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8483 =
                                let uu____8484 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8484
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8482 uu____8483
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8481  in
                          let uu____8485 =
                            let uu____8486 =
                              let uu____8487 =
                                let uu____8488 =
                                  let uu____8489 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8489  in
                                let uu____8490 =
                                  let uu____8491 =
                                    let uu____8492 =
                                      let uu____8493 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8494 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8500 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8500)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8493
                                        uu____8494
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8492
                                     in
                                  jump2 uu____8491  in
                                FStar_Pprint.ifflat uu____8488 uu____8490  in
                              FStar_Pprint.group uu____8487  in
                            let uu____8502 =
                              let uu____8503 =
                                let uu____8504 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.hang last_n uu____8504  in
                              FStar_Pprint.align uu____8503  in
                            FStar_Pprint.prefix n Prims.int_one uu____8486
                              uu____8502
                             in
                          FStar_Pprint.ifflat uu____8480 uu____8485  in
                        FStar_Pprint.group uu____8479))

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
            | Arrows uu____8518 -> p_tmArrow' p_Tm e
            | Binders uu____8525 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8548 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8554 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8548 uu____8554
      | uu____8557 -> let uu____8558 = p_Tm e  in [uu____8558]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8611 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8637 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8611 uu____8637
        | uu____8660 ->
            let uu____8661 =
              let uu____8672 = p_Tm1 e1  in
              (uu____8672, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8661]
         in
      let fold_fun bs x =
        let uu____8770 = x  in
        match uu____8770 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu____8902 = hd  in
                 (match uu____8902 with
                  | (b2s,t2,uu____8931) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu____9033 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9090 = cb  in
        match uu____9090 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9119 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu____9130 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9136 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9136) hd tl
                         in
                      f uu____9130 typ))
         in
      let binders =
        let uu____9152 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9152  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9215 =
        let uu____9216 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9216 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9215  in
    let disj =
      let uu____9219 =
        let uu____9220 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9220 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9219  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____9245 = FStar_Ident.text_of_id id  in uu____9245 = "\\/" ->
        let uu____9249 = p_tmDisjunction e1  in
        let uu____9254 = let uu____9259 = p_tmConjunction e2  in [uu____9259]
           in
        FStar_List.append uu____9249 uu____9254
    | uu____9268 -> let uu____9269 = p_tmConjunction e  in [uu____9269]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____9284 = FStar_Ident.text_of_id id  in uu____9284 = "/\\" ->
        let uu____9288 = p_tmConjunction e1  in
        let uu____9291 = let uu____9294 = p_tmTuple e2  in [uu____9294]  in
        FStar_List.append uu____9288 uu____9291
    | uu____9295 -> let uu____9296 = p_tmTuple e  in [uu____9296]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9313 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9313
          (fun uu____9321  ->
             match uu____9321 with | (e1,uu____9327) -> p_tmEq e1) args
    | uu____9328 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9337 =
             let uu____9338 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9338  in
           FStar_Pprint.group uu____9337)

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
            ((is_operatorInfix0ad12 op) ||
               (let uu____9357 = FStar_Ident.text_of_id op  in
                uu____9357 = "="))
              ||
              (let uu____9362 = FStar_Ident.text_of_id op  in
               uu____9362 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9368 = levels op1  in
            (match uu____9368 with
             | (left,mine,right) ->
                 let uu____9387 =
                   let uu____9388 = FStar_All.pipe_left str op1  in
                   let uu____9390 = p_tmEqWith' p_X left e1  in
                   let uu____9391 = p_tmEqWith' p_X right e2  in
                   infix0 uu____9388 uu____9390 uu____9391  in
                 paren_if_gt curr mine uu____9387)
        | FStar_Parser_AST.Op (id,e1::e2::[]) when
            let uu____9397 = FStar_Ident.text_of_id id  in uu____9397 = ":="
            ->
            let uu____9401 =
              let uu____9402 = p_tmEqWith p_X e1  in
              let uu____9403 =
                let uu____9404 =
                  let uu____9405 =
                    let uu____9406 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9406  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9405  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9404  in
              FStar_Pprint.op_Hat_Hat uu____9402 uu____9403  in
            FStar_Pprint.group uu____9401
        | FStar_Parser_AST.Op (id,e1::[]) when
            let uu____9411 = FStar_Ident.text_of_id id  in uu____9411 = "-"
            ->
            let uu____9415 = levels "-"  in
            (match uu____9415 with
             | (left,mine,right) ->
                 let uu____9435 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9435)
        | uu____9436 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9484)::(e2,uu____9486)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9506 = is_list e  in Prims.op_Negation uu____9506)
              ->
              let op = "::"  in
              let uu____9511 = levels op  in
              (match uu____9511 with
               | (left,mine,right) ->
                   let uu____9530 =
                     let uu____9531 = str op  in
                     let uu____9532 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9534 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9531 uu____9532 uu____9534  in
                   paren_if_gt curr mine uu____9530)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9553 = levels op  in
              (match uu____9553 with
               | (left,mine,right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9587 = p_binder false b  in
                         let uu____9589 =
                           let uu____9590 =
                             let uu____9591 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9591 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9590
                            in
                         FStar_Pprint.op_Hat_Hat uu____9587 uu____9589
                     | FStar_Util.Inr t ->
                         let uu____9593 = p_tmNoEqWith' false p_X left t  in
                         let uu____9595 =
                           let uu____9596 =
                             let uu____9597 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9597 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9596
                            in
                         FStar_Pprint.op_Hat_Hat uu____9593 uu____9595
                      in
                   let uu____9598 =
                     let uu____9599 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9604 = p_tmNoEqWith' false p_X right res  in
                     FStar_Pprint.op_Hat_Hat uu____9599 uu____9604  in
                   paren_if_gt curr mine uu____9598)
          | FStar_Parser_AST.Op (id,e1::e2::[]) when
              (let uu____9613 = FStar_Ident.text_of_id id  in
               uu____9613 = "*") && (FStar_ST.op_Bang unfold_tuples)
              ->
              let op = "*"  in
              let uu____9641 = levels op  in
              (match uu____9641 with
               | (left,mine,right) ->
                   if inside_tuple
                   then
                     let uu____9661 = str op  in
                     let uu____9662 = p_tmNoEqWith' true p_X left e1  in
                     let uu____9664 = p_tmNoEqWith' true p_X right e2  in
                     infix0 uu____9661 uu____9662 uu____9664
                   else
                     (let uu____9668 =
                        let uu____9669 = str op  in
                        let uu____9670 = p_tmNoEqWith' true p_X left e1  in
                        let uu____9672 = p_tmNoEqWith' true p_X right e2  in
                        infix0 uu____9669 uu____9670 uu____9672  in
                      paren_if_gt curr mine uu____9668))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9681 = levels op1  in
              (match uu____9681 with
               | (left,mine,right) ->
                   let uu____9700 =
                     let uu____9701 = str op1  in
                     let uu____9702 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9704 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9701 uu____9702 uu____9704  in
                   paren_if_gt curr mine uu____9700)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9724 =
                let uu____9725 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9726 =
                  let uu____9727 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9727 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9725 uu____9726  in
              braces_with_nesting uu____9724
          | FStar_Parser_AST.Op (id,e1::[]) when
              let uu____9736 = FStar_Ident.text_of_id id  in uu____9736 = "~"
              ->
              let uu____9740 =
                let uu____9741 = str "~"  in
                let uu____9743 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9741 uu____9743  in
              FStar_Pprint.group uu____9740
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op (id,e1::e2::[]) when
                   let uu____9750 = FStar_Ident.text_of_id id  in
                   uu____9750 = "*" ->
                   let op = "*"  in
                   let uu____9757 = levels op  in
                   (match uu____9757 with
                    | (left,mine,right) ->
                        let uu____9776 =
                          let uu____9777 = str op  in
                          let uu____9778 = p_tmNoEqWith' true p_X left e1  in
                          let uu____9780 = p_tmNoEqWith' true p_X right e2
                             in
                          infix0 uu____9777 uu____9778 uu____9780  in
                        paren_if_gt curr mine uu____9776)
               | uu____9782 -> p_X e)
          | uu____9783 -> p_X e

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
        let uu____9790 =
          let uu____9791 = p_lident lid  in
          let uu____9792 =
            let uu____9793 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9793  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9791 uu____9792  in
        FStar_Pprint.group uu____9790
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9796 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9798 = p_appTerm e  in
    let uu____9799 =
      let uu____9800 =
        let uu____9801 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9801 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9800  in
    FStar_Pprint.op_Hat_Hat uu____9798 uu____9799

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9807 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9807 t phi
      | FStar_Parser_AST.TAnnotated uu____9808 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9814 ->
          let uu____9815 =
            let uu____9817 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9817
             in
          failwith uu____9815
      | FStar_Parser_AST.TVariable uu____9820 ->
          let uu____9821 =
            let uu____9823 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9823
             in
          failwith uu____9821
      | FStar_Parser_AST.NoName uu____9826 ->
          let uu____9827 =
            let uu____9829 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9829
             in
          failwith uu____9827

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9833  ->
      match uu____9833 with
      | (lid,e) ->
          let uu____9841 =
            let uu____9842 = p_qlident lid  in
            let uu____9843 =
              let uu____9844 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9844
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9842 uu____9843  in
          FStar_Pprint.group uu____9841

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9847 when is_general_application e ->
        let uu____9854 = head_and_args e  in
        (match uu____9854 with
         | (head,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9901 = p_argTerm e1  in
                  let uu____9902 =
                    let uu____9903 =
                      let uu____9904 =
                        let uu____9905 = str "`"  in
                        let uu____9907 =
                          let uu____9908 = p_indexingTerm head  in
                          let uu____9909 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9908 uu____9909  in
                        FStar_Pprint.op_Hat_Hat uu____9905 uu____9907  in
                      FStar_Pprint.group uu____9904  in
                    let uu____9911 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9903 uu____9911  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9901 uu____9902
              | uu____9912 ->
                  let uu____9919 =
                    let uu____9930 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9930
                    then
                      let uu____9964 =
                        FStar_Util.take
                          (fun uu____9988  ->
                             match uu____9988 with
                             | (uu____9994,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9964 with
                      | (fs_typ_args,args1) ->
                          let uu____10032 =
                            let uu____10033 = p_indexingTerm head  in
                            let uu____10034 =
                              let uu____10035 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10035
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10033 uu____10034
                             in
                          (uu____10032, args1)
                    else
                      (let uu____10050 = p_indexingTerm head  in
                       (uu____10050, args))
                     in
                  (match uu____9919 with
                   | (head_doc,args1) ->
                       let uu____10071 =
                         let uu____10072 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10072 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10071)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10094 =
             (is_dtuple_constructor lid) && (all1_explicit args)  in
           Prims.op_Negation uu____10094)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10113 =
               let uu____10114 = p_quident lid  in
               let uu____10115 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10114 uu____10115  in
             FStar_Pprint.group uu____10113
         | hd::tl ->
             let uu____10132 =
               let uu____10133 =
                 let uu____10134 =
                   let uu____10135 = p_quident lid  in
                   let uu____10136 = p_argTerm hd  in
                   prefix2 uu____10135 uu____10136  in
                 FStar_Pprint.group uu____10134  in
               let uu____10137 =
                 let uu____10138 =
                   FStar_Pprint.separate_map break1 p_argTerm tl  in
                 jump2 uu____10138  in
               FStar_Pprint.op_Hat_Hat uu____10133 uu____10137  in
             FStar_Pprint.group uu____10132)
    | uu____10143 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10154 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10154 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10158 = str "#"  in
        let uu____10160 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10158 uu____10160
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10163 = str "#["  in
        let uu____10165 =
          let uu____10166 = p_indexingTerm t  in
          let uu____10167 =
            let uu____10168 = str "]"  in
            let uu____10170 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10168 uu____10170  in
          FStar_Pprint.op_Hat_Hat uu____10166 uu____10167  in
        FStar_Pprint.op_Hat_Hat uu____10163 uu____10165
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10173  ->
    match uu____10173 with | (e,uu____10179) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (id,e1::e2::[]) when
          let uu____10189 = FStar_Ident.text_of_id id  in uu____10189 = ".()"
          ->
          let uu____10193 =
            let uu____10194 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10195 =
              let uu____10196 =
                let uu____10197 = p_term false false e2  in
                soft_parens_with_nesting uu____10197  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10196  in
            FStar_Pprint.op_Hat_Hat uu____10194 uu____10195  in
          FStar_Pprint.group uu____10193
      | FStar_Parser_AST.Op (id,e1::e2::[]) when
          let uu____10205 = FStar_Ident.text_of_id id  in uu____10205 = ".[]"
          ->
          let uu____10209 =
            let uu____10210 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10211 =
              let uu____10212 =
                let uu____10213 = p_term false false e2  in
                soft_brackets_with_nesting uu____10213  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10212  in
            FStar_Pprint.op_Hat_Hat uu____10210 uu____10211  in
          FStar_Pprint.group uu____10209
      | uu____10216 -> exit e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10221 = p_quident lid  in
        let uu____10222 =
          let uu____10223 =
            let uu____10224 = p_term false false e1  in
            soft_parens_with_nesting uu____10224  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10223  in
        FStar_Pprint.op_Hat_Hat uu____10221 uu____10222
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10232 =
          let uu____10233 = FStar_Ident.text_of_id op  in str uu____10233  in
        let uu____10235 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10232 uu____10235
    | uu____10236 -> p_atomicTermNotQUident e

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
         | uu____10249 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10258 =
          let uu____10259 = FStar_Ident.text_of_id op  in str uu____10259  in
        let uu____10261 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10258 uu____10261
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10265 =
          let uu____10266 =
            let uu____10267 =
              let uu____10268 = FStar_Ident.text_of_id op  in str uu____10268
               in
            let uu____10270 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10267 uu____10270  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10266  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10265
    | FStar_Parser_AST.Construct (lid,args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10285 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____10286 =
          let uu____10287 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____10287
            (fun uu____10295  ->
               match uu____10295 with | (e1,uu____10301) -> p_tmEq e1) args
           in
        let uu____10302 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10285
          uu____10286 uu____10302
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10307 =
          let uu____10308 = p_atomicTermNotQUident e1  in
          let uu____10309 =
            let uu____10310 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10310  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10308
            uu____10309
           in
        FStar_Pprint.group uu____10307
    | uu____10313 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10318 = p_quident constr_lid  in
        let uu____10319 =
          let uu____10320 =
            let uu____10321 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10321  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10320  in
        FStar_Pprint.op_Hat_Hat uu____10318 uu____10319
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10323 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10323 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10325 = p_term_sep false false e1  in
        (match uu____10325 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10338 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10338))
    | uu____10339 when is_array e ->
        let es = extract_from_list e  in
        let uu____10343 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10344 =
          let uu____10345 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10345
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10350 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10343
          uu____10344 uu____10350
    | uu____10353 when is_list e ->
        let uu____10354 =
          let uu____10355 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10356 = extract_from_list e  in
          separate_map_or_flow_last uu____10355
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10356
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10354 FStar_Pprint.rbracket
    | uu____10365 when is_lex_list e ->
        let uu____10366 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10367 =
          let uu____10368 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10369 = extract_from_list e  in
          separate_map_or_flow_last uu____10368
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10369
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10366
          uu____10367 FStar_Pprint.rbracket
    | uu____10378 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10382 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10383 =
          let uu____10384 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10384 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10382
          uu____10383 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10394 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10397 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10394 uu____10397
    | FStar_Parser_AST.Op (op,args) when
        let uu____10406 = handleable_op op args  in
        Prims.op_Negation uu____10406 ->
        let uu____10408 =
          let uu____10410 =
            let uu____10412 = FStar_Ident.text_of_id op  in
            let uu____10414 =
              let uu____10416 =
                let uu____10418 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10418
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10416  in
            Prims.op_Hat uu____10412 uu____10414  in
          Prims.op_Hat "Operation " uu____10410  in
        failwith uu____10408
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10425 = p_term false false e  in
        soft_parens_with_nesting uu____10425
    | FStar_Parser_AST.Const uu____10428 ->
        let uu____10429 = p_term false false e  in
        soft_parens_with_nesting uu____10429
    | FStar_Parser_AST.Op uu____10432 ->
        let uu____10439 = p_term false false e  in
        soft_parens_with_nesting uu____10439
    | FStar_Parser_AST.Tvar uu____10442 ->
        let uu____10443 = p_term false false e  in
        soft_parens_with_nesting uu____10443
    | FStar_Parser_AST.Var uu____10446 ->
        let uu____10447 = p_term false false e  in
        soft_parens_with_nesting uu____10447
    | FStar_Parser_AST.Name uu____10450 ->
        let uu____10451 = p_term false false e  in
        soft_parens_with_nesting uu____10451
    | FStar_Parser_AST.Construct uu____10454 ->
        let uu____10465 = p_term false false e  in
        soft_parens_with_nesting uu____10465
    | FStar_Parser_AST.Abs uu____10468 ->
        let uu____10475 = p_term false false e  in
        soft_parens_with_nesting uu____10475
    | FStar_Parser_AST.App uu____10478 ->
        let uu____10485 = p_term false false e  in
        soft_parens_with_nesting uu____10485
    | FStar_Parser_AST.Let uu____10488 ->
        let uu____10509 = p_term false false e  in
        soft_parens_with_nesting uu____10509
    | FStar_Parser_AST.LetOpen uu____10512 ->
        let uu____10517 = p_term false false e  in
        soft_parens_with_nesting uu____10517
    | FStar_Parser_AST.Seq uu____10520 ->
        let uu____10525 = p_term false false e  in
        soft_parens_with_nesting uu____10525
    | FStar_Parser_AST.Bind uu____10528 ->
        let uu____10535 = p_term false false e  in
        soft_parens_with_nesting uu____10535
    | FStar_Parser_AST.If uu____10538 ->
        let uu____10545 = p_term false false e  in
        soft_parens_with_nesting uu____10545
    | FStar_Parser_AST.Match uu____10548 ->
        let uu____10563 = p_term false false e  in
        soft_parens_with_nesting uu____10563
    | FStar_Parser_AST.TryWith uu____10566 ->
        let uu____10581 = p_term false false e  in
        soft_parens_with_nesting uu____10581
    | FStar_Parser_AST.Ascribed uu____10584 ->
        let uu____10593 = p_term false false e  in
        soft_parens_with_nesting uu____10593
    | FStar_Parser_AST.Record uu____10596 ->
        let uu____10609 = p_term false false e  in
        soft_parens_with_nesting uu____10609
    | FStar_Parser_AST.Project uu____10612 ->
        let uu____10617 = p_term false false e  in
        soft_parens_with_nesting uu____10617
    | FStar_Parser_AST.Product uu____10620 ->
        let uu____10627 = p_term false false e  in
        soft_parens_with_nesting uu____10627
    | FStar_Parser_AST.Sum uu____10630 ->
        let uu____10641 = p_term false false e  in
        soft_parens_with_nesting uu____10641
    | FStar_Parser_AST.QForall uu____10644 ->
        let uu____10663 = p_term false false e  in
        soft_parens_with_nesting uu____10663
    | FStar_Parser_AST.QExists uu____10666 ->
        let uu____10685 = p_term false false e  in
        soft_parens_with_nesting uu____10685
    | FStar_Parser_AST.Refine uu____10688 ->
        let uu____10693 = p_term false false e  in
        soft_parens_with_nesting uu____10693
    | FStar_Parser_AST.NamedTyp uu____10696 ->
        let uu____10701 = p_term false false e  in
        soft_parens_with_nesting uu____10701
    | FStar_Parser_AST.Requires uu____10704 ->
        let uu____10712 = p_term false false e  in
        soft_parens_with_nesting uu____10712
    | FStar_Parser_AST.Ensures uu____10715 ->
        let uu____10723 = p_term false false e  in
        soft_parens_with_nesting uu____10723
    | FStar_Parser_AST.Attributes uu____10726 ->
        let uu____10729 = p_term false false e  in
        soft_parens_with_nesting uu____10729
    | FStar_Parser_AST.Quote uu____10732 ->
        let uu____10737 = p_term false false e  in
        soft_parens_with_nesting uu____10737
    | FStar_Parser_AST.VQuote uu____10740 ->
        let uu____10741 = p_term false false e  in
        soft_parens_with_nesting uu____10741
    | FStar_Parser_AST.Antiquote uu____10744 ->
        let uu____10745 = p_term false false e  in
        soft_parens_with_nesting uu____10745
    | FStar_Parser_AST.CalcProof uu____10748 ->
        let uu____10757 = p_term false false e  in
        soft_parens_with_nesting uu____10757

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10760  ->
    match uu___15_10760 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10772) ->
        let uu____10775 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10775
    | FStar_Const.Const_bytearray (bytes,uu____10777) ->
        let uu____10784 =
          let uu____10785 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10785  in
        let uu____10786 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10784 uu____10786
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10809 =
          match uu___13_10809 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10816 =
          match uu___14_10816 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10831  ->
               match uu____10831 with
               | (s,w) ->
                   let uu____10838 = signedness s  in
                   let uu____10839 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10838 uu____10839)
            sign_width_opt
           in
        let uu____10840 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10840 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10844 = FStar_Range.string_of_range r  in str uu____10844
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10848 = p_quident lid  in
        let uu____10849 =
          let uu____10850 =
            let uu____10851 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10851  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10850  in
        FStar_Pprint.op_Hat_Hat uu____10848 uu____10849

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10854 = str "u#"  in
    let uu____10856 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10854 uu____10856

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,u1::u2::[]) when
        let uu____10863 = FStar_Ident.text_of_id id  in uu____10863 = "+" ->
        let uu____10867 =
          let uu____10868 = p_universeFrom u1  in
          let uu____10869 =
            let uu____10870 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10870  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10868 uu____10869  in
        FStar_Pprint.group uu____10867
    | FStar_Parser_AST.App uu____10871 ->
        let uu____10878 = head_and_args u  in
        (match uu____10878 with
         | (head,args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10904 =
                    let uu____10905 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10906 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10914  ->
                           match uu____10914 with
                           | (u1,uu____10920) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10905 uu____10906  in
                  FStar_Pprint.group uu____10904
              | uu____10921 ->
                  let uu____10922 =
                    let uu____10924 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10924
                     in
                  failwith uu____10922))
    | uu____10927 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu____10953 = FStar_Ident.text_of_id id  in str uu____10953
    | FStar_Parser_AST.Paren u1 ->
        let uu____10956 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10956
    | FStar_Parser_AST.App uu____10957 ->
        let uu____10964 = p_universeFrom u  in
        soft_parens_with_nesting uu____10964
    | FStar_Parser_AST.Op (id,uu____10966::uu____10967::[]) when
        let uu____10970 = FStar_Ident.text_of_id id  in uu____10970 = "+" ->
        let uu____10974 = p_universeFrom u  in
        soft_parens_with_nesting uu____10974
    | uu____10975 ->
        let uu____10976 =
          let uu____10978 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10978
           in
        failwith uu____10976

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
       | FStar_Parser_AST.Module (uu____11067,decls) ->
           let uu____11073 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11073
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11082,decls,uu____11084) ->
           let uu____11091 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11091
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11151  ->
         match uu____11151 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id,uu____11173)) -> false
      | ([],uu____11177) -> false
      | uu____11181 -> true  in
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
        | FStar_Parser_AST.Module (uu____11230,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11236,decls,uu____11238) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11290 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11303;
                 FStar_Parser_AST.quals = uu____11304;
                 FStar_Parser_AST.attrs = uu____11305;_}::uu____11306 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11310 =
                   let uu____11313 =
                     let uu____11316 = FStar_List.tl ds  in d :: uu____11316
                      in
                   d0 :: uu____11313  in
                 (uu____11310, (d0.FStar_Parser_AST.drange))
             | uu____11321 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11290 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11378 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11378 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11487 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11487, comments1))))))
  