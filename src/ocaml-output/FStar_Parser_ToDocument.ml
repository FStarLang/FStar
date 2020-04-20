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
    | FStar_Parser_AST.Tycon (true ,uu____5208,uu____5209) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5225 = str "%splice"  in
        let uu____5227 =
          let uu____5228 =
            let uu____5229 = str ";"  in p_list p_uident uu____5229 ids  in
          let uu____5231 =
            let uu____5232 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5232  in
          FStar_Pprint.op_Hat_Hat uu____5228 uu____5231  in
        FStar_Pprint.op_Hat_Hat uu____5225 uu____5227

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5235  ->
    match uu___5_5235 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5238 = str "#set-options"  in
        let uu____5240 =
          let uu____5241 =
            let uu____5242 = str s  in FStar_Pprint.dquotes uu____5242  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5241  in
        FStar_Pprint.op_Hat_Hat uu____5238 uu____5240
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5247 = str "#reset-options"  in
        let uu____5249 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5255 =
                 let uu____5256 = str s  in FStar_Pprint.dquotes uu____5256
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5255) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5247 uu____5249
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5261 = str "#push-options"  in
        let uu____5263 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5269 =
                 let uu____5270 = str s  in FStar_Pprint.dquotes uu____5270
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5269) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5261 uu____5263
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
      let uu____5303 = p_typeDecl kw typedecl  in
      match uu____5303 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5326 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5326
          else
            (let uu____5329 =
               let uu____5330 =
                 let uu____5331 =
                   let uu____5332 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5332 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5331  in
               let uu____5333 =
                 let uu____5334 =
                   let uu____5335 =
                     let uu____5336 =
                       let uu____5337 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5337  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5336
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5335  in
                 FStar_Pprint.op_Hat_Hat decl uu____5334  in
               FStar_Pprint.ifflat uu____5330 uu____5333  in
             FStar_All.pipe_left FStar_Pprint.group uu____5329)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5340  ->
      match uu___6_5340 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5363 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5363, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5380 = p_typ_sep false false t  in
          (match uu____5380 with
           | (comm,doc) ->
               let uu____5400 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5400, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5444 =
            match uu____5444 with
            | (lid1,t) ->
                let uu____5452 =
                  let uu____5457 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5457
                   in
                (match uu____5452 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5469 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5469  in
          let uu____5474 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5474, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5529 =
            match uu____5529 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5549 =
                    let uu____5550 = FStar_Ident.range_of_id uid  in
                    let uu____5551 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uu____5550 uu____5551  in
                  FStar_Range.extend_to_end_of_line uu____5549  in
                let uu____5556 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5556 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5585 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5585, datacon_doc, jump2)

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
                let uu____5613 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5613  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5620 =
                    let uu____5621 =
                      let uu____5622 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5622 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5621  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5620
               in
            if bs = []
            then with_kw (fun n  -> prefix2 n typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n  ->
                    let uu____5642 =
                      let uu____5643 = FStar_Pprint.flow break1 binders  in
                      prefix2 n uu____5643  in
                    prefix2 uu____5642 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5645  ->
      match uu____5645 with
      | (lid,t) ->
          let uu____5653 =
            let uu____5654 = p_lident lid  in
            let uu____5655 =
              let uu____5656 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5656  in
            FStar_Pprint.op_Hat_Hat uu____5654 uu____5655  in
          FStar_Pprint.group uu____5653

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5658  ->
    match uu____5658 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5683 =
            let uu____5684 =
              let uu____5685 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5685  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5684  in
          FStar_Pprint.group uu____5683  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5689 =
               let uu____5690 =
                 let uu____5691 =
                   let uu____5692 =
                     let uu____5693 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5693
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5692  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5691  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5690  in
             FStar_Pprint.group uu____5689) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5697  ->
      fun inner_let  ->
        match uu____5697 with
        | (pat,uu____5705) ->
            let uu____5706 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5758 =
                    let uu____5765 =
                      let uu____5770 =
                        let uu____5771 =
                          let uu____5772 =
                            let uu____5773 = str "by"  in
                            let uu____5775 =
                              let uu____5776 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5776
                               in
                            FStar_Pprint.op_Hat_Hat uu____5773 uu____5775  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5772
                           in
                        FStar_Pprint.group uu____5771  in
                      (t, uu____5770)  in
                    FStar_Pervasives_Native.Some uu____5765  in
                  (pat1, uu____5758)
              | uu____5787 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5706 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5813);
                         FStar_Parser_AST.prange = uu____5814;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5831 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5831 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5837 =
                        if inner_let
                        then
                          let uu____5851 = pats_as_binders_if_possible pats
                             in
                          match uu____5851 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5874 = pats_as_binders_if_possible pats
                              in
                           match uu____5874 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5837 with
                       | (terms,style) ->
                           let uu____5901 =
                             let uu____5902 =
                               let uu____5903 =
                                 let uu____5904 = p_lident lid  in
                                 let uu____5905 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5904
                                   uu____5905
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5903
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5902  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5901)
                  | uu____5908 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5916 =
                              let uu____5917 =
                                let uu____5918 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5918
                                 in
                              FStar_Pprint.group uu____5917  in
                            FStar_Pprint.op_Hat_Hat uu____5916 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5929 =
                        let uu____5930 =
                          let uu____5931 =
                            let uu____5932 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5932  in
                          FStar_Pprint.group uu____5931  in
                        FStar_Pprint.op_Hat_Hat uu____5930 ascr_doc  in
                      FStar_Pprint.group uu____5929))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5934  ->
      match uu____5934 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5943 = p_term_sep false false e  in
          (match uu____5943 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5953 =
                 let uu____5954 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5954  in
               let uu____5955 =
                 let uu____5956 =
                   let uu____5957 =
                     let uu____5958 =
                       let uu____5959 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5959
                        in
                     FStar_Pprint.group uu____5958  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5957  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5956  in
               FStar_Pprint.ifflat uu____5953 uu____5955)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5960  ->
    match uu___7_5960 with
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
        let uu____5985 = p_uident uid  in
        let uu____5986 = p_binders true bs  in
        let uu____5988 =
          let uu____5989 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5989  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5985
          uu____5986 uu____5988

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
          let uu____6004 =
            let uu____6005 =
              let uu____6006 =
                let uu____6007 = p_uident uid  in
                let uu____6008 = p_binders true bs  in
                let uu____6010 =
                  let uu____6011 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6011  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____6007 uu____6008 uu____6010
                 in
              FStar_Pprint.group uu____6006  in
            let uu____6016 =
              let uu____6017 = str "with"  in
              let uu____6019 =
                let uu____6020 =
                  let uu____6021 =
                    let uu____6022 =
                      let uu____6023 =
                        let uu____6024 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6024
                         in
                      separate_map_last uu____6023 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6022  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6021  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6020  in
              FStar_Pprint.op_Hat_Hat uu____6017 uu____6019  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6005 uu____6016  in
          braces_with_nesting uu____6004

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____6028,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6041 =
            let uu____6042 = p_lident lid  in
            let uu____6043 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6042 uu____6043  in
          let uu____6044 = p_simpleTerm ps false e  in
          prefix2 uu____6041 uu____6044
      | uu____6046 ->
          let uu____6047 =
            let uu____6049 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6049
             in
          failwith uu____6047

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6132 =
        match uu____6132 with
        | (kwd,t) ->
            let uu____6143 =
              let uu____6144 = str kwd  in
              let uu____6145 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6144 uu____6145  in
            let uu____6146 = p_simpleTerm ps false t  in
            prefix2 uu____6143 uu____6146
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6153 =
      let uu____6154 =
        let uu____6155 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6156 =
          let uu____6157 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6157  in
        FStar_Pprint.op_Hat_Hat uu____6155 uu____6156  in
      let uu____6159 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6154 uu____6159  in
    let uu____6160 =
      let uu____6161 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6161  in
    FStar_Pprint.op_Hat_Hat uu____6153 uu____6160

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6162  ->
    match uu___8_6162 with
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
        let uu____6182 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6182 FStar_Pprint.hardline
    | uu____6183 ->
        let uu____6184 =
          let uu____6185 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6185  in
        FStar_Pprint.op_Hat_Hat uu____6184 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6188  ->
    match uu___9_6188 with
    | FStar_Parser_AST.Rec  ->
        let uu____6189 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6189
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6191  ->
    match uu___10_6191 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6196,e) -> e
          | uu____6202 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6203 = str "#["  in
        let uu____6205 =
          let uu____6206 = p_term false false t1  in
          let uu____6209 =
            let uu____6210 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6210 break1  in
          FStar_Pprint.op_Hat_Hat uu____6206 uu____6209  in
        FStar_Pprint.op_Hat_Hat uu____6203 uu____6205

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6216 =
          let uu____6217 =
            let uu____6218 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6218  in
          FStar_Pprint.separate_map uu____6217 p_tuplePattern pats  in
        FStar_Pprint.group uu____6216
    | uu____6219 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6228 =
          let uu____6229 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6229 p_constructorPattern pats  in
        FStar_Pprint.group uu____6228
    | uu____6230 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6233;_},hd::tl::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6238 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6239 = p_constructorPattern hd  in
        let uu____6240 = p_constructorPattern tl  in
        infix0 uu____6238 uu____6239 uu____6240
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6242;_},pats)
        ->
        let uu____6248 = p_quident uid  in
        let uu____6249 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6248 uu____6249
    | uu____6250 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6266;
               FStar_Parser_AST.blevel = uu____6267;
               FStar_Parser_AST.aqual = uu____6268;_},phi))
             when
             let uu____6276 = FStar_Ident.text_of_id lid  in
             let uu____6278 = FStar_Ident.text_of_id lid'  in
             uu____6276 = uu____6278 ->
             let uu____6281 =
               let uu____6282 = p_ident lid  in
               p_refinement aqual uu____6282 t1 phi  in
             soft_parens_with_nesting uu____6281
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6285;
               FStar_Parser_AST.blevel = uu____6286;
               FStar_Parser_AST.aqual = uu____6287;_},phi))
             ->
             let uu____6293 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6293
         | uu____6294 ->
             let uu____6299 =
               let uu____6300 = p_tuplePattern pat  in
               let uu____6301 =
                 let uu____6302 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6302
                  in
               FStar_Pprint.op_Hat_Hat uu____6300 uu____6301  in
             soft_parens_with_nesting uu____6299)
    | FStar_Parser_AST.PatList pats ->
        let uu____6306 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6306 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6325 =
          match uu____6325 with
          | (lid,pat) ->
              let uu____6332 = p_qlident lid  in
              let uu____6333 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6332 uu____6333
           in
        let uu____6334 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6334
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6346 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6347 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6348 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6346
          uu____6347 uu____6348
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6359 =
          let uu____6360 =
            let uu____6361 =
              let uu____6362 = FStar_Ident.text_of_id op  in str uu____6362
               in
            let uu____6364 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6361 uu____6364  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6360  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6359
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6368 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6368 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6376 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6377 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6376 uu____6377
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6379 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6383;
           FStar_Parser_AST.prange = uu____6384;_},uu____6385)
        ->
        let uu____6390 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6390
    | FStar_Parser_AST.PatTuple (uu____6391,false ) ->
        let uu____6398 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6398
    | uu____6399 ->
        let uu____6400 =
          let uu____6402 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6402  in
        failwith uu____6400

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,uu____6408) when
        let uu____6413 = FStar_Ident.text_of_id id  in uu____6413 = "*" ->
        true
    | uu____6418 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6424) -> true
    | uu____6426 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6433 = p_binder' is_atomic b  in
      match uu____6433 with
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
          let uu____6470 =
            let uu____6471 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6472 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6471 uu____6472  in
          (uu____6470, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6478 = p_lident lid  in
          (uu____6478, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6485 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6496;
                   FStar_Parser_AST.blevel = uu____6497;
                   FStar_Parser_AST.aqual = uu____6498;_},phi)
                when
                let uu____6502 = FStar_Ident.text_of_id lid  in
                let uu____6504 = FStar_Ident.text_of_id lid'  in
                uu____6502 = uu____6504 ->
                let uu____6507 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6507 t1 phi
            | uu____6508 ->
                let t' =
                  let uu____6510 = is_typ_tuple t  in
                  if uu____6510
                  then
                    let uu____6513 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6513
                  else p_tmFormula t  in
                let uu____6516 =
                  let uu____6517 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6518 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6517 uu____6518  in
                (uu____6516, t')
             in
          (match uu____6485 with
           | (b',t') ->
               let catf1 =
                 let uu____6536 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6536
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6543 =
                         let uu____6544 =
                           let uu____6545 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6545
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6544
                          in
                       FStar_Pprint.group uu____6543
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6550 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6550)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf1))
      | FStar_Parser_AST.TAnnotated uu____6555 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6583;
                  FStar_Parser_AST.blevel = uu____6584;
                  FStar_Parser_AST.aqual = uu____6585;_},phi)
               ->
               let uu____6589 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6589 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6610 ->
               if is_atomic
               then
                 let uu____6622 = p_atomicTerm t  in
                 (uu____6622, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6629 = p_appTerm t  in
                  (uu____6629, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6640 = p_refinement' aqual_opt binder t phi  in
          match uu____6640 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____6656 -> false
            | FStar_Parser_AST.App uu____6668 -> false
            | FStar_Parser_AST.Op uu____6676 -> false
            | uu____6684 -> true  in
          let uu____6686 = p_noSeqTerm false false phi  in
          match uu____6686 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6703 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6703)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____6712 =
                let uu____6713 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6713 binder  in
              let uu____6714 =
                let uu____6715 = p_appTerm t  in
                let uu____6716 =
                  let uu____6717 =
                    let uu____6718 =
                      let uu____6719 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6720 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6719 uu____6720  in
                    FStar_Pprint.group uu____6718  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6717
                   in
                FStar_Pprint.op_Hat_Hat uu____6715 uu____6716  in
              (uu____6712, uu____6714)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6734 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6734

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6738 =
      (let uu____6742 = FStar_Ident.text_of_id lid  in
       FStar_Util.starts_with uu____6742 FStar_Ident.reserved_prefix) &&
        (let uu____6745 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6745)
       in
    if uu____6738
    then FStar_Pprint.underscore
    else (let uu____6750 = FStar_Ident.text_of_id lid  in str uu____6750)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6753 =
      (let uu____6757 =
         let uu____6759 = FStar_Ident.ident_of_lid lid  in
         FStar_Ident.text_of_id uu____6759  in
       FStar_Util.starts_with uu____6757 FStar_Ident.reserved_prefix) &&
        (let uu____6761 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6761)
       in
    if uu____6753
    then FStar_Pprint.underscore
    else (let uu____6766 = FStar_Ident.string_of_lid lid  in str uu____6766)

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
          let uu____6787 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6787
        else
          (let uu____6790 =
             let uu____6791 =
               let uu____6792 =
                 let uu____6793 =
                   let uu____6794 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6794  in
                 FStar_Pprint.op_Hat_Hat doc uu____6793  in
               FStar_Pprint.group uu____6792  in
             let uu____6795 =
               let uu____6796 =
                 let uu____6797 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6797  in
               FStar_Pprint.op_Hat_Hat comm uu____6796  in
             FStar_Pprint.ifflat uu____6791 uu____6795  in
           FStar_All.pipe_left FStar_Pprint.group uu____6790)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6805 = p_noSeqTerm true false e1  in
            (match uu____6805 with
             | (comm,t1) ->
                 let uu____6814 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6815 =
                   let uu____6816 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6816
                    in
                 FStar_Pprint.op_Hat_Hat uu____6814 uu____6815)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6820 =
              let uu____6821 =
                let uu____6822 =
                  let uu____6823 = p_lident x  in
                  let uu____6824 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6823 uu____6824  in
                let uu____6825 =
                  let uu____6826 = p_noSeqTermAndComment true false e1  in
                  let uu____6829 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6826 uu____6829  in
                op_Hat_Slash_Plus_Hat uu____6822 uu____6825  in
              FStar_Pprint.group uu____6821  in
            let uu____6830 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6820 uu____6830
        | uu____6831 ->
            let uu____6832 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6832

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
            let uu____6844 = p_noSeqTerm true false e1  in
            (match uu____6844 with
             | (comm,t1) ->
                 let uu____6857 =
                   let uu____6858 =
                     let uu____6859 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6859  in
                   let uu____6860 =
                     let uu____6861 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6861
                      in
                   FStar_Pprint.op_Hat_Hat uu____6858 uu____6860  in
                 (comm, uu____6857))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6865 =
              let uu____6866 =
                let uu____6867 =
                  let uu____6868 =
                    let uu____6869 = p_lident x  in
                    let uu____6870 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6869 uu____6870  in
                  let uu____6871 =
                    let uu____6872 = p_noSeqTermAndComment true false e1  in
                    let uu____6875 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6872 uu____6875  in
                  op_Hat_Slash_Plus_Hat uu____6868 uu____6871  in
                FStar_Pprint.group uu____6867  in
              let uu____6876 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6866 uu____6876  in
            (FStar_Pprint.empty, uu____6865)
        | uu____6877 -> p_noSeqTerm ps pb e

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
            let uu____6897 =
              let uu____6898 = p_tmIff e1  in
              let uu____6899 =
                let uu____6900 =
                  let uu____6901 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6901
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6900  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6898 uu____6899  in
            FStar_Pprint.group uu____6897
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6907 =
              let uu____6908 = p_tmIff e1  in
              let uu____6909 =
                let uu____6910 =
                  let uu____6911 =
                    let uu____6912 = p_typ false false t  in
                    let uu____6915 =
                      let uu____6916 = str "by"  in
                      let uu____6918 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6916 uu____6918  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6912 uu____6915  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6911
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6910  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6908 uu____6909  in
            FStar_Pprint.group uu____6907
        | FStar_Parser_AST.Op (id,e1::e2::e3::[]) when
            let uu____6925 = FStar_Ident.text_of_id id  in
            uu____6925 = ".()<-" ->
            let uu____6929 =
              let uu____6930 =
                let uu____6931 =
                  let uu____6932 = p_atomicTermNotQUident e1  in
                  let uu____6933 =
                    let uu____6934 =
                      let uu____6935 =
                        let uu____6936 = p_term false false e2  in
                        soft_parens_with_nesting uu____6936  in
                      let uu____6939 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6935 uu____6939  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6934  in
                  FStar_Pprint.op_Hat_Hat uu____6932 uu____6933  in
                FStar_Pprint.group uu____6931  in
              let uu____6940 =
                let uu____6941 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6941  in
              FStar_Pprint.op_Hat_Hat uu____6930 uu____6940  in
            FStar_Pprint.group uu____6929
        | FStar_Parser_AST.Op (id,e1::e2::e3::[]) when
            let uu____6948 = FStar_Ident.text_of_id id  in
            uu____6948 = ".[]<-" ->
            let uu____6952 =
              let uu____6953 =
                let uu____6954 =
                  let uu____6955 = p_atomicTermNotQUident e1  in
                  let uu____6956 =
                    let uu____6957 =
                      let uu____6958 =
                        let uu____6959 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6959  in
                      let uu____6962 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6958 uu____6962  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6957  in
                  FStar_Pprint.op_Hat_Hat uu____6955 uu____6956  in
                FStar_Pprint.group uu____6954  in
              let uu____6963 =
                let uu____6964 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6964  in
              FStar_Pprint.op_Hat_Hat uu____6953 uu____6963  in
            FStar_Pprint.group uu____6952
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6974 =
              let uu____6975 = str "requires"  in
              let uu____6977 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6975 uu____6977  in
            FStar_Pprint.group uu____6974
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6987 =
              let uu____6988 = str "ensures"  in
              let uu____6990 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6988 uu____6990  in
            FStar_Pprint.group uu____6987
        | FStar_Parser_AST.Attributes es ->
            let uu____6994 =
              let uu____6995 = str "attributes"  in
              let uu____6997 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6995 uu____6997  in
            FStar_Pprint.group uu____6994
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7002 =
                let uu____7003 =
                  let uu____7004 = str "if"  in
                  let uu____7006 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7004 uu____7006  in
                let uu____7009 =
                  let uu____7010 = str "then"  in
                  let uu____7012 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7010 uu____7012  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7003 uu____7009  in
              FStar_Pprint.group uu____7002
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7016,uu____7017,e31) when
                     is_unit e31 ->
                     let uu____7019 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7019
                 | uu____7022 -> p_noSeqTermAndComment false false e2  in
               let uu____7025 =
                 let uu____7026 =
                   let uu____7027 = str "if"  in
                   let uu____7029 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7027 uu____7029  in
                 let uu____7032 =
                   let uu____7033 =
                     let uu____7034 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7034 e2_doc  in
                   let uu____7036 =
                     let uu____7037 = str "else"  in
                     let uu____7039 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7037 uu____7039  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7033 uu____7036  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7026 uu____7032  in
               FStar_Pprint.group uu____7025)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7062 =
              let uu____7063 =
                let uu____7064 =
                  let uu____7065 = str "try"  in
                  let uu____7067 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7065 uu____7067  in
                let uu____7070 =
                  let uu____7071 = str "with"  in
                  let uu____7073 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7071 uu____7073  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7064 uu____7070  in
              FStar_Pprint.group uu____7063  in
            let uu____7082 = paren_if (ps || pb)  in uu____7082 uu____7062
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7109 =
              let uu____7110 =
                let uu____7111 =
                  let uu____7112 = str "match"  in
                  let uu____7114 = p_noSeqTermAndComment false false e1  in
                  let uu____7117 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7112 uu____7114 uu____7117
                   in
                let uu____7121 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7111 uu____7121  in
              FStar_Pprint.group uu____7110  in
            let uu____7130 = paren_if (ps || pb)  in uu____7130 uu____7109
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7137 =
              let uu____7138 =
                let uu____7139 =
                  let uu____7140 = str "let open"  in
                  let uu____7142 = p_quident uid  in
                  let uu____7143 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7140 uu____7142 uu____7143
                   in
                let uu____7147 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7139 uu____7147  in
              FStar_Pprint.group uu____7138  in
            let uu____7149 = paren_if ps  in uu____7149 uu____7137
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7214 is_last =
              match uu____7214 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7248 =
                          let uu____7249 = str "let"  in
                          let uu____7251 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7249 uu____7251
                           in
                        FStar_Pprint.group uu____7248
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7254 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7260 = p_term_sep false false e2  in
                  (match uu____7260 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7270 =
                         if is_last
                         then
                           let uu____7272 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7273 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7272 doc_expr1 uu____7273
                         else
                           (let uu____7279 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7279)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7270)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7330 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7330
                     else
                       (let uu____7335 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7335)) lbs
               in
            let lbs_doc =
              let uu____7339 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7339  in
            let uu____7340 =
              let uu____7341 =
                let uu____7342 =
                  let uu____7343 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7343
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7342  in
              FStar_Pprint.group uu____7341  in
            let uu____7345 = paren_if ps  in uu____7345 uu____7340
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7352;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7355;
                                                             FStar_Parser_AST.level
                                                               = uu____7356;_})
            when matches_var maybe_x x ->
            let uu____7383 =
              let uu____7384 =
                let uu____7385 = str "function"  in
                let uu____7387 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7385 uu____7387  in
              FStar_Pprint.group uu____7384  in
            let uu____7396 = paren_if (ps || pb)  in uu____7396 uu____7383
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7402 =
              let uu____7403 = str "quote"  in
              let uu____7405 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7403 uu____7405  in
            FStar_Pprint.group uu____7402
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7407 =
              let uu____7408 = str "`"  in
              let uu____7410 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7408 uu____7410  in
            FStar_Pprint.group uu____7407
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7412 =
              let uu____7413 = str "`%"  in
              let uu____7415 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7413 uu____7415  in
            FStar_Pprint.group uu____7412
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7417;
              FStar_Parser_AST.level = uu____7418;_}
            ->
            let uu____7419 =
              let uu____7420 = str "`@"  in
              let uu____7422 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7420 uu____7422  in
            FStar_Pprint.group uu____7419
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7424 =
              let uu____7425 = str "`#"  in
              let uu____7427 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7425 uu____7427  in
            FStar_Pprint.group uu____7424
        | FStar_Parser_AST.CalcProof (rel,init,steps) ->
            let head =
              let uu____7436 = str "calc"  in
              let uu____7438 =
                let uu____7439 =
                  let uu____7440 = p_noSeqTermAndComment false false rel  in
                  let uu____7443 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7440 uu____7443  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7439  in
              FStar_Pprint.op_Hat_Hat uu____7436 uu____7438  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7445 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7446 =
              let uu____7447 =
                let uu____7448 =
                  let uu____7449 = p_noSeqTermAndComment false false init  in
                  let uu____7452 =
                    let uu____7453 = str ";"  in
                    let uu____7455 =
                      let uu____7456 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7456
                       in
                    FStar_Pprint.op_Hat_Hat uu____7453 uu____7455  in
                  FStar_Pprint.op_Hat_Hat uu____7449 uu____7452  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7448  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7447
               in
            FStar_Pprint.enclose head uu____7445 uu____7446
        | uu____7458 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7459  ->
    fun uu____7460  ->
      match uu____7460 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7465 =
            let uu____7466 = p_noSeqTermAndComment false false rel  in
            let uu____7469 =
              let uu____7470 =
                let uu____7471 =
                  let uu____7472 =
                    let uu____7473 = p_noSeqTermAndComment false false just
                       in
                    let uu____7476 =
                      let uu____7477 =
                        let uu____7478 =
                          let uu____7479 =
                            let uu____7480 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7483 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7480 uu____7483  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7479
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7478
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7477
                       in
                    FStar_Pprint.op_Hat_Hat uu____7473 uu____7476  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7472  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7471  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7470  in
            FStar_Pprint.op_Hat_Hat uu____7466 uu____7469  in
          FStar_Pprint.group uu____7465

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7485  ->
    match uu___11_7485 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7497 =
          let uu____7498 = str "[@"  in
          let uu____7500 =
            let uu____7501 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7502 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7501 uu____7502  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7498 uu____7500  in
        FStar_Pprint.group uu____7497

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
        | FStar_Parser_AST.QForall (bs,(uu____7520,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7554 =
                   let uu____7555 =
                     let uu____7556 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7556 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7555 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7554 term_doc
             | pats ->
                 let uu____7564 =
                   let uu____7565 =
                     let uu____7566 =
                       let uu____7567 =
                         let uu____7568 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7568
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7567 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7571 = p_trigger trigger  in
                     prefix2 uu____7566 uu____7571  in
                   FStar_Pprint.group uu____7565  in
                 prefix2 uu____7564 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7573,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7607 =
                   let uu____7608 =
                     let uu____7609 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7609 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7608 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7607 term_doc
             | pats ->
                 let uu____7617 =
                   let uu____7618 =
                     let uu____7619 =
                       let uu____7620 =
                         let uu____7621 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7621
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7620 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7624 = p_trigger trigger  in
                     prefix2 uu____7619 uu____7624  in
                   FStar_Pprint.group uu____7618  in
                 prefix2 uu____7617 term_doc)
        | uu____7625 -> p_simpleTerm ps pb e

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
      let uu____7646 = all_binders_annot t  in
      if uu____7646
      then
        let uu____7649 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7649
      else
        (let uu____7660 =
           let uu____7661 =
             let uu____7662 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7662  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7661  in
         FStar_Pprint.group uu____7660)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7721 = x  in
      match uu____7721 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd::tl ->
               let uu____7786 = hd  in
               (match uu____7786 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl
                    else ([b1], t1) :: hd :: tl))
       in
    let p_collapsed_binder cb =
      let uu____7858 = cb  in
      match uu____7858 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd::tl ->
               let uu____7877 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7883 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7883) hd tl
                  in
               cat_with_colon uu____7877 typ)
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
                 FStar_Parser_AST.brange = uu____7962;
                 FStar_Parser_AST.blevel = uu____7963;
                 FStar_Parser_AST.aqual = uu____7964;_},phi))
               when
               let uu____7972 = FStar_Ident.text_of_id lid  in
               let uu____7974 = FStar_Ident.text_of_id lid'  in
               uu____7972 = uu____7974 ->
               let uu____7977 =
                 let uu____7982 = p_ident lid  in
                 p_refinement' aqual uu____7982 t1 phi  in
               FStar_Pervasives_Native.Some uu____7977
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7989) ->
               let uu____7994 =
                 let uu____7999 =
                   let uu____8000 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8001 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8000 uu____8001  in
                 let uu____8002 = p_tmEqNoRefinement t  in
                 (uu____7999, uu____8002)  in
               FStar_Pervasives_Native.Some uu____7994
           | uu____8007 -> FStar_Pervasives_Native.None)
      | uu____8016 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8029 -> false
      | uu____8041 -> true  in
    let uu____8043 = map_if_all all_binders pats  in
    match uu____8043 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8075 = collapse_pats bs  in
        (uu____8075, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8092 = FStar_List.map p_atomicPattern pats  in
        (uu____8092, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8104 -> str "forall"
    | FStar_Parser_AST.QExists uu____8124 -> str "exists"
    | uu____8144 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8146  ->
    match uu___12_8146 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8158 =
          let uu____8159 =
            let uu____8160 =
              let uu____8161 = str "pattern"  in
              let uu____8163 =
                let uu____8164 =
                  let uu____8165 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8165
                   in
                FStar_Pprint.op_Hat_Hat uu____8164 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8161 uu____8163  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8160  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8159  in
        FStar_Pprint.group uu____8158

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8173 = str "\\/"  in
    FStar_Pprint.separate_map uu____8173 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8180 =
      let uu____8181 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8181 p_appTerm pats  in
    FStar_Pprint.group uu____8180

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8193 = p_term_sep false pb e1  in
            (match uu____8193 with
             | (comm,doc) ->
                 let prefix =
                   let uu____8202 = str "fun"  in
                   let uu____8204 =
                     let uu____8205 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8205
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8202 uu____8204  in
                 let uu____8206 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8208 =
                       let uu____8209 =
                         let uu____8210 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8210  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8209
                        in
                     FStar_Pprint.op_Hat_Hat prefix uu____8208
                   else
                     (let uu____8213 = op_Hat_Slash_Plus_Hat prefix doc  in
                      FStar_Pprint.group uu____8213)
                    in
                 let uu____8214 = paren_if ps  in uu____8214 uu____8206)
        | uu____8219 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8227  ->
      match uu____8227 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8251 =
                    let uu____8252 =
                      let uu____8253 =
                        let uu____8254 = p_tuplePattern p  in
                        let uu____8255 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8254 uu____8255  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8253
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8252  in
                  FStar_Pprint.group uu____8251
              | FStar_Pervasives_Native.Some f ->
                  let uu____8257 =
                    let uu____8258 =
                      let uu____8259 =
                        let uu____8260 =
                          let uu____8261 =
                            let uu____8262 = p_tuplePattern p  in
                            let uu____8263 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8262
                              uu____8263
                             in
                          FStar_Pprint.group uu____8261  in
                        let uu____8265 =
                          let uu____8266 =
                            let uu____8269 = p_tmFormula f  in
                            [uu____8269; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8266  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8260 uu____8265
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8259
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8258  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8257
               in
            let uu____8271 = p_term_sep false pb e  in
            match uu____8271 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8281 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8281
                   else
                     (let uu____8284 =
                        let uu____8285 =
                          let uu____8286 =
                            let uu____8287 =
                              let uu____8288 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8288  in
                            op_Hat_Slash_Plus_Hat branch uu____8287  in
                          FStar_Pprint.group uu____8286  in
                        let uu____8289 =
                          let uu____8290 =
                            let uu____8291 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8291  in
                          FStar_Pprint.op_Hat_Hat branch uu____8290  in
                        FStar_Pprint.ifflat uu____8285 uu____8289  in
                      FStar_Pprint.group uu____8284))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8295 =
                       let uu____8296 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8296  in
                     op_Hat_Slash_Plus_Hat branch uu____8295)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd::tl ->
                    let last_pat_branch = one_pattern_branch hd  in
                    let uu____8307 =
                      let uu____8308 =
                        let uu____8309 =
                          let uu____8310 =
                            let uu____8311 =
                              let uu____8312 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8312  in
                            FStar_Pprint.separate_map uu____8311
                              p_tuplePattern (FStar_List.rev tl)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8310
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8309
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8308  in
                    FStar_Pprint.group uu____8307
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8314 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____8321 = FStar_Ident.text_of_id id  in uu____8321 = "<==>" ->
        let uu____8325 = str "<==>"  in
        let uu____8327 = p_tmImplies e1  in
        let uu____8328 = p_tmIff e2  in
        infix0 uu____8325 uu____8327 uu____8328
    | uu____8329 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____8336 = FStar_Ident.text_of_id id  in uu____8336 = "==>" ->
        let uu____8340 = str "==>"  in
        let uu____8342 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8348 = p_tmImplies e2  in
        infix0 uu____8340 uu____8342 uu____8348
    | uu____8349 ->
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
          let uu____8363 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8363 with
          | (terms',last) ->
              let uu____8383 =
                match style with
                | Arrows (n,ln) ->
                    let uu____8418 =
                      let uu____8419 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8419
                       in
                    let uu____8420 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n, ln, terms', uu____8418, uu____8420)
                | Binders (n,ln,parens) ->
                    let uu____8434 =
                      if parens
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8442 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n, ln, uu____8434, break1, uu____8442)
                 in
              (match uu____8383 with
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
                    | uu____8475 when uu____8475 = Prims.int_one ->
                        FStar_List.hd terms
                    | uu____8476 ->
                        let uu____8477 =
                          let uu____8478 =
                            let uu____8479 =
                              let uu____8480 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8481 =
                                let uu____8482 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8482
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8480 uu____8481
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8479  in
                          let uu____8483 =
                            let uu____8484 =
                              let uu____8485 =
                                let uu____8486 =
                                  let uu____8487 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8487  in
                                let uu____8488 =
                                  let uu____8489 =
                                    let uu____8490 =
                                      let uu____8491 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8492 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8498 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8498)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8491
                                        uu____8492
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8490
                                     in
                                  jump2 uu____8489  in
                                FStar_Pprint.ifflat uu____8486 uu____8488  in
                              FStar_Pprint.group uu____8485  in
                            let uu____8500 =
                              let uu____8501 =
                                let uu____8502 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last1  in
                                FStar_Pprint.hang last_n uu____8502  in
                              FStar_Pprint.align uu____8501  in
                            FStar_Pprint.prefix n Prims.int_one uu____8484
                              uu____8500
                             in
                          FStar_Pprint.ifflat uu____8478 uu____8483  in
                        FStar_Pprint.group uu____8477))

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
            | Arrows uu____8516 -> p_tmArrow' p_Tm e
            | Binders uu____8523 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8546 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8552 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8546 uu____8552
      | uu____8555 -> let uu____8556 = p_Tm e  in [uu____8556]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8609 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8635 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8609 uu____8635
        | uu____8658 ->
            let uu____8659 =
              let uu____8670 = p_Tm1 e1  in
              (uu____8670, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8659]
         in
      let fold_fun bs x =
        let uu____8768 = x  in
        match uu____8768 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd::tl ->
                 let uu____8900 = hd  in
                 (match uu____8900 with
                  | (b2s,t2,uu____8929) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl
                           else ([b1], t1, f1) :: hd :: tl
                       | uu____9031 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9088 = cb  in
        match uu____9088 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9117 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd::tl ->
                      let uu____9128 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9134 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9134) hd tl
                         in
                      f uu____9128 typ))
         in
      let binders =
        let uu____9150 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9150  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9213 =
        let uu____9214 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9214 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9213  in
    let disj =
      let uu____9217 =
        let uu____9218 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9218 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9217  in
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
        let uu____9243 = FStar_Ident.text_of_id id  in uu____9243 = "\\/" ->
        let uu____9247 = p_tmDisjunction e1  in
        let uu____9252 = let uu____9257 = p_tmConjunction e2  in [uu____9257]
           in
        FStar_List.append uu____9247 uu____9252
    | uu____9266 -> let uu____9267 = p_tmConjunction e  in [uu____9267]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,e1::e2::[]) when
        let uu____9282 = FStar_Ident.text_of_id id  in uu____9282 = "/\\" ->
        let uu____9286 = p_tmConjunction e1  in
        let uu____9289 = let uu____9292 = p_tmTuple e2  in [uu____9292]  in
        FStar_List.append uu____9286 uu____9289
    | uu____9293 -> let uu____9294 = p_tmTuple e  in [uu____9294]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all1_explicit args) ->
        let uu____9311 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9311
          (fun uu____9319  ->
             match uu____9319 with | (e1,uu____9325) -> p_tmEq e1) args
    | uu____9326 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9335 =
             let uu____9336 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9336  in
           FStar_Pprint.group uu____9335)

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
            (let uu____9356 =
               (let uu____9360 = FStar_Ident.text_of_id op  in
                uu____9360 = "==>") ||
                 (let uu____9365 = FStar_Ident.text_of_id op  in
                  uu____9365 = "<==>")
                in
             Prims.op_Negation uu____9356) &&
              (((is_operatorInfix0ad12 op) ||
                  (let uu____9370 = FStar_Ident.text_of_id op  in
                   uu____9370 = "="))
                 ||
                 (let uu____9375 = FStar_Ident.text_of_id op  in
                  uu____9375 = "|>"))
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9381 = levels op1  in
            (match uu____9381 with
             | (left,mine,right) ->
                 let uu____9400 =
                   let uu____9401 = FStar_All.pipe_left str op1  in
                   let uu____9403 = p_tmEqWith' p_X left e1  in
                   let uu____9404 = p_tmEqWith' p_X right e2  in
                   infix0 uu____9401 uu____9403 uu____9404  in
                 paren_if_gt curr mine uu____9400)
        | FStar_Parser_AST.Op (id,e1::e2::[]) when
            let uu____9410 = FStar_Ident.text_of_id id  in uu____9410 = ":="
            ->
            let uu____9414 =
              let uu____9415 = p_tmEqWith p_X e1  in
              let uu____9416 =
                let uu____9417 =
                  let uu____9418 =
                    let uu____9419 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9419  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9418  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9417  in
              FStar_Pprint.op_Hat_Hat uu____9415 uu____9416  in
            FStar_Pprint.group uu____9414
        | FStar_Parser_AST.Op (id,e1::[]) when
            let uu____9424 = FStar_Ident.text_of_id id  in uu____9424 = "-"
            ->
            let uu____9428 = levels "-"  in
            (match uu____9428 with
             | (left,mine,right) ->
                 let uu____9448 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9448)
        | uu____9449 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9497)::(e2,uu____9499)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9519 = is_list e  in Prims.op_Negation uu____9519)
              ->
              let op = "::"  in
              let uu____9524 = levels op  in
              (match uu____9524 with
               | (left,mine,right) ->
                   let uu____9543 =
                     let uu____9544 = str op  in
                     let uu____9545 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9547 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9544 uu____9545 uu____9547  in
                   paren_if_gt curr mine uu____9543)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9566 = levels op  in
              (match uu____9566 with
               | (left,mine,right) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9600 = p_binder false b  in
                         let uu____9602 =
                           let uu____9603 =
                             let uu____9604 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9604 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9603
                            in
                         FStar_Pprint.op_Hat_Hat uu____9600 uu____9602
                     | FStar_Util.Inr t ->
                         let uu____9606 = p_tmNoEqWith' false p_X left t  in
                         let uu____9608 =
                           let uu____9609 =
                             let uu____9610 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9610 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9609
                            in
                         FStar_Pprint.op_Hat_Hat uu____9606 uu____9608
                      in
                   let uu____9611 =
                     let uu____9612 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9617 = p_tmNoEqWith' false p_X right res  in
                     FStar_Pprint.op_Hat_Hat uu____9612 uu____9617  in
                   paren_if_gt curr mine uu____9611)
          | FStar_Parser_AST.Op (id,e1::e2::[]) when
              (let uu____9626 = FStar_Ident.text_of_id id  in
               uu____9626 = "*") && (FStar_ST.op_Bang unfold_tuples)
              ->
              let op = "*"  in
              let uu____9654 = levels op  in
              (match uu____9654 with
               | (left,mine,right) ->
                   if inside_tuple
                   then
                     let uu____9674 = str op  in
                     let uu____9675 = p_tmNoEqWith' true p_X left e1  in
                     let uu____9677 = p_tmNoEqWith' true p_X right e2  in
                     infix0 uu____9674 uu____9675 uu____9677
                   else
                     (let uu____9681 =
                        let uu____9682 = str op  in
                        let uu____9683 = p_tmNoEqWith' true p_X left e1  in
                        let uu____9685 = p_tmNoEqWith' true p_X right e2  in
                        infix0 uu____9682 uu____9683 uu____9685  in
                      paren_if_gt curr mine uu____9681))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9694 = levels op1  in
              (match uu____9694 with
               | (left,mine,right) ->
                   let uu____9713 =
                     let uu____9714 = str op1  in
                     let uu____9715 = p_tmNoEqWith' false p_X left e1  in
                     let uu____9717 = p_tmNoEqWith' false p_X right e2  in
                     infix0 uu____9714 uu____9715 uu____9717  in
                   paren_if_gt curr mine uu____9713)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9737 =
                let uu____9738 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9739 =
                  let uu____9740 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9740 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9738 uu____9739  in
              braces_with_nesting uu____9737
          | FStar_Parser_AST.Op (id,e1::[]) when
              let uu____9749 = FStar_Ident.text_of_id id  in uu____9749 = "~"
              ->
              let uu____9753 =
                let uu____9754 = str "~"  in
                let uu____9756 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9754 uu____9756  in
              FStar_Pprint.group uu____9753
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op (id,e1::e2::[]) when
                   let uu____9763 = FStar_Ident.text_of_id id  in
                   uu____9763 = "*" ->
                   let op = "*"  in
                   let uu____9770 = levels op  in
                   (match uu____9770 with
                    | (left,mine,right) ->
                        let uu____9789 =
                          let uu____9790 = str op  in
                          let uu____9791 = p_tmNoEqWith' true p_X left e1  in
                          let uu____9793 = p_tmNoEqWith' true p_X right e2
                             in
                          infix0 uu____9790 uu____9791 uu____9793  in
                        paren_if_gt curr mine uu____9789)
               | uu____9795 -> p_X e)
          | uu____9796 -> p_X e

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
        let uu____9803 =
          let uu____9804 = p_lident lid  in
          let uu____9805 =
            let uu____9806 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9806  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9804 uu____9805  in
        FStar_Pprint.group uu____9803
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9809 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9811 = p_appTerm e  in
    let uu____9812 =
      let uu____9813 =
        let uu____9814 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9814 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9813  in
    FStar_Pprint.op_Hat_Hat uu____9811 uu____9812

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9820 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9820 t phi
      | FStar_Parser_AST.TAnnotated uu____9821 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9827 ->
          let uu____9828 =
            let uu____9830 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9830
             in
          failwith uu____9828
      | FStar_Parser_AST.TVariable uu____9833 ->
          let uu____9834 =
            let uu____9836 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9836
             in
          failwith uu____9834
      | FStar_Parser_AST.NoName uu____9839 ->
          let uu____9840 =
            let uu____9842 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9842
             in
          failwith uu____9840

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9846  ->
      match uu____9846 with
      | (lid,e) ->
          let uu____9854 =
            let uu____9855 = p_qlident lid  in
            let uu____9856 =
              let uu____9857 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9857
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9855 uu____9856  in
          FStar_Pprint.group uu____9854

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9860 when is_general_application e ->
        let uu____9867 = head_and_args e  in
        (match uu____9867 with
         | (head,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9914 = p_argTerm e1  in
                  let uu____9915 =
                    let uu____9916 =
                      let uu____9917 =
                        let uu____9918 = str "`"  in
                        let uu____9920 =
                          let uu____9921 = p_indexingTerm head  in
                          let uu____9922 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9921 uu____9922  in
                        FStar_Pprint.op_Hat_Hat uu____9918 uu____9920  in
                      FStar_Pprint.group uu____9917  in
                    let uu____9924 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9916 uu____9924  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9914 uu____9915
              | uu____9925 ->
                  let uu____9932 =
                    let uu____9943 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9943
                    then
                      let uu____9977 =
                        FStar_Util.take
                          (fun uu____10001  ->
                             match uu____10001 with
                             | (uu____10007,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9977 with
                      | (fs_typ_args,args1) ->
                          let uu____10045 =
                            let uu____10046 = p_indexingTerm head  in
                            let uu____10047 =
                              let uu____10048 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____10048
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10046 uu____10047
                             in
                          (uu____10045, args1)
                    else
                      (let uu____10063 = p_indexingTerm head  in
                       (uu____10063, args))
                     in
                  (match uu____9932 with
                   | (head_doc,args1) ->
                       let uu____10084 =
                         let uu____10085 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____10085 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10084)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10107 =
             (is_dtuple_constructor lid) && (all1_explicit args)  in
           Prims.op_Negation uu____10107)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10126 =
               let uu____10127 = p_quident lid  in
               let uu____10128 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10127 uu____10128  in
             FStar_Pprint.group uu____10126
         | hd::tl ->
             let uu____10145 =
               let uu____10146 =
                 let uu____10147 =
                   let uu____10148 = p_quident lid  in
                   let uu____10149 = p_argTerm hd  in
                   prefix2 uu____10148 uu____10149  in
                 FStar_Pprint.group uu____10147  in
               let uu____10150 =
                 let uu____10151 =
                   FStar_Pprint.separate_map break1 p_argTerm tl  in
                 jump2 uu____10151  in
               FStar_Pprint.op_Hat_Hat uu____10146 uu____10150  in
             FStar_Pprint.group uu____10145)
    | uu____10156 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10167 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10167 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10171 = str "#"  in
        let uu____10173 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10171 uu____10173
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10176 = str "#["  in
        let uu____10178 =
          let uu____10179 = p_indexingTerm t  in
          let uu____10180 =
            let uu____10181 = str "]"  in
            let uu____10183 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10181 uu____10183  in
          FStar_Pprint.op_Hat_Hat uu____10179 uu____10180  in
        FStar_Pprint.op_Hat_Hat uu____10176 uu____10178
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10186  ->
    match uu____10186 with | (e,uu____10192) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (id,e1::e2::[]) when
          let uu____10202 = FStar_Ident.text_of_id id  in uu____10202 = ".()"
          ->
          let uu____10206 =
            let uu____10207 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10208 =
              let uu____10209 =
                let uu____10210 = p_term false false e2  in
                soft_parens_with_nesting uu____10210  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10209  in
            FStar_Pprint.op_Hat_Hat uu____10207 uu____10208  in
          FStar_Pprint.group uu____10206
      | FStar_Parser_AST.Op (id,e1::e2::[]) when
          let uu____10218 = FStar_Ident.text_of_id id  in uu____10218 = ".[]"
          ->
          let uu____10222 =
            let uu____10223 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10224 =
              let uu____10225 =
                let uu____10226 = p_term false false e2  in
                soft_brackets_with_nesting uu____10226  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10225  in
            FStar_Pprint.op_Hat_Hat uu____10223 uu____10224  in
          FStar_Pprint.group uu____10222
      | uu____10229 -> exit e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10234 = p_quident lid  in
        let uu____10235 =
          let uu____10236 =
            let uu____10237 = p_term false false e1  in
            soft_parens_with_nesting uu____10237  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10236  in
        FStar_Pprint.op_Hat_Hat uu____10234 uu____10235
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10245 =
          let uu____10246 = FStar_Ident.text_of_id op  in str uu____10246  in
        let uu____10248 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10245 uu____10248
    | uu____10249 -> p_atomicTermNotQUident e

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
         | uu____10262 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10271 =
          let uu____10272 = FStar_Ident.text_of_id op  in str uu____10272  in
        let uu____10274 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10271 uu____10274
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10278 =
          let uu____10279 =
            let uu____10280 =
              let uu____10281 = FStar_Ident.text_of_id op  in str uu____10281
               in
            let uu____10283 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10280 uu____10283  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10279  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10278
    | FStar_Parser_AST.Construct (lid,args) when
        (is_dtuple_constructor lid) && (all1_explicit args) ->
        let uu____10298 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____10299 =
          let uu____10300 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____10300
            (fun uu____10308  ->
               match uu____10308 with | (e1,uu____10314) -> p_tmEq e1) args
           in
        let uu____10315 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10298
          uu____10299 uu____10315
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10320 =
          let uu____10321 = p_atomicTermNotQUident e1  in
          let uu____10322 =
            let uu____10323 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10323  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10321
            uu____10322
           in
        FStar_Pprint.group uu____10320
    | uu____10326 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10331 = p_quident constr_lid  in
        let uu____10332 =
          let uu____10333 =
            let uu____10334 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10334  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10333  in
        FStar_Pprint.op_Hat_Hat uu____10331 uu____10332
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10336 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10336 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10338 = p_term_sep false false e1  in
        (match uu____10338 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10351 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10351))
    | uu____10352 when is_array e ->
        let es = extract_from_list e  in
        let uu____10356 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10357 =
          let uu____10358 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10358
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10363 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10356
          uu____10357 uu____10363
    | uu____10366 when is_list e ->
        let uu____10367 =
          let uu____10368 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10369 = extract_from_list e  in
          separate_map_or_flow_last uu____10368
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10369
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10367 FStar_Pprint.rbracket
    | uu____10378 when is_lex_list e ->
        let uu____10379 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10380 =
          let uu____10381 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10382 = extract_from_list e  in
          separate_map_or_flow_last uu____10381
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10382
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10379
          uu____10380 FStar_Pprint.rbracket
    | uu____10391 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10395 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10396 =
          let uu____10397 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10397 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10395
          uu____10396 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10407 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10410 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10407 uu____10410
    | FStar_Parser_AST.Op (op,args) when
        let uu____10419 = handleable_op op args  in
        Prims.op_Negation uu____10419 ->
        let uu____10421 =
          let uu____10423 =
            let uu____10425 = FStar_Ident.text_of_id op  in
            let uu____10427 =
              let uu____10429 =
                let uu____10431 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10431
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10429  in
            Prims.op_Hat uu____10425 uu____10427  in
          Prims.op_Hat "Operation " uu____10423  in
        failwith uu____10421
    | FStar_Parser_AST.Uvar id ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10438 = p_term false false e  in
        soft_parens_with_nesting uu____10438
    | FStar_Parser_AST.Const uu____10441 ->
        let uu____10442 = p_term false false e  in
        soft_parens_with_nesting uu____10442
    | FStar_Parser_AST.Op uu____10445 ->
        let uu____10452 = p_term false false e  in
        soft_parens_with_nesting uu____10452
    | FStar_Parser_AST.Tvar uu____10455 ->
        let uu____10456 = p_term false false e  in
        soft_parens_with_nesting uu____10456
    | FStar_Parser_AST.Var uu____10459 ->
        let uu____10460 = p_term false false e  in
        soft_parens_with_nesting uu____10460
    | FStar_Parser_AST.Name uu____10463 ->
        let uu____10464 = p_term false false e  in
        soft_parens_with_nesting uu____10464
    | FStar_Parser_AST.Construct uu____10467 ->
        let uu____10478 = p_term false false e  in
        soft_parens_with_nesting uu____10478
    | FStar_Parser_AST.Abs uu____10481 ->
        let uu____10488 = p_term false false e  in
        soft_parens_with_nesting uu____10488
    | FStar_Parser_AST.App uu____10491 ->
        let uu____10498 = p_term false false e  in
        soft_parens_with_nesting uu____10498
    | FStar_Parser_AST.Let uu____10501 ->
        let uu____10522 = p_term false false e  in
        soft_parens_with_nesting uu____10522
    | FStar_Parser_AST.LetOpen uu____10525 ->
        let uu____10530 = p_term false false e  in
        soft_parens_with_nesting uu____10530
    | FStar_Parser_AST.Seq uu____10533 ->
        let uu____10538 = p_term false false e  in
        soft_parens_with_nesting uu____10538
    | FStar_Parser_AST.Bind uu____10541 ->
        let uu____10548 = p_term false false e  in
        soft_parens_with_nesting uu____10548
    | FStar_Parser_AST.If uu____10551 ->
        let uu____10558 = p_term false false e  in
        soft_parens_with_nesting uu____10558
    | FStar_Parser_AST.Match uu____10561 ->
        let uu____10576 = p_term false false e  in
        soft_parens_with_nesting uu____10576
    | FStar_Parser_AST.TryWith uu____10579 ->
        let uu____10594 = p_term false false e  in
        soft_parens_with_nesting uu____10594
    | FStar_Parser_AST.Ascribed uu____10597 ->
        let uu____10606 = p_term false false e  in
        soft_parens_with_nesting uu____10606
    | FStar_Parser_AST.Record uu____10609 ->
        let uu____10622 = p_term false false e  in
        soft_parens_with_nesting uu____10622
    | FStar_Parser_AST.Project uu____10625 ->
        let uu____10630 = p_term false false e  in
        soft_parens_with_nesting uu____10630
    | FStar_Parser_AST.Product uu____10633 ->
        let uu____10640 = p_term false false e  in
        soft_parens_with_nesting uu____10640
    | FStar_Parser_AST.Sum uu____10643 ->
        let uu____10654 = p_term false false e  in
        soft_parens_with_nesting uu____10654
    | FStar_Parser_AST.QForall uu____10657 ->
        let uu____10676 = p_term false false e  in
        soft_parens_with_nesting uu____10676
    | FStar_Parser_AST.QExists uu____10679 ->
        let uu____10698 = p_term false false e  in
        soft_parens_with_nesting uu____10698
    | FStar_Parser_AST.Refine uu____10701 ->
        let uu____10706 = p_term false false e  in
        soft_parens_with_nesting uu____10706
    | FStar_Parser_AST.NamedTyp uu____10709 ->
        let uu____10714 = p_term false false e  in
        soft_parens_with_nesting uu____10714
    | FStar_Parser_AST.Requires uu____10717 ->
        let uu____10725 = p_term false false e  in
        soft_parens_with_nesting uu____10725
    | FStar_Parser_AST.Ensures uu____10728 ->
        let uu____10736 = p_term false false e  in
        soft_parens_with_nesting uu____10736
    | FStar_Parser_AST.Attributes uu____10739 ->
        let uu____10742 = p_term false false e  in
        soft_parens_with_nesting uu____10742
    | FStar_Parser_AST.Quote uu____10745 ->
        let uu____10750 = p_term false false e  in
        soft_parens_with_nesting uu____10750
    | FStar_Parser_AST.VQuote uu____10753 ->
        let uu____10754 = p_term false false e  in
        soft_parens_with_nesting uu____10754
    | FStar_Parser_AST.Antiquote uu____10757 ->
        let uu____10758 = p_term false false e  in
        soft_parens_with_nesting uu____10758
    | FStar_Parser_AST.CalcProof uu____10761 ->
        let uu____10770 = p_term false false e  in
        soft_parens_with_nesting uu____10770

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10773  ->
    match uu___15_10773 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10785) ->
        let uu____10788 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10788
    | FStar_Const.Const_bytearray (bytes,uu____10790) ->
        let uu____10797 =
          let uu____10798 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10798  in
        let uu____10799 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10797 uu____10799
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10822 =
          match uu___13_10822 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10829 =
          match uu___14_10829 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10844  ->
               match uu____10844 with
               | (s,w) ->
                   let uu____10851 = signedness s  in
                   let uu____10852 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10851 uu____10852)
            sign_width_opt
           in
        let uu____10853 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10853 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10857 = FStar_Range.string_of_range r  in str uu____10857
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10861 = p_quident lid  in
        let uu____10862 =
          let uu____10863 =
            let uu____10864 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10864  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10863  in
        FStar_Pprint.op_Hat_Hat uu____10861 uu____10862

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10867 = str "u#"  in
    let uu____10869 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10867 uu____10869

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op (id,u1::u2::[]) when
        let uu____10876 = FStar_Ident.text_of_id id  in uu____10876 = "+" ->
        let uu____10880 =
          let uu____10881 = p_universeFrom u1  in
          let uu____10882 =
            let uu____10883 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10883  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10881 uu____10882  in
        FStar_Pprint.group uu____10880
    | FStar_Parser_AST.App uu____10884 ->
        let uu____10891 = head_and_args u  in
        (match uu____10891 with
         | (head,args) ->
             (match head.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10917 =
                    let uu____10918 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10919 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10927  ->
                           match uu____10927 with
                           | (u1,uu____10933) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10918 uu____10919  in
                  FStar_Pprint.group uu____10917
              | uu____10934 ->
                  let uu____10935 =
                    let uu____10937 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10937
                     in
                  failwith uu____10935))
    | uu____10940 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id ->
        let uu____10966 = FStar_Ident.text_of_id id  in str uu____10966
    | FStar_Parser_AST.Paren u1 ->
        let uu____10969 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10969
    | FStar_Parser_AST.App uu____10970 ->
        let uu____10977 = p_universeFrom u  in
        soft_parens_with_nesting uu____10977
    | FStar_Parser_AST.Op (id,uu____10979::uu____10980::[]) when
        let uu____10983 = FStar_Ident.text_of_id id  in uu____10983 = "+" ->
        let uu____10987 = p_universeFrom u  in
        soft_parens_with_nesting uu____10987
    | uu____10988 ->
        let uu____10989 =
          let uu____10991 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10991
           in
        failwith uu____10989

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
       | FStar_Parser_AST.Module (uu____11080,decls) ->
           let uu____11086 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11086
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11095,decls,uu____11097) ->
           let uu____11104 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11104
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11164  ->
         match uu____11164 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id,uu____11186)) -> false
      | ([],uu____11190) -> false
      | uu____11194 -> true  in
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
        | FStar_Parser_AST.Module (uu____11243,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11249,decls,uu____11251) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11303 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11316;
                 FStar_Parser_AST.quals = uu____11317;
                 FStar_Parser_AST.attrs = uu____11318;_}::uu____11319 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11323 =
                   let uu____11326 =
                     let uu____11329 = FStar_List.tl ds  in d :: uu____11329
                      in
                   d0 :: uu____11326  in
                 (uu____11323, (d0.FStar_Parser_AST.drange))
             | uu____11334 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11303 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11391 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11391 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11500 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11500, comments1))))))
  