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
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___0_270  ->
         match uu___0_270 with
         | (uu____276,FStar_Parser_AST.Nothing ) -> true
         | uu____278 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____307 'Auu____308 .
    Prims.bool -> ('Auu____307 -> 'Auu____308) -> 'Auu____307 -> 'Auu____308
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
  'Auu____418 'Auu____419 .
    'Auu____418 ->
      ('Auu____419 -> 'Auu____418) ->
        'Auu____419 FStar_Pervasives_Native.option -> 'Auu____418
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
  'Auu____532 .
    FStar_Pprint.document ->
      ('Auu____532 -> FStar_Pprint.document) ->
        'Auu____532 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____557 =
          let uu____558 =
            let uu____559 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____559  in
          FStar_Pprint.separate_map uu____558 f l  in
        FStar_Pprint.group uu____557
  
let precede_break_separate_map :
  'Auu____571 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____571 -> FStar_Pprint.document) ->
          'Auu____571 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____601 =
            let uu____602 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____603 =
              let uu____604 = FStar_List.hd l  in
              FStar_All.pipe_right uu____604 f  in
            FStar_Pprint.precede uu____602 uu____603  in
          let uu____605 =
            let uu____606 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____612 =
                   let uu____613 =
                     let uu____614 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____614  in
                   FStar_Pprint.op_Hat_Hat sep uu____613  in
                 FStar_Pprint.op_Hat_Hat break1 uu____612) uu____606
             in
          FStar_Pprint.op_Hat_Hat uu____601 uu____605
  
let concat_break_map :
  'Auu____622 .
    ('Auu____622 -> FStar_Pprint.document) ->
      'Auu____622 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____642 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____646 = f x  in FStar_Pprint.op_Hat_Hat uu____646 break1)
          l
         in
      FStar_Pprint.group uu____642
  
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
    let uu____709 = str "begin"  in
    let uu____711 = str "end"  in
    FStar_Pprint.soft_surround (Prims.of_int (2)) Prims.int_one uu____709
      contents uu____711
  
let separate_map_last :
  'Auu____724 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____724 -> FStar_Pprint.document) ->
        'Auu____724 Prims.list -> FStar_Pprint.document
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
  'Auu____776 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____776 -> FStar_Pprint.document) ->
        'Auu____776 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____808 =
          let uu____809 =
            let uu____810 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____810  in
          separate_map_last uu____809 f l  in
        FStar_Pprint.group uu____808
  
let separate_map_or_flow :
  'Auu____820 .
    FStar_Pprint.document ->
      ('Auu____820 -> FStar_Pprint.document) ->
        'Auu____820 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.of_int (10))
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____858 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____858 -> FStar_Pprint.document) ->
        'Auu____858 Prims.list -> FStar_Pprint.document
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
  'Auu____910 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____910 -> FStar_Pprint.document) ->
        'Auu____910 Prims.list -> FStar_Pprint.document
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
              let uu____992 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____992
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1014 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1014 -> FStar_Pprint.document) ->
                  'Auu____1014 Prims.list -> FStar_Pprint.document
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
                    (let uu____1073 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1073
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1093 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1093 -> FStar_Pprint.document) ->
                  'Auu____1093 Prims.list -> FStar_Pprint.document
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
                    (let uu____1152 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1152
                       closing)
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1162 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1178 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1178
      | uu____1181 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1232::(e2,uu____1234)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1257 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1281,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1292,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1313 = extract_from_list e2  in e1 :: uu____1313
    | uu____1316 ->
        let uu____1317 =
          let uu____1319 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1319  in
        failwith uu____1317
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1333;
           FStar_Parser_AST.level = uu____1334;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_of_list_lid) &&
          (is_list l)
    | uu____1336 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1348;
           FStar_Parser_AST.level = uu____1349;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1351;
                                                         FStar_Parser_AST.level
                                                           = uu____1352;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1354;
                                                    FStar_Parser_AST.level =
                                                      uu____1355;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1357;
                FStar_Parser_AST.level = uu____1358;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1360;
           FStar_Parser_AST.level = uu____1361;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1363 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1375 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1376;
           FStar_Parser_AST.range = uu____1377;
           FStar_Parser_AST.level = uu____1378;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1379;
                                                         FStar_Parser_AST.range
                                                           = uu____1380;
                                                         FStar_Parser_AST.level
                                                           = uu____1381;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1383;
                                                    FStar_Parser_AST.level =
                                                      uu____1384;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1385;
                FStar_Parser_AST.range = uu____1386;
                FStar_Parser_AST.level = uu____1387;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1389;
           FStar_Parser_AST.level = uu____1390;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1392 = extract_from_ref_set e1  in
        let uu____1395 = extract_from_ref_set e2  in
        FStar_List.append uu____1392 uu____1395
    | uu____1398 ->
        let uu____1399 =
          let uu____1401 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1401  in
        failwith uu____1399
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1413 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1413
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1422 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1422
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1433 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1433 Prims.int_zero  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1443 = FStar_Ident.text_of_id op  in uu____1443 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1513 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1533 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1544 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1555 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_1581  ->
    match uu___1_1581 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_1616  ->
      match uu___2_1616 with
      | FStar_Util.Inl c ->
          let uu____1629 = FStar_String.get s Prims.int_zero  in
          uu____1629 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1645 .
    Prims.string ->
      ('Auu____1645 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1669  ->
      match uu____1669 with
      | (assoc_levels,tokens) ->
          let uu____1701 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1701 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_1873 =
    match uu___3_1873 with
    | Left  -> (l, l, (l - Prims.int_one))
    | Right  -> ((l - Prims.int_one), l, l)
    | NonAssoc  -> ((l - Prims.int_one), l, (l - Prims.int_one))  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1923  ->
         match uu____1923 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1998 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1998 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2050) ->
          assoc_levels
      | uu____2088 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2121 . ('Auu____2121 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2170 =
        FStar_List.tryFind
          (fun uu____2206  ->
             match uu____2206 with
             | (uu____2223,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2170 with
      | FStar_Pervasives_Native.Some ((uu____2252,l1,uu____2254),uu____2255)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2305 =
            let uu____2307 =
              let uu____2309 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2309  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2307
             in
          failwith uu____2305
       in
    FStar_List.fold_left find_level_and_max Prims.int_zero l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2344 = assign_levels level_associativity_spec op  in
    match uu____2344 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - Prims.int_one), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2403 =
      let uu____2406 =
        let uu____2412 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2412  in
      FStar_List.tryFind uu____2406 operatorInfix0ad12  in
    uu____2403 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2479 =
      let uu____2494 =
        let uu____2512 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2512  in
      FStar_List.tryFind uu____2494 opinfix34  in
    uu____2479 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2578 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2578
    then Prims.int_one
    else
      (let uu____2591 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2591
       then (Prims.of_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.of_int (3))
         else Prims.int_zero)
  
let handleable_op :
  'Auu____2637 . FStar_Ident.ident -> 'Auu____2637 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _2653 when _2653 = Prims.int_zero -> true
      | _2655 when _2655 = Prims.int_one ->
          (is_general_prefix_op op) ||
            (let uu____2657 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2657 ["-"; "~"])
      | _2665 when _2665 = (Prims.of_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2667 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2667
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _2689 when _2689 = (Prims.of_int (3)) ->
          let uu____2690 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2690 [".()<-"; ".[]<-"]
      | uu____2698 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2744 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2796 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2838 -> true
      | uu____2844 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2877 = FStar_List.for_all is_binder_annot bs  in
          if uu____2877
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, Prims.int_zero)
      | uu____2892 -> (true, (l + Prims.int_one))  in
    let uu____2897 = all_binders e Prims.int_zero  in
    match uu____2897 with
    | (b,l) -> if b && (l > Prims.int_one) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____2936 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____2936
  
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
  'Auu____3025 .
    ('Auu____3025 -> FStar_Pprint.document) ->
      'Auu____3025 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3067 = FStar_ST.op_Bang comment_stack  in
          match uu____3067 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3138 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3138 FStar_Pprint.hardline  in
              let uu____3139 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3139
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3181 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3181 print_pos lookahead_pos))
              else
                (let uu____3184 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3184))
           in
        let uu____3187 =
          let uu____3193 =
            let uu____3194 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3194  in
          let uu____3195 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3193 uu____3195  in
        match uu____3187 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3204 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3204
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3216 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3216)
  
let with_comment_sep :
  'Auu____3228 'Auu____3229 .
    ('Auu____3228 -> 'Auu____3229) ->
      'Auu____3228 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3229)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3275 = FStar_ST.op_Bang comment_stack  in
          match uu____3275 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3346 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3346
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3388 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3392 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3392)
                     in
                  comments_before_pos uu____3388 print_pos lookahead_pos))
              else
                (let uu____3395 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3395))
           in
        let uu____3398 =
          let uu____3404 =
            let uu____3405 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3405  in
          let uu____3406 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3404 uu____3406  in
        match uu____3398 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3419 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3419
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
                let uu____3472 = FStar_ST.op_Bang comment_stack  in
                match uu____3472 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3566 =
                          let uu____3568 =
                            let uu____3570 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3570  in
                          uu____3568 - lbegin  in
                        max k uu____3566  in
                      let lnum1 = min (Prims.of_int (2)) lnum  in
                      let doc1 =
                        let uu____3575 =
                          let uu____3576 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3577 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3576 uu____3577  in
                        FStar_Pprint.op_Hat_Hat doc uu____3575  in
                      let uu____3578 =
                        let uu____3580 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3580  in
                      place_comments_until_pos Prims.int_one uu____3578 pos
                        meta_decl doc1 true init1))
                | uu____3583 ->
                    if doc = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3596 = FStar_Range.line_of_pos pos  in
                         uu____3596 - lbegin  in
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
                       let uu____3624 =
                         FStar_Pprint.repeat lnum5 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc uu____3624)
  
let separate_map_with_comments :
  'Auu____3638 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3638 -> FStar_Pprint.document) ->
          'Auu____3638 Prims.list ->
            ('Auu____3638 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3697 x =
              match uu____3697 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3716 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3716 meta_decl doc false false
                     in
                  let uu____3720 =
                    let uu____3722 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3722  in
                  let uu____3723 =
                    let uu____3724 =
                      let uu____3725 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3725  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3724  in
                  (uu____3720, uu____3723)
               in
            let uu____3727 =
              let uu____3734 = FStar_List.hd xs  in
              let uu____3735 = FStar_List.tl xs  in (uu____3734, uu____3735)
               in
            match uu____3727 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3753 =
                    let uu____3755 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3755  in
                  let uu____3756 =
                    let uu____3757 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3757  in
                  (uu____3753, uu____3756)  in
                let uu____3759 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3759
  
let separate_map_with_comments_kw :
  'Auu____3786 'Auu____3787 .
    'Auu____3786 ->
      'Auu____3786 ->
        ('Auu____3786 -> 'Auu____3787 -> FStar_Pprint.document) ->
          'Auu____3787 Prims.list ->
            ('Auu____3787 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3851 x =
              match uu____3851 with
              | (last_line,doc) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc1 =
                    let uu____3870 = FStar_Range.start_of_range r  in
                    place_comments_until_pos Prims.int_one last_line
                      uu____3870 meta_decl doc false false
                     in
                  let uu____3874 =
                    let uu____3876 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3876  in
                  let uu____3877 =
                    let uu____3878 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____3878  in
                  (uu____3874, uu____3877)
               in
            let uu____3880 =
              let uu____3887 = FStar_List.hd xs  in
              let uu____3888 = FStar_List.tl xs  in (uu____3887, uu____3888)
               in
            match uu____3880 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3906 =
                    let uu____3908 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3908  in
                  let uu____3909 = f prefix1 x  in (uu____3906, uu____3909)
                   in
                let uu____3911 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3911
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4867)) ->
          let uu____4870 =
            let uu____4872 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____4872 FStar_Util.is_upper  in
          if uu____4870
          then
            let uu____4878 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4878 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4881 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4888 = p_attributes d.FStar_Parser_AST.attrs  in
    let uu____4889 =
      let uu____4890 = p_rawDecl d  in
      FStar_Pprint.op_Hat_Hat qualifiers uu____4890  in
    FStar_Pprint.op_Hat_Hat uu____4888 uu____4889

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4892 ->
        let uu____4893 =
          let uu____4894 = str "@ "  in
          let uu____4896 =
            let uu____4897 =
              let uu____4898 =
                let uu____4899 =
                  let uu____4900 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4900  in
                FStar_Pprint.op_Hat_Hat uu____4899 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4898  in
            FStar_Pprint.op_Hat_Hat uu____4897 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4894 uu____4896  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4893

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4906 =
          let uu____4907 = str "val"  in
          let uu____4909 =
            let uu____4910 =
              let uu____4911 = p_lident lid  in
              let uu____4912 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4911 uu____4912  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4910  in
          FStar_Pprint.op_Hat_Hat uu____4907 uu____4909  in
        let uu____4913 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4906 uu____4913
    | FStar_Parser_AST.TopLevelLet (uu____4916,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4941 =
               let uu____4942 = str "let"  in p_letlhs uu____4942 lb false
                in
             FStar_Pprint.group uu____4941) lbs
    | uu____4945 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_4960 =
          match uu___4_4960 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4968 = f x  in
              let uu____4969 =
                let uu____4970 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4970  in
              FStar_Pprint.op_Hat_Hat uu____4968 uu____4969
           in
        let uu____4971 = str "["  in
        let uu____4973 =
          let uu____4974 = p_list' l  in
          let uu____4975 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4974 uu____4975  in
        FStar_Pprint.op_Hat_Hat uu____4971 uu____4973

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4979 =
          let uu____4980 = str "open"  in
          let uu____4982 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4980 uu____4982  in
        FStar_Pprint.group uu____4979
    | FStar_Parser_AST.Include uid ->
        let uu____4984 =
          let uu____4985 = str "include"  in
          let uu____4987 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4985 uu____4987  in
        FStar_Pprint.group uu____4984
    | FStar_Parser_AST.Friend uid ->
        let uu____4989 =
          let uu____4990 = str "friend"  in
          let uu____4992 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4990 uu____4992  in
        FStar_Pprint.group uu____4989
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4995 =
          let uu____4996 = str "module"  in
          let uu____4998 =
            let uu____4999 =
              let uu____5000 = p_uident uid1  in
              let uu____5001 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5000 uu____5001  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4999  in
          FStar_Pprint.op_Hat_Hat uu____4996 uu____4998  in
        let uu____5002 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4995 uu____5002
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5004 =
          let uu____5005 = str "module"  in
          let uu____5007 =
            let uu____5008 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5008  in
          FStar_Pprint.op_Hat_Hat uu____5005 uu____5007  in
        FStar_Pprint.group uu____5004
    | FStar_Parser_AST.Tycon
        (true ,uu____5009,(FStar_Parser_AST.TyconAbbrev
         (uid,tpars,FStar_Pervasives_Native.None ,t))::[])
        ->
        let effect_prefix_doc =
          let uu____5026 = str "effect"  in
          let uu____5028 =
            let uu____5029 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5029  in
          FStar_Pprint.op_Hat_Hat uu____5026 uu____5028  in
        let uu____5030 =
          let uu____5031 = p_typars tpars  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            effect_prefix_doc uu____5031 FStar_Pprint.equals
           in
        let uu____5034 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5030 uu____5034
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5053 =
          let uu____5054 = FStar_List.hd tcdefs  in
          p_typeDeclWithKw s uu____5054  in
        let uu____5055 =
          let uu____5056 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5064 =
                    let uu____5065 = str "and"  in
                    p_typeDeclWithKw uu____5065 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5064)) uu____5056
           in
        FStar_Pprint.op_Hat_Hat uu____5053 uu____5055
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5082 = str "let"  in
          let uu____5084 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5082 uu____5084  in
        let uu____5085 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5085 p_letbinding lbs
          (fun uu____5095  ->
             match uu____5095 with
             | (p,t) ->
                 let uu____5102 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 { r = uu____5102; has_qs = false; has_attrs = false })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5107 =
          let uu____5108 = str "val"  in
          let uu____5110 =
            let uu____5111 =
              let uu____5112 = p_lident lid  in
              let uu____5113 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5112 uu____5113  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5111  in
          FStar_Pprint.op_Hat_Hat uu____5108 uu____5110  in
        FStar_All.pipe_left FStar_Pprint.group uu____5107
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5118 =
            let uu____5120 =
              FStar_Util.char_at id1.FStar_Ident.idText Prims.int_zero  in
            FStar_All.pipe_right uu____5120 FStar_Util.is_upper  in
          if uu____5118
          then FStar_Pprint.empty
          else
            (let uu____5128 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5128 FStar_Pprint.space)
           in
        let uu____5130 =
          let uu____5131 = p_ident id1  in
          let uu____5132 =
            let uu____5133 =
              let uu____5134 =
                let uu____5135 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5135  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5134  in
            FStar_Pprint.group uu____5133  in
          FStar_Pprint.op_Hat_Hat uu____5131 uu____5132  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5130
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5144 = str "exception"  in
        let uu____5146 =
          let uu____5147 =
            let uu____5148 = p_uident uid  in
            let uu____5149 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5153 =
                     let uu____5154 = str "of"  in
                     let uu____5156 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5154 uu____5156  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5153) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5148 uu____5149  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5147  in
        FStar_Pprint.op_Hat_Hat uu____5144 uu____5146
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5160 = str "new_effect"  in
        let uu____5162 =
          let uu____5163 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5163  in
        FStar_Pprint.op_Hat_Hat uu____5160 uu____5162
    | FStar_Parser_AST.SubEffect se ->
        let uu____5165 = str "sub_effect"  in
        let uu____5167 =
          let uu____5168 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5168  in
        FStar_Pprint.op_Hat_Hat uu____5165 uu____5167
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Main uu____5170 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5172,uu____5173) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5189 = str "%splice"  in
        let uu____5191 =
          let uu____5192 =
            let uu____5193 = str ";"  in p_list p_uident uu____5193 ids  in
          let uu____5195 =
            let uu____5196 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5196  in
          FStar_Pprint.op_Hat_Hat uu____5192 uu____5195  in
        FStar_Pprint.op_Hat_Hat uu____5189 uu____5191

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_5199  ->
    match uu___5_5199 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5202 = str "#set-options"  in
        let uu____5204 =
          let uu____5205 =
            let uu____5206 = str s  in FStar_Pprint.dquotes uu____5206  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5205  in
        FStar_Pprint.op_Hat_Hat uu____5202 uu____5204
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5211 = str "#reset-options"  in
        let uu____5213 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5219 =
                 let uu____5220 = str s  in FStar_Pprint.dquotes uu____5220
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5219) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5211 uu____5213
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5225 = str "#push-options"  in
        let uu____5227 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5233 =
                 let uu____5234 = str s  in FStar_Pprint.dquotes uu____5234
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5233) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5225 uu____5227
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
      let uu____5267 = p_typeDecl kw typedecl  in
      match uu____5267 with
      | (comm,decl,body,pre) ->
          if comm = FStar_Pprint.empty
          then
            let uu____5290 = pre body  in
            FStar_Pprint.op_Hat_Hat decl uu____5290
          else
            (let uu____5293 =
               let uu____5294 =
                 let uu____5295 =
                   let uu____5296 = pre body  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5296 comm  in
                 FStar_Pprint.op_Hat_Hat decl uu____5295  in
               let uu____5297 =
                 let uu____5298 =
                   let uu____5299 =
                     let uu____5300 =
                       let uu____5301 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline body
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____5301  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5300
                      in
                   FStar_Pprint.nest (Prims.of_int (2)) uu____5299  in
                 FStar_Pprint.op_Hat_Hat decl uu____5298  in
               FStar_Pprint.ifflat uu____5294 uu____5297  in
             FStar_All.pipe_left FStar_Pprint.group uu____5293)

and (p_typeDecl :
  FStar_Pprint.document ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_5304  ->
      match uu___6_5304 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5327 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5327, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5344 = p_typ_sep false false t  in
          (match uu____5344 with
           | (comm,doc) ->
               let uu____5364 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5364, doc, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordField ps uu____5408 =
            match uu____5408 with
            | (lid1,t) ->
                let uu____5416 =
                  let uu____5421 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t)
                    uu____5421
                   in
                (match uu____5416 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5433 =
              separate_map_last FStar_Pprint.hardline p_recordField
                record_field_decls
               in
            braces_with_nesting uu____5433  in
          let uu____5438 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5438, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5493 =
            match uu____5493 with
            | (uid,t_opt,use_of) ->
                let range =
                  let uu____5513 =
                    let uu____5514 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5514  in
                  FStar_Range.extend_to_end_of_line uu____5513  in
                let uu____5519 =
                  with_comment_sep p_constructorBranch (uid, t_opt, use_of)
                    range
                   in
                (match uu____5519 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____5548 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5548, datacon_doc, jump2)

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
                let uu____5576 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc  in
                FStar_Pprint.group uu____5576  in
              cont kw_lid  in
            let typ =
              let maybe_eq =
                if eq1 then FStar_Pprint.equals else FStar_Pprint.empty  in
              match typ_opt with
              | FStar_Pervasives_Native.None  -> maybe_eq
              | FStar_Pervasives_Native.Some t ->
                  let uu____5583 =
                    let uu____5584 =
                      let uu____5585 = p_typ false false t  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5585 maybe_eq  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5584  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5583
               in
            if bs = []
            then with_kw (fun n1  -> prefix2 n1 typ)
            else
              (let binders = p_binders_list true bs  in
               with_kw
                 (fun n1  ->
                    let uu____5605 =
                      let uu____5606 = FStar_Pprint.flow break1 binders  in
                      prefix2 n1 uu____5606  in
                    prefix2 uu____5605 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5608  ->
      match uu____5608 with
      | (lid,t) ->
          let uu____5616 =
            let uu____5617 = p_lident lid  in
            let uu____5618 =
              let uu____5619 = p_typ ps false t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5619  in
            FStar_Pprint.op_Hat_Hat uu____5617 uu____5618  in
          FStar_Pprint.group uu____5616

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    Prims.bool) -> FStar_Pprint.document)
  =
  fun uu____5621  ->
    match uu____5621 with
    | (uid,t_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5646 =
            let uu____5647 =
              let uu____5648 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5648  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5647  in
          FStar_Pprint.group uu____5646  in
        default_or_map uid_doc
          (fun t  ->
             let uu____5652 =
               let uu____5653 =
                 let uu____5654 =
                   let uu____5655 =
                     let uu____5656 = p_typ false false t  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656
                      in
                   FStar_Pprint.op_Hat_Hat sep uu____5655  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5654  in
               FStar_Pprint.op_Hat_Hat uid_doc uu____5653  in
             FStar_Pprint.group uu____5652) t_opt

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5660  ->
      fun inner_let  ->
        match uu____5660 with
        | (pat,uu____5668) ->
            let uu____5669 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____5721 =
                    let uu____5728 =
                      let uu____5733 =
                        let uu____5734 =
                          let uu____5735 =
                            let uu____5736 = str "by"  in
                            let uu____5738 =
                              let uu____5739 =
                                p_atomicTerm (maybe_unthunk tac)  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____5739
                               in
                            FStar_Pprint.op_Hat_Hat uu____5736 uu____5738  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____5735
                           in
                        FStar_Pprint.group uu____5734  in
                      (t, uu____5733)  in
                    FStar_Pervasives_Native.Some uu____5728  in
                  (pat1, uu____5721)
              | uu____5750 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____5669 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____5776);
                         FStar_Parser_AST.prange = uu____5777;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5794 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____5794 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5800 =
                        if inner_let
                        then
                          let uu____5814 = pats_as_binders_if_possible pats
                             in
                          match uu____5814 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____5837 = pats_as_binders_if_possible pats
                              in
                           match uu____5837 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____5800 with
                       | (terms,style) ->
                           let uu____5864 =
                             let uu____5865 =
                               let uu____5866 =
                                 let uu____5867 = p_lident lid  in
                                 let uu____5868 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____5867
                                   uu____5868
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5866
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____5865  in
                           FStar_All.pipe_left FStar_Pprint.group uu____5864)
                  | uu____5871 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____5879 =
                              let uu____5880 =
                                let uu____5881 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.of_int (2)),
                                         (Prims.of_int (2)))) false false t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____5881
                                 in
                              FStar_Pprint.group uu____5880  in
                            FStar_Pprint.op_Hat_Hat uu____5879 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____5892 =
                        let uu____5893 =
                          let uu____5894 =
                            let uu____5895 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____5895  in
                          FStar_Pprint.group uu____5894  in
                        FStar_Pprint.op_Hat_Hat uu____5893 ascr_doc  in
                      FStar_Pprint.group uu____5892))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5897  ->
      match uu____5897 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____5906 = p_term_sep false false e  in
          (match uu____5906 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____5916 =
                 let uu____5917 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5917  in
               let uu____5918 =
                 let uu____5919 =
                   let uu____5920 =
                     let uu____5921 =
                       let uu____5922 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5922
                        in
                     FStar_Pprint.group uu____5921  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5920  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____5919  in
               FStar_Pprint.ifflat uu____5916 uu____5918)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_5923  ->
    match uu___7_5923 with
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
        let uu____5948 = p_uident uid  in
        let uu____5949 = p_binders true bs  in
        let uu____5951 =
          let uu____5952 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5952  in
        surround_maybe_empty (Prims.of_int (2)) Prims.int_one uu____5948
          uu____5949 uu____5951

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
          let uu____5967 =
            let uu____5968 =
              let uu____5969 =
                let uu____5970 = p_uident uid  in
                let uu____5971 = p_binders true bs  in
                let uu____5973 =
                  let uu____5974 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5974  in
                surround_maybe_empty (Prims.of_int (2)) Prims.int_one
                  uu____5970 uu____5971 uu____5973
                 in
              FStar_Pprint.group uu____5969  in
            let uu____5979 =
              let uu____5980 = str "with"  in
              let uu____5982 =
                let uu____5983 =
                  let uu____5984 =
                    let uu____5985 =
                      let uu____5986 =
                        let uu____5987 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5987
                         in
                      separate_map_last uu____5986 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5985  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5984  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5983  in
              FStar_Pprint.op_Hat_Hat uu____5980 uu____5982  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5968 uu____5979  in
          braces_with_nesting uu____5967

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false ,uu____5991,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e))::[])
          ->
          let uu____6004 =
            let uu____6005 = p_lident lid  in
            let uu____6006 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6005 uu____6006  in
          let uu____6007 = p_simpleTerm ps false e  in
          prefix2 uu____6004 uu____6007
      | uu____6009 ->
          let uu____6010 =
            let uu____6012 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6012
             in
          failwith uu____6010

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6095 =
        match uu____6095 with
        | (kwd,t) ->
            let uu____6106 =
              let uu____6107 = str kwd  in
              let uu____6108 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6107 uu____6108  in
            let uu____6109 = p_simpleTerm ps false t  in
            prefix2 uu____6106 uu____6109
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6116 =
      let uu____6117 =
        let uu____6118 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6119 =
          let uu____6120 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6120  in
        FStar_Pprint.op_Hat_Hat uu____6118 uu____6119  in
      let uu____6122 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6117 uu____6122  in
    let uu____6123 =
      let uu____6124 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6124  in
    FStar_Pprint.op_Hat_Hat uu____6116 uu____6123

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_6125  ->
    match uu___8_6125 with
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
        let uu____6145 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6145 FStar_Pprint.hardline
    | uu____6146 ->
        let uu____6147 =
          let uu____6148 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6148  in
        FStar_Pprint.op_Hat_Hat uu____6147 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_6151  ->
    match uu___9_6151 with
    | FStar_Parser_AST.Rec  ->
        let uu____6152 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6152
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_6154  ->
    match uu___10_6154 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6159,e) -> e
          | uu____6165 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6166 = str "#["  in
        let uu____6168 =
          let uu____6169 = p_term false false t1  in
          let uu____6172 =
            let uu____6173 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6173 break1  in
          FStar_Pprint.op_Hat_Hat uu____6169 uu____6172  in
        FStar_Pprint.op_Hat_Hat uu____6166 uu____6168

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6179 =
          let uu____6180 =
            let uu____6181 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6181  in
          FStar_Pprint.separate_map uu____6180 p_tuplePattern pats  in
        FStar_Pprint.group uu____6179
    | uu____6182 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6191 =
          let uu____6192 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6192 p_constructorPattern pats  in
        FStar_Pprint.group uu____6191
    | uu____6193 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6196;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6201 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6202 = p_constructorPattern hd1  in
        let uu____6203 = p_constructorPattern tl1  in
        infix0 uu____6201 uu____6202 uu____6203
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6205;_},pats)
        ->
        let uu____6211 = p_quident uid  in
        let uu____6212 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6211 uu____6212
    | uu____6213 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6229;
               FStar_Parser_AST.blevel = uu____6230;
               FStar_Parser_AST.aqual = uu____6231;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6240 =
               let uu____6241 = p_ident lid  in
               p_refinement aqual uu____6241 t1 phi  in
             soft_parens_with_nesting uu____6240
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6244;
               FStar_Parser_AST.blevel = uu____6245;
               FStar_Parser_AST.aqual = uu____6246;_},phi))
             ->
             let uu____6252 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6252
         | uu____6253 ->
             let uu____6258 =
               let uu____6259 = p_tuplePattern pat  in
               let uu____6260 =
                 let uu____6261 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6261
                  in
               FStar_Pprint.op_Hat_Hat uu____6259 uu____6260  in
             soft_parens_with_nesting uu____6258)
    | FStar_Parser_AST.PatList pats ->
        let uu____6265 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____6265 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6284 =
          match uu____6284 with
          | (lid,pat) ->
              let uu____6291 = p_qlident lid  in
              let uu____6292 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6291 uu____6292
           in
        let uu____6293 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6293
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6305 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6306 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6307 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____6305
          uu____6306 uu____6307
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6318 =
          let uu____6319 =
            let uu____6320 =
              let uu____6321 = FStar_Ident.text_of_id op  in str uu____6321
               in
            let uu____6323 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6320 uu____6323  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6319  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6318
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6327 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6327 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6335 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6336 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6335 uu____6336
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6338 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6342;
           FStar_Parser_AST.prange = uu____6343;_},uu____6344)
        ->
        let uu____6349 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6349
    | FStar_Parser_AST.PatTuple (uu____6350,false ) ->
        let uu____6357 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6357
    | uu____6358 ->
        let uu____6359 =
          let uu____6361 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6361  in
        failwith uu____6359

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6366;_},uu____6367)
        -> true
    | uu____6374 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6380) -> true
    | uu____6382 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6389 = p_binder' is_atomic b  in
      match uu____6389 with
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
          let uu____6426 =
            let uu____6427 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6428 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6427 uu____6428  in
          (uu____6426, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6434 = p_lident lid  in
          (uu____6434, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6441 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6452;
                   FStar_Parser_AST.blevel = uu____6453;
                   FStar_Parser_AST.aqual = uu____6454;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____6459 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____6459 t1 phi
            | uu____6460 ->
                let t' =
                  let uu____6462 = is_typ_tuple t  in
                  if uu____6462
                  then
                    let uu____6465 = p_tmFormula t  in
                    soft_parens_with_nesting uu____6465
                  else p_tmFormula t  in
                let uu____6468 =
                  let uu____6469 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____6470 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____6469 uu____6470  in
                (uu____6468, t')
             in
          (match uu____6441 with
           | (b',t') ->
               let catf =
                 let uu____6488 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____6488
                 then
                   fun x  ->
                     fun y  ->
                       let uu____6495 =
                         let uu____6496 =
                           let uu____6497 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____6497
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____6496
                          in
                       FStar_Pprint.group uu____6495
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____6502 = cat_with_colon x y  in
                        FStar_Pprint.group uu____6502)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____6507 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____6535;
                  FStar_Parser_AST.blevel = uu____6536;
                  FStar_Parser_AST.aqual = uu____6537;_},phi)
               ->
               let uu____6541 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____6541 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____6562 ->
               if is_atomic
               then
                 let uu____6574 = p_atomicTerm t  in
                 (uu____6574, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____6581 = p_appTerm t  in
                  (uu____6581, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____6592 = p_refinement' aqual_opt binder t phi  in
          match uu____6592 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____6608 -> false
            | FStar_Parser_AST.App uu____6620 -> false
            | FStar_Parser_AST.Op uu____6628 -> false
            | uu____6636 -> true  in
          let uu____6638 = p_noSeqTerm false false phi  in
          match uu____6638 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____6655 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____6655)
                 in
              let jump_break =
                if is_t_atomic then Prims.int_zero else Prims.int_one  in
              let uu____6664 =
                let uu____6665 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____6665 binder  in
              let uu____6666 =
                let uu____6667 = p_appTerm t  in
                let uu____6668 =
                  let uu____6669 =
                    let uu____6670 =
                      let uu____6671 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____6672 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____6671 uu____6672  in
                    FStar_Pprint.group uu____6670  in
                  FStar_Pprint.jump (Prims.of_int (2)) jump_break uu____6669
                   in
                FStar_Pprint.op_Hat_Hat uu____6667 uu____6668  in
              (uu____6664, uu____6666)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____6686 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____6686

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____6690 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6693 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6693)
       in
    if uu____6690
    then FStar_Pprint.underscore
    else (let uu____6698 = FStar_Ident.text_of_id lid  in str uu____6698)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____6701 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____6704 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____6704)
       in
    if uu____6701
    then FStar_Pprint.underscore
    else (let uu____6709 = FStar_Ident.text_of_lid lid  in str uu____6709)

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
          let uu____6730 = FStar_Pprint.op_Hat_Hat doc sep  in
          FStar_Pprint.group uu____6730
        else
          (let uu____6733 =
             let uu____6734 =
               let uu____6735 =
                 let uu____6736 =
                   let uu____6737 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____6737  in
                 FStar_Pprint.op_Hat_Hat doc uu____6736  in
               FStar_Pprint.group uu____6735  in
             let uu____6738 =
               let uu____6739 =
                 let uu____6740 = FStar_Pprint.op_Hat_Hat doc sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6740  in
               FStar_Pprint.op_Hat_Hat comm uu____6739  in
             FStar_Pprint.ifflat uu____6734 uu____6738  in
           FStar_All.pipe_left FStar_Pprint.group uu____6733)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____6748 = p_noSeqTerm true false e1  in
            (match uu____6748 with
             | (comm,t1) ->
                 let uu____6757 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____6758 =
                   let uu____6759 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6759
                    in
                 FStar_Pprint.op_Hat_Hat uu____6757 uu____6758)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6763 =
              let uu____6764 =
                let uu____6765 =
                  let uu____6766 = p_lident x  in
                  let uu____6767 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____6766 uu____6767  in
                let uu____6768 =
                  let uu____6769 = p_noSeqTermAndComment true false e1  in
                  let uu____6772 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____6769 uu____6772  in
                op_Hat_Slash_Plus_Hat uu____6765 uu____6768  in
              FStar_Pprint.group uu____6764  in
            let uu____6773 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6763 uu____6773
        | uu____6774 ->
            let uu____6775 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____6775

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
            let uu____6787 = p_noSeqTerm true false e1  in
            (match uu____6787 with
             | (comm,t1) ->
                 let uu____6800 =
                   let uu____6801 =
                     let uu____6802 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____6802  in
                   let uu____6803 =
                     let uu____6804 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6804
                      in
                   FStar_Pprint.op_Hat_Hat uu____6801 uu____6803  in
                 (comm, uu____6800))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____6808 =
              let uu____6809 =
                let uu____6810 =
                  let uu____6811 =
                    let uu____6812 = p_lident x  in
                    let uu____6813 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____6812 uu____6813  in
                  let uu____6814 =
                    let uu____6815 = p_noSeqTermAndComment true false e1  in
                    let uu____6818 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____6815 uu____6818  in
                  op_Hat_Slash_Plus_Hat uu____6811 uu____6814  in
                FStar_Pprint.group uu____6810  in
              let uu____6819 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6809 uu____6819  in
            (FStar_Pprint.empty, uu____6808)
        | uu____6820 -> p_noSeqTerm ps pb e

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
            let uu____6840 =
              let uu____6841 = p_tmIff e1  in
              let uu____6842 =
                let uu____6843 =
                  let uu____6844 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6844
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6843  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6841 uu____6842  in
            FStar_Pprint.group uu____6840
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____6850 =
              let uu____6851 = p_tmIff e1  in
              let uu____6852 =
                let uu____6853 =
                  let uu____6854 =
                    let uu____6855 = p_typ false false t  in
                    let uu____6858 =
                      let uu____6859 = str "by"  in
                      let uu____6861 = p_typ ps pb (maybe_unthunk tac)  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____6859 uu____6861  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____6855 uu____6858  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6854
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____6853  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6851 uu____6852  in
            FStar_Pprint.group uu____6850
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____6862;_},e1::e2::e3::[])
            ->
            let uu____6869 =
              let uu____6870 =
                let uu____6871 =
                  let uu____6872 = p_atomicTermNotQUident e1  in
                  let uu____6873 =
                    let uu____6874 =
                      let uu____6875 =
                        let uu____6876 = p_term false false e2  in
                        soft_parens_with_nesting uu____6876  in
                      let uu____6879 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6875 uu____6879  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6874  in
                  FStar_Pprint.op_Hat_Hat uu____6872 uu____6873  in
                FStar_Pprint.group uu____6871  in
              let uu____6880 =
                let uu____6881 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6881  in
              FStar_Pprint.op_Hat_Hat uu____6870 uu____6880  in
            FStar_Pprint.group uu____6869
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____6882;_},e1::e2::e3::[])
            ->
            let uu____6889 =
              let uu____6890 =
                let uu____6891 =
                  let uu____6892 = p_atomicTermNotQUident e1  in
                  let uu____6893 =
                    let uu____6894 =
                      let uu____6895 =
                        let uu____6896 = p_term false false e2  in
                        soft_brackets_with_nesting uu____6896  in
                      let uu____6899 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____6895 uu____6899  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6894  in
                  FStar_Pprint.op_Hat_Hat uu____6892 uu____6893  in
                FStar_Pprint.group uu____6891  in
              let uu____6900 =
                let uu____6901 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____6901  in
              FStar_Pprint.op_Hat_Hat uu____6890 uu____6900  in
            FStar_Pprint.group uu____6889
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____6911 =
              let uu____6912 = str "requires"  in
              let uu____6914 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6912 uu____6914  in
            FStar_Pprint.group uu____6911
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____6924 =
              let uu____6925 = str "ensures"  in
              let uu____6927 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6925 uu____6927  in
            FStar_Pprint.group uu____6924
        | FStar_Parser_AST.Attributes es ->
            let uu____6931 =
              let uu____6932 = str "attributes"  in
              let uu____6934 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6932 uu____6934  in
            FStar_Pprint.group uu____6931
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____6939 =
                let uu____6940 =
                  let uu____6941 = str "if"  in
                  let uu____6943 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____6941 uu____6943  in
                let uu____6946 =
                  let uu____6947 = str "then"  in
                  let uu____6949 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____6947 uu____6949  in
                FStar_Pprint.op_Hat_Slash_Hat uu____6940 uu____6946  in
              FStar_Pprint.group uu____6939
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____6953,uu____6954,e31) when
                     is_unit e31 ->
                     let uu____6956 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____6956
                 | uu____6959 -> p_noSeqTermAndComment false false e2  in
               let uu____6962 =
                 let uu____6963 =
                   let uu____6964 = str "if"  in
                   let uu____6966 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____6964 uu____6966  in
                 let uu____6969 =
                   let uu____6970 =
                     let uu____6971 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____6971 e2_doc  in
                   let uu____6973 =
                     let uu____6974 = str "else"  in
                     let uu____6976 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____6974 uu____6976  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____6970 uu____6973  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____6963 uu____6969  in
               FStar_Pprint.group uu____6962)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____6999 =
              let uu____7000 =
                let uu____7001 =
                  let uu____7002 = str "try"  in
                  let uu____7004 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7002 uu____7004  in
                let uu____7007 =
                  let uu____7008 = str "with"  in
                  let uu____7010 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7008 uu____7010  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7001 uu____7007  in
              FStar_Pprint.group uu____7000  in
            let uu____7019 = paren_if (ps || pb)  in uu____7019 uu____6999
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7046 =
              let uu____7047 =
                let uu____7048 =
                  let uu____7049 = str "match"  in
                  let uu____7051 = p_noSeqTermAndComment false false e1  in
                  let uu____7054 = str "with"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7049 uu____7051 uu____7054
                   in
                let uu____7058 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7048 uu____7058  in
              FStar_Pprint.group uu____7047  in
            let uu____7067 = paren_if (ps || pb)  in uu____7067 uu____7046
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7074 =
              let uu____7075 =
                let uu____7076 =
                  let uu____7077 = str "let open"  in
                  let uu____7079 = p_quident uid  in
                  let uu____7080 = str "in"  in
                  FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
                    uu____7077 uu____7079 uu____7080
                   in
                let uu____7084 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7076 uu____7084  in
              FStar_Pprint.group uu____7075  in
            let uu____7086 = paren_if ps  in uu____7086 uu____7074
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7151 is_last =
              match uu____7151 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7185 =
                          let uu____7186 = str "let"  in
                          let uu____7188 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7186 uu____7188
                           in
                        FStar_Pprint.group uu____7185
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7191 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7197 = p_term_sep false false e2  in
                  (match uu____7197 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7207 =
                         if is_last
                         then
                           let uu____7209 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7210 = str "in"  in
                           FStar_Pprint.surround (Prims.of_int (2))
                             Prims.int_one uu____7209 doc_expr1 uu____7210
                         else
                           (let uu____7216 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.of_int (2)) uu____7216)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7207)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = Prims.int_zero
                     then
                       let uu____7267 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - Prims.int_one))
                          in
                       FStar_Pprint.group uu____7267
                     else
                       (let uu____7272 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - Prims.int_one))
                           in
                        FStar_Pprint.group uu____7272)) lbs
               in
            let lbs_doc =
              let uu____7276 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7276  in
            let uu____7277 =
              let uu____7278 =
                let uu____7279 =
                  let uu____7280 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7280
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7279  in
              FStar_Pprint.group uu____7278  in
            let uu____7282 = paren_if ps  in uu____7282 uu____7277
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7289;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7292;
                                                             FStar_Parser_AST.level
                                                               = uu____7293;_})
            when matches_var maybe_x x ->
            let uu____7320 =
              let uu____7321 =
                let uu____7322 = str "function"  in
                let uu____7324 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7322 uu____7324  in
              FStar_Pprint.group uu____7321  in
            let uu____7333 = paren_if (ps || pb)  in uu____7333 uu____7320
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7339 =
              let uu____7340 = str "quote"  in
              let uu____7342 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7340 uu____7342  in
            FStar_Pprint.group uu____7339
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7344 =
              let uu____7345 = str "`"  in
              let uu____7347 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7345 uu____7347  in
            FStar_Pprint.group uu____7344
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7349 =
              let uu____7350 = str "`%"  in
              let uu____7352 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7350 uu____7352  in
            FStar_Pprint.group uu____7349
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7354;
              FStar_Parser_AST.level = uu____7355;_}
            ->
            let uu____7356 =
              let uu____7357 = str "`@"  in
              let uu____7359 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7357 uu____7359  in
            FStar_Pprint.group uu____7356
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7361 =
              let uu____7362 = str "`#"  in
              let uu____7364 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7362 uu____7364  in
            FStar_Pprint.group uu____7361
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7373 = str "calc"  in
              let uu____7375 =
                let uu____7376 =
                  let uu____7377 = p_noSeqTermAndComment false false rel  in
                  let uu____7380 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7377 uu____7380  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7376  in
              FStar_Pprint.op_Hat_Hat uu____7373 uu____7375  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7382 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7383 =
              let uu____7384 =
                let uu____7385 =
                  let uu____7386 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7389 =
                    let uu____7390 = str ";"  in
                    let uu____7392 =
                      let uu____7393 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7393
                       in
                    FStar_Pprint.op_Hat_Hat uu____7390 uu____7392  in
                  FStar_Pprint.op_Hat_Hat uu____7386 uu____7389  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7385  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.of_int (2)))
                uu____7384
               in
            FStar_Pprint.enclose head1 uu____7382 uu____7383
        | uu____7395 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7396  ->
    fun uu____7397  ->
      match uu____7397 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7402 =
            let uu____7403 = p_noSeqTermAndComment false false rel  in
            let uu____7406 =
              let uu____7407 =
                let uu____7408 =
                  let uu____7409 =
                    let uu____7410 = p_noSeqTermAndComment false false just
                       in
                    let uu____7413 =
                      let uu____7414 =
                        let uu____7415 =
                          let uu____7416 =
                            let uu____7417 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7420 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7417 uu____7420  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7416
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7415
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7414
                       in
                    FStar_Pprint.op_Hat_Hat uu____7410 uu____7413  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7409  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7408  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7407  in
            FStar_Pprint.op_Hat_Hat uu____7403 uu____7406  in
          FStar_Pprint.group uu____7402

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_7422  ->
    match uu___11_7422 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7434 =
          let uu____7435 = str "[@"  in
          let uu____7437 =
            let uu____7438 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7439 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7438 uu____7439  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7435 uu____7437  in
        FStar_Pprint.group uu____7434

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
        | FStar_Parser_AST.QForall (bs,(uu____7457,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7491 =
                   let uu____7492 =
                     let uu____7493 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7493 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7492 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7491 term_doc
             | pats ->
                 let uu____7501 =
                   let uu____7502 =
                     let uu____7503 =
                       let uu____7504 =
                         let uu____7505 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7505
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7504 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7508 = p_trigger trigger  in
                     prefix2 uu____7503 uu____7508  in
                   FStar_Pprint.group uu____7502  in
                 prefix2 uu____7501 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____7510,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____7544 =
                   let uu____7545 =
                     let uu____7546 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7546 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.of_int (2))
                     Prims.int_zero uu____7545 binders_doc FStar_Pprint.dot
                    in
                 prefix2 uu____7544 term_doc
             | pats ->
                 let uu____7554 =
                   let uu____7555 =
                     let uu____7556 =
                       let uu____7557 =
                         let uu____7558 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7558
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.of_int (2))
                         Prims.int_zero uu____7557 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7561 = p_trigger trigger  in
                     prefix2 uu____7556 uu____7561  in
                   FStar_Pprint.group uu____7555  in
                 prefix2 uu____7554 term_doc)
        | uu____7562 -> p_simpleTerm ps pb e

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
      let uu____7583 = all_binders_annot t  in
      if uu____7583
      then
        let uu____7586 =
          p_typ_top (Binders ((Prims.of_int (4)), Prims.int_zero, true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____7586
      else
        (let uu____7597 =
           let uu____7598 =
             let uu____7599 =
               p_typ_top (Arrows ((Prims.of_int (2)), (Prims.of_int (2))))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____7599  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7598  in
         FStar_Pprint.group uu____7597)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____7658 = x  in
      match uu____7658 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____7723 = hd1  in
               (match uu____7723 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____7795 = cb  in
      match uu____7795 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____7814 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____7820 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____7820) hd1 tl1
                  in
               cat_with_colon uu____7814 typ)
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
                 FStar_Parser_AST.brange = uu____7899;
                 FStar_Parser_AST.blevel = uu____7900;
                 FStar_Parser_AST.aqual = uu____7901;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____7910 =
                 let uu____7915 = p_ident lid  in
                 p_refinement' aqual uu____7915 t1 phi  in
               FStar_Pervasives_Native.Some uu____7910
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____7922) ->
               let uu____7927 =
                 let uu____7932 =
                   let uu____7933 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____7934 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____7933 uu____7934  in
                 let uu____7935 = p_tmEqNoRefinement t  in
                 (uu____7932, uu____7935)  in
               FStar_Pervasives_Native.Some uu____7927
           | uu____7940 -> FStar_Pervasives_Native.None)
      | uu____7949 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____7962 -> false
      | uu____7974 -> true  in
    let uu____7976 = map_if_all all_binders pats  in
    match uu____7976 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8008 = collapse_pats bs  in
        (uu____8008, (Binders ((Prims.of_int (4)), Prims.int_zero, true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8025 = FStar_List.map p_atomicPattern pats  in
        (uu____8025, (Binders ((Prims.of_int (4)), Prims.int_zero, false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8037 -> str "forall"
    | FStar_Parser_AST.QExists uu____8057 -> str "exists"
    | uu____8077 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_8079  ->
    match uu___12_8079 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8091 =
          let uu____8092 =
            let uu____8093 =
              let uu____8094 = str "pattern"  in
              let uu____8096 =
                let uu____8097 =
                  let uu____8098 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.of_int (2)) Prims.int_zero
                    uu____8098
                   in
                FStar_Pprint.op_Hat_Hat uu____8097 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8094 uu____8096  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8093  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8092  in
        FStar_Pprint.group uu____8091

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8106 = str "\\/"  in
    FStar_Pprint.separate_map uu____8106 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8113 =
      let uu____8114 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8114 p_appTerm pats  in
    FStar_Pprint.group uu____8113

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8126 = p_term_sep false pb e1  in
            (match uu____8126 with
             | (comm,doc) ->
                 let prefix1 =
                   let uu____8135 = str "fun"  in
                   let uu____8137 =
                     let uu____8138 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8138
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8135 uu____8137  in
                 let uu____8139 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8141 =
                       let uu____8142 =
                         let uu____8143 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8143  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8142
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8141
                   else
                     (let uu____8146 = op_Hat_Slash_Plus_Hat prefix1 doc  in
                      FStar_Pprint.group uu____8146)
                    in
                 let uu____8147 = paren_if ps  in uu____8147 uu____8139)
        | uu____8152 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8160  ->
      match uu____8160 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8184 =
                    let uu____8185 =
                      let uu____8186 =
                        let uu____8187 = p_tuplePattern p  in
                        let uu____8188 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8187 uu____8188  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8186
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8185  in
                  FStar_Pprint.group uu____8184
              | FStar_Pervasives_Native.Some f ->
                  let uu____8190 =
                    let uu____8191 =
                      let uu____8192 =
                        let uu____8193 =
                          let uu____8194 =
                            let uu____8195 = p_tuplePattern p  in
                            let uu____8196 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8195
                              uu____8196
                             in
                          FStar_Pprint.group uu____8194  in
                        let uu____8198 =
                          let uu____8199 =
                            let uu____8202 = p_tmFormula f  in
                            [uu____8202; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8199  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8193 uu____8198
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8192
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8191  in
                  FStar_Pprint.hang (Prims.of_int (2)) uu____8190
               in
            let uu____8204 = p_term_sep false pb e  in
            match uu____8204 with
            | (comm,doc) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8214 = op_Hat_Slash_Plus_Hat branch doc  in
                     FStar_Pprint.group uu____8214
                   else
                     (let uu____8217 =
                        let uu____8218 =
                          let uu____8219 =
                            let uu____8220 =
                              let uu____8221 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc uu____8221  in
                            op_Hat_Slash_Plus_Hat branch uu____8220  in
                          FStar_Pprint.group uu____8219  in
                        let uu____8222 =
                          let uu____8223 =
                            let uu____8224 =
                              inline_comment_or_above comm doc
                                FStar_Pprint.empty
                               in
                            jump2 uu____8224  in
                          FStar_Pprint.op_Hat_Hat branch uu____8223  in
                        FStar_Pprint.ifflat uu____8218 uu____8222  in
                      FStar_Pprint.group uu____8217))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8228 =
                       let uu____8229 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8229  in
                     op_Hat_Slash_Plus_Hat branch uu____8228)
                  else op_Hat_Slash_Plus_Hat branch doc
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8240 =
                      let uu____8241 =
                        let uu____8242 =
                          let uu____8243 =
                            let uu____8244 =
                              let uu____8245 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8245  in
                            FStar_Pprint.separate_map uu____8244
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8243
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8242
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8241  in
                    FStar_Pprint.group uu____8240
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8247 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8249;_},e1::e2::[])
        ->
        let uu____8255 = str "<==>"  in
        let uu____8257 = p_tmImplies e1  in
        let uu____8258 = p_tmIff e2  in
        infix0 uu____8255 uu____8257 uu____8258
    | uu____8259 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8261;_},e1::e2::[])
        ->
        let uu____8267 = str "==>"  in
        let uu____8269 =
          p_tmArrow (Arrows ((Prims.of_int (2)), (Prims.of_int (2)))) false
            p_tmFormula e1
           in
        let uu____8275 = p_tmImplies e2  in
        infix0 uu____8267 uu____8269 uu____8275
    | uu____8276 ->
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
          let uu____8290 =
            FStar_List.splitAt ((FStar_List.length terms) - Prims.int_one)
              terms
             in
          match uu____8290 with
          | (terms',last1) ->
              let uu____8310 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8345 =
                      let uu____8346 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8346
                       in
                    let uu____8347 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8345, uu____8347)
                | Binders (n1,ln,parens1) ->
                    let uu____8361 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8369 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8361, break1, uu____8369)
                 in
              (match uu____8310 with
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
                    | _8402 when _8402 = Prims.int_one -> FStar_List.hd terms
                    | uu____8403 ->
                        let uu____8404 =
                          let uu____8405 =
                            let uu____8406 =
                              let uu____8407 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8408 =
                                let uu____8409 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8409
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8407 uu____8408
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8406  in
                          let uu____8410 =
                            let uu____8411 =
                              let uu____8412 =
                                let uu____8413 =
                                  let uu____8414 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8414  in
                                let uu____8415 =
                                  let uu____8416 =
                                    let uu____8417 =
                                      let uu____8418 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8419 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8425 =
                                               FStar_Pprint.hang
                                                 (Prims.of_int (2)) x
                                                in
                                             FStar_Pprint.align uu____8425)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8418
                                        uu____8419
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8417
                                     in
                                  jump2 uu____8416  in
                                FStar_Pprint.ifflat uu____8413 uu____8415  in
                              FStar_Pprint.group uu____8412  in
                            let uu____8427 =
                              let uu____8428 =
                                let uu____8429 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8429  in
                              FStar_Pprint.align uu____8428  in
                            FStar_Pprint.prefix n1 Prims.int_one uu____8411
                              uu____8427
                             in
                          FStar_Pprint.ifflat uu____8405 uu____8410  in
                        FStar_Pprint.group uu____8404))

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
            | Arrows uu____8443 -> p_tmArrow' p_Tm e
            | Binders uu____8450 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8473 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8479 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8473 uu____8479
      | uu____8482 -> let uu____8483 = p_Tm e  in [uu____8483]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8536 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____8562 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8536 uu____8562
        | uu____8585 ->
            let uu____8586 =
              let uu____8597 = p_Tm1 e1  in
              (uu____8597, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____8586]
         in
      let fold_fun bs x =
        let uu____8695 = x  in
        match uu____8695 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____8827 = hd1  in
                 (match uu____8827 with
                  | (b2s,t2,uu____8856) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____8958 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9015 = cb  in
        match uu____9015 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9044 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9055 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9061 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9061) hd1 tl1
                         in
                      f uu____9055 typ))
         in
      let binders =
        let uu____9077 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9077  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9140 =
        let uu____9141 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9141 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9140  in
    let disj =
      let uu____9144 =
        let uu____9145 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9145 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9144  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9165;_},e1::e2::[])
        ->
        let uu____9171 = p_tmDisjunction e1  in
        let uu____9176 = let uu____9181 = p_tmConjunction e2  in [uu____9181]
           in
        FStar_List.append uu____9171 uu____9176
    | uu____9190 -> let uu____9191 = p_tmConjunction e  in [uu____9191]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9201;_},e1::e2::[])
        ->
        let uu____9207 = p_tmConjunction e1  in
        let uu____9210 = let uu____9213 = p_tmTuple e2  in [uu____9213]  in
        FStar_List.append uu____9207 uu____9210
    | uu____9214 -> let uu____9215 = p_tmTuple e  in [uu____9215]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9232 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9232
          (fun uu____9240  ->
             match uu____9240 with | (e1,uu____9246) -> p_tmEq e1) args
    | uu____9247 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc  ->
        if mine <= curr
        then doc
        else
          (let uu____9256 =
             let uu____9257 = FStar_Pprint.op_Hat_Hat doc FStar_Pprint.rparen
                in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9257  in
           FStar_Pprint.group uu____9256)

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
               (let uu____9276 = FStar_Ident.text_of_id op  in
                uu____9276 = "="))
              ||
              (let uu____9281 = FStar_Ident.text_of_id op  in
               uu____9281 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9287 = levels op1  in
            (match uu____9287 with
             | (left1,mine,right1) ->
                 let uu____9306 =
                   let uu____9307 = FStar_All.pipe_left str op1  in
                   let uu____9309 = p_tmEqWith' p_X left1 e1  in
                   let uu____9310 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9307 uu____9309 uu____9310  in
                 paren_if_gt curr mine uu____9306)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9311;_},e1::e2::[])
            ->
            let uu____9317 =
              let uu____9318 = p_tmEqWith p_X e1  in
              let uu____9319 =
                let uu____9320 =
                  let uu____9321 =
                    let uu____9322 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9322  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9321  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9320  in
              FStar_Pprint.op_Hat_Hat uu____9318 uu____9319  in
            FStar_Pprint.group uu____9317
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9323;_},e1::[])
            ->
            let uu____9328 = levels "-"  in
            (match uu____9328 with
             | (left1,mine,right1) ->
                 let uu____9348 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9348)
        | uu____9349 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9397)::(e2,uu____9399)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9419 = is_list e  in Prims.op_Negation uu____9419)
              ->
              let op = "::"  in
              let uu____9424 = levels op  in
              (match uu____9424 with
               | (left1,mine,right1) ->
                   let uu____9443 =
                     let uu____9444 = str op  in
                     let uu____9445 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9447 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9444 uu____9445 uu____9447  in
                   paren_if_gt curr mine uu____9443)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9466 = levels op  in
              (match uu____9466 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9500 = p_binder false b  in
                         let uu____9502 =
                           let uu____9503 =
                             let uu____9504 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9504 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9503
                            in
                         FStar_Pprint.op_Hat_Hat uu____9500 uu____9502
                     | FStar_Util.Inr t ->
                         let uu____9506 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____9508 =
                           let uu____9509 =
                             let uu____9510 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9510 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9509
                            in
                         FStar_Pprint.op_Hat_Hat uu____9506 uu____9508
                      in
                   let uu____9511 =
                     let uu____9512 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____9517 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____9512 uu____9517  in
                   paren_if_gt curr mine uu____9511)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____9519;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____9549 = levels op  in
              (match uu____9549 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____9569 = str op  in
                     let uu____9570 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____9572 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____9569 uu____9570 uu____9572
                   else
                     (let uu____9576 =
                        let uu____9577 = str op  in
                        let uu____9578 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____9580 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____9577 uu____9578 uu____9580  in
                      paren_if_gt curr mine uu____9576))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____9589 = levels op1  in
              (match uu____9589 with
               | (left1,mine,right1) ->
                   let uu____9608 =
                     let uu____9609 = str op1  in
                     let uu____9610 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9612 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9609 uu____9610 uu____9612  in
                   paren_if_gt curr mine uu____9608)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____9632 =
                let uu____9633 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____9634 =
                  let uu____9635 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____9635 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____9633 uu____9634  in
              braces_with_nesting uu____9632
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____9640;_},e1::[])
              ->
              let uu____9645 =
                let uu____9646 = str "~"  in
                let uu____9648 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____9646 uu____9648  in
              FStar_Pprint.group uu____9645
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____9650;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____9659 = levels op  in
                   (match uu____9659 with
                    | (left1,mine,right1) ->
                        let uu____9678 =
                          let uu____9679 = str op  in
                          let uu____9680 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____9682 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____9679 uu____9680 uu____9682  in
                        paren_if_gt curr mine uu____9678)
               | uu____9684 -> p_X e)
          | uu____9685 -> p_X e

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
        let uu____9692 =
          let uu____9693 = p_lident lid  in
          let uu____9694 =
            let uu____9695 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9695  in
          FStar_Pprint.op_Hat_Slash_Hat uu____9693 uu____9694  in
        FStar_Pprint.group uu____9692
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____9698 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____9700 = p_appTerm e  in
    let uu____9701 =
      let uu____9702 =
        let uu____9703 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____9703 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9702  in
    FStar_Pprint.op_Hat_Hat uu____9700 uu____9701

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____9709 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____9709 t phi
      | FStar_Parser_AST.TAnnotated uu____9710 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____9716 ->
          let uu____9717 =
            let uu____9719 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9719
             in
          failwith uu____9717
      | FStar_Parser_AST.TVariable uu____9722 ->
          let uu____9723 =
            let uu____9725 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9725
             in
          failwith uu____9723
      | FStar_Parser_AST.NoName uu____9728 ->
          let uu____9729 =
            let uu____9731 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____9731
             in
          failwith uu____9729

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____9735  ->
      match uu____9735 with
      | (lid,e) ->
          let uu____9743 =
            let uu____9744 = p_qlident lid  in
            let uu____9745 =
              let uu____9746 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____9746
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____9744 uu____9745  in
          FStar_Pprint.group uu____9743

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____9749 when is_general_application e ->
        let uu____9756 = head_and_args e  in
        (match uu____9756 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____9803 = p_argTerm e1  in
                  let uu____9804 =
                    let uu____9805 =
                      let uu____9806 =
                        let uu____9807 = str "`"  in
                        let uu____9809 =
                          let uu____9810 = p_indexingTerm head1  in
                          let uu____9811 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____9810 uu____9811  in
                        FStar_Pprint.op_Hat_Hat uu____9807 uu____9809  in
                      FStar_Pprint.group uu____9806  in
                    let uu____9813 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9805 uu____9813  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9803 uu____9804
              | uu____9814 ->
                  let uu____9821 =
                    let uu____9832 = FStar_ST.op_Bang should_print_fs_typ_app
                       in
                    if uu____9832
                    then
                      let uu____9866 =
                        FStar_Util.take
                          (fun uu____9890  ->
                             match uu____9890 with
                             | (uu____9896,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____9866 with
                      | (fs_typ_args,args1) ->
                          let uu____9934 =
                            let uu____9935 = p_indexingTerm head1  in
                            let uu____9936 =
                              let uu____9937 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.of_int (2))
                                Prims.int_zero FStar_Pprint.empty
                                FStar_Pprint.langle uu____9937
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____9935 uu____9936  in
                          (uu____9934, args1)
                    else
                      (let uu____9952 = p_indexingTerm head1  in
                       (uu____9952, args))
                     in
                  (match uu____9821 with
                   | (head_doc,args1) ->
                       let uu____9973 =
                         let uu____9974 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.of_int (2))
                           Prims.int_zero head_doc uu____9974 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____9973)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____9996 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____9996)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10015 =
               let uu____10016 = p_quident lid  in
               let uu____10017 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10016 uu____10017  in
             FStar_Pprint.group uu____10015
         | hd1::tl1 ->
             let uu____10034 =
               let uu____10035 =
                 let uu____10036 =
                   let uu____10037 = p_quident lid  in
                   let uu____10038 = p_argTerm hd1  in
                   prefix2 uu____10037 uu____10038  in
                 FStar_Pprint.group uu____10036  in
               let uu____10039 =
                 let uu____10040 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10040  in
               FStar_Pprint.op_Hat_Hat uu____10035 uu____10039  in
             FStar_Pprint.group uu____10034)
    | uu____10045 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10056 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one
            FStar_Pprint.langle uu____10056 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10060 = str "#"  in
        let uu____10062 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10060 uu____10062
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10065 = str "#["  in
        let uu____10067 =
          let uu____10068 = p_indexingTerm t  in
          let uu____10069 =
            let uu____10070 = str "]"  in
            let uu____10072 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10070 uu____10072  in
          FStar_Pprint.op_Hat_Hat uu____10068 uu____10069  in
        FStar_Pprint.op_Hat_Hat uu____10065 uu____10067
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10075  ->
    match uu____10075 with | (e,uu____10081) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10086;_},e1::e2::[])
          ->
          let uu____10092 =
            let uu____10093 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10094 =
              let uu____10095 =
                let uu____10096 = p_term false false e2  in
                soft_parens_with_nesting uu____10096  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10095  in
            FStar_Pprint.op_Hat_Hat uu____10093 uu____10094  in
          FStar_Pprint.group uu____10092
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10099;_},e1::e2::[])
          ->
          let uu____10105 =
            let uu____10106 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10107 =
              let uu____10108 =
                let uu____10109 = p_term false false e2  in
                soft_brackets_with_nesting uu____10109  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10108  in
            FStar_Pprint.op_Hat_Hat uu____10106 uu____10107  in
          FStar_Pprint.group uu____10105
      | uu____10112 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10117 = p_quident lid  in
        let uu____10118 =
          let uu____10119 =
            let uu____10120 = p_term false false e1  in
            soft_parens_with_nesting uu____10120  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10119  in
        FStar_Pprint.op_Hat_Hat uu____10117 uu____10118
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10128 =
          let uu____10129 = FStar_Ident.text_of_id op  in str uu____10129  in
        let uu____10131 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10128 uu____10131
    | uu____10132 -> p_atomicTermNotQUident e

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
         | uu____10145 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10154 =
          let uu____10155 = FStar_Ident.text_of_id op  in str uu____10155  in
        let uu____10157 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10154 uu____10157
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10161 =
          let uu____10162 =
            let uu____10163 =
              let uu____10164 = FStar_Ident.text_of_id op  in str uu____10164
               in
            let uu____10166 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10163 uu____10166  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10162  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10161
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10181 = all_explicit args  in
        if uu____10181
        then
          let uu____10184 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10185 =
            let uu____10186 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10187 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10186 p_tmEq uu____10187  in
          let uu____10194 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10184
            uu____10185 uu____10194
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10216 =
                 let uu____10217 = p_quident lid  in
                 let uu____10218 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10217 uu____10218  in
               FStar_Pprint.group uu____10216
           | hd1::tl1 ->
               let uu____10235 =
                 let uu____10236 =
                   let uu____10237 =
                     let uu____10238 = p_quident lid  in
                     let uu____10239 = p_argTerm hd1  in
                     prefix2 uu____10238 uu____10239  in
                   FStar_Pprint.group uu____10237  in
                 let uu____10240 =
                   let uu____10241 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10241  in
                 FStar_Pprint.op_Hat_Hat uu____10236 uu____10240  in
               FStar_Pprint.group uu____10235)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10248 =
          let uu____10249 = p_atomicTermNotQUident e1  in
          let uu____10250 =
            let uu____10251 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10251  in
          FStar_Pprint.prefix (Prims.of_int (2)) Prims.int_zero uu____10249
            uu____10250
           in
        FStar_Pprint.group uu____10248
    | uu____10254 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10259 = p_quident constr_lid  in
        let uu____10260 =
          let uu____10261 =
            let uu____10262 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10262  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10261  in
        FStar_Pprint.op_Hat_Hat uu____10259 uu____10260
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10264 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10264 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10266 = p_term_sep false false e1  in
        (match uu____10266 with
         | (comm,t) ->
             let doc = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc
             else
               (let uu____10279 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc  in
                FStar_Pprint.op_Hat_Hat comm uu____10279))
    | uu____10280 when is_array e ->
        let es = extract_from_list e  in
        let uu____10284 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10285 =
          let uu____10286 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10286
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10291 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10284
          uu____10285 uu____10291
    | uu____10294 when is_list e ->
        let uu____10295 =
          let uu____10296 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10297 = extract_from_list e  in
          separate_map_or_flow_last uu____10296
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10297
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero
          FStar_Pprint.lbracket uu____10295 FStar_Pprint.rbracket
    | uu____10306 when is_lex_list e ->
        let uu____10307 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10308 =
          let uu____10309 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10310 = extract_from_list e  in
          separate_map_or_flow_last uu____10309
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10310
           in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_one uu____10307
          uu____10308 FStar_Pprint.rbracket
    | uu____10319 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10323 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10324 =
          let uu____10325 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10325 p_appTerm es  in
        FStar_Pprint.surround (Prims.of_int (2)) Prims.int_zero uu____10323
          uu____10324 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10335 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10338 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10335 uu____10338
    | FStar_Parser_AST.Op (op,args) when
        let uu____10347 = handleable_op op args  in
        Prims.op_Negation uu____10347 ->
        let uu____10349 =
          let uu____10351 =
            let uu____10353 = FStar_Ident.text_of_id op  in
            let uu____10355 =
              let uu____10357 =
                let uu____10359 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10359
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10357  in
            Prims.op_Hat uu____10353 uu____10355  in
          Prims.op_Hat "Operation " uu____10351  in
        failwith uu____10349
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10366 = p_term false false e  in
        soft_parens_with_nesting uu____10366
    | FStar_Parser_AST.Const uu____10369 ->
        let uu____10370 = p_term false false e  in
        soft_parens_with_nesting uu____10370
    | FStar_Parser_AST.Op uu____10373 ->
        let uu____10380 = p_term false false e  in
        soft_parens_with_nesting uu____10380
    | FStar_Parser_AST.Tvar uu____10383 ->
        let uu____10384 = p_term false false e  in
        soft_parens_with_nesting uu____10384
    | FStar_Parser_AST.Var uu____10387 ->
        let uu____10388 = p_term false false e  in
        soft_parens_with_nesting uu____10388
    | FStar_Parser_AST.Name uu____10391 ->
        let uu____10392 = p_term false false e  in
        soft_parens_with_nesting uu____10392
    | FStar_Parser_AST.Construct uu____10395 ->
        let uu____10406 = p_term false false e  in
        soft_parens_with_nesting uu____10406
    | FStar_Parser_AST.Abs uu____10409 ->
        let uu____10416 = p_term false false e  in
        soft_parens_with_nesting uu____10416
    | FStar_Parser_AST.App uu____10419 ->
        let uu____10426 = p_term false false e  in
        soft_parens_with_nesting uu____10426
    | FStar_Parser_AST.Let uu____10429 ->
        let uu____10450 = p_term false false e  in
        soft_parens_with_nesting uu____10450
    | FStar_Parser_AST.LetOpen uu____10453 ->
        let uu____10458 = p_term false false e  in
        soft_parens_with_nesting uu____10458
    | FStar_Parser_AST.Seq uu____10461 ->
        let uu____10466 = p_term false false e  in
        soft_parens_with_nesting uu____10466
    | FStar_Parser_AST.Bind uu____10469 ->
        let uu____10476 = p_term false false e  in
        soft_parens_with_nesting uu____10476
    | FStar_Parser_AST.If uu____10479 ->
        let uu____10486 = p_term false false e  in
        soft_parens_with_nesting uu____10486
    | FStar_Parser_AST.Match uu____10489 ->
        let uu____10504 = p_term false false e  in
        soft_parens_with_nesting uu____10504
    | FStar_Parser_AST.TryWith uu____10507 ->
        let uu____10522 = p_term false false e  in
        soft_parens_with_nesting uu____10522
    | FStar_Parser_AST.Ascribed uu____10525 ->
        let uu____10534 = p_term false false e  in
        soft_parens_with_nesting uu____10534
    | FStar_Parser_AST.Record uu____10537 ->
        let uu____10550 = p_term false false e  in
        soft_parens_with_nesting uu____10550
    | FStar_Parser_AST.Project uu____10553 ->
        let uu____10558 = p_term false false e  in
        soft_parens_with_nesting uu____10558
    | FStar_Parser_AST.Product uu____10561 ->
        let uu____10568 = p_term false false e  in
        soft_parens_with_nesting uu____10568
    | FStar_Parser_AST.Sum uu____10571 ->
        let uu____10582 = p_term false false e  in
        soft_parens_with_nesting uu____10582
    | FStar_Parser_AST.QForall uu____10585 ->
        let uu____10604 = p_term false false e  in
        soft_parens_with_nesting uu____10604
    | FStar_Parser_AST.QExists uu____10607 ->
        let uu____10626 = p_term false false e  in
        soft_parens_with_nesting uu____10626
    | FStar_Parser_AST.Refine uu____10629 ->
        let uu____10634 = p_term false false e  in
        soft_parens_with_nesting uu____10634
    | FStar_Parser_AST.NamedTyp uu____10637 ->
        let uu____10642 = p_term false false e  in
        soft_parens_with_nesting uu____10642
    | FStar_Parser_AST.Requires uu____10645 ->
        let uu____10653 = p_term false false e  in
        soft_parens_with_nesting uu____10653
    | FStar_Parser_AST.Ensures uu____10656 ->
        let uu____10664 = p_term false false e  in
        soft_parens_with_nesting uu____10664
    | FStar_Parser_AST.Attributes uu____10667 ->
        let uu____10670 = p_term false false e  in
        soft_parens_with_nesting uu____10670
    | FStar_Parser_AST.Quote uu____10673 ->
        let uu____10678 = p_term false false e  in
        soft_parens_with_nesting uu____10678
    | FStar_Parser_AST.VQuote uu____10681 ->
        let uu____10682 = p_term false false e  in
        soft_parens_with_nesting uu____10682
    | FStar_Parser_AST.Antiquote uu____10685 ->
        let uu____10686 = p_term false false e  in
        soft_parens_with_nesting uu____10686
    | FStar_Parser_AST.CalcProof uu____10689 ->
        let uu____10698 = p_term false false e  in
        soft_parens_with_nesting uu____10698

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_10701  ->
    match uu___15_10701 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____10713) ->
        let uu____10716 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____10716
    | FStar_Const.Const_bytearray (bytes,uu____10718) ->
        let uu____10723 =
          let uu____10724 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____10724  in
        let uu____10725 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____10723 uu____10725
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_10748 =
          match uu___13_10748 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_10755 =
          match uu___14_10755 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____10770  ->
               match uu____10770 with
               | (s,w) ->
                   let uu____10777 = signedness s  in
                   let uu____10778 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____10777 uu____10778)
            sign_width_opt
           in
        let uu____10779 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____10779 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____10783 = FStar_Range.string_of_range r  in str uu____10783
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____10787 = p_quident lid  in
        let uu____10788 =
          let uu____10789 =
            let uu____10790 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10790  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10789  in
        FStar_Pprint.op_Hat_Hat uu____10787 uu____10788

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____10793 = str "u#"  in
    let uu____10795 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____10793 uu____10795

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10797;_},u1::u2::[])
        ->
        let uu____10803 =
          let uu____10804 = p_universeFrom u1  in
          let uu____10805 =
            let uu____10806 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____10806  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10804 uu____10805  in
        FStar_Pprint.group uu____10803
    | FStar_Parser_AST.App uu____10807 ->
        let uu____10814 = head_and_args u  in
        (match uu____10814 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____10840 =
                    let uu____10841 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____10842 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____10850  ->
                           match uu____10850 with
                           | (u1,uu____10856) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____10841 uu____10842  in
                  FStar_Pprint.group uu____10840
              | uu____10857 ->
                  let uu____10858 =
                    let uu____10860 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____10860
                     in
                  failwith uu____10858))
    | uu____10863 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10889 = FStar_Ident.text_of_id id1  in str uu____10889
    | FStar_Parser_AST.Paren u1 ->
        let uu____10892 = p_universeFrom u1  in
        soft_parens_with_nesting uu____10892
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____10893;_},uu____10894::uu____10895::[])
        ->
        let uu____10899 = p_universeFrom u  in
        soft_parens_with_nesting uu____10899
    | FStar_Parser_AST.App uu____10900 ->
        let uu____10907 = p_universeFrom u  in
        soft_parens_with_nesting uu____10907
    | uu____10908 ->
        let uu____10909 =
          let uu____10911 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____10911
           in
        failwith uu____10909

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
       | FStar_Parser_AST.Module (uu____11000,decls) ->
           let uu____11006 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11006
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11015,decls,uu____11017) ->
           let uu____11024 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11024
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11084  ->
         match uu____11084 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11106)) -> false
      | ([],uu____11110) -> false
      | uu____11114 -> true  in
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
        | FStar_Parser_AST.Module (uu____11163,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11169,decls,uu____11171) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11223 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11236;
                 FStar_Parser_AST.quals = uu____11237;
                 FStar_Parser_AST.attrs = uu____11238;_}::uu____11239 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11243 =
                   let uu____11246 =
                     let uu____11249 = FStar_List.tl ds  in d :: uu____11249
                      in
                   d0 :: uu____11246  in
                 (uu____11243, (d0.FStar_Parser_AST.drange))
             | uu____11254 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11223 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11311 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos Prims.int_zero Prims.int_one
                      uu____11311 dummy_meta FStar_Pprint.empty false true
                     in
                  let doc =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11420 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc  in
                   (uu____11420, comments1))))))
  