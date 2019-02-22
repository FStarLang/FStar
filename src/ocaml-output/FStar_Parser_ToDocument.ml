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
            let uu____99 = let uu____102 = f x  in uu____102 :: acc  in
            aux xs uu____99
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
            let uu____169 = f x  in
            (match uu____169 with
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
          let uu____225 = f x  in if uu____225 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___27_258  ->
         match uu___27_258 with
         | (uu____264,FStar_Parser_AST.Nothing ) -> true
         | uu____266 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____317 'Auu____318 .
    Prims.bool -> ('Auu____317 -> 'Auu____318) -> 'Auu____317 -> 'Auu____318
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
  'Auu____428 'Auu____429 .
    'Auu____428 ->
      ('Auu____429 -> 'Auu____428) ->
        'Auu____429 FStar_Pervasives_Native.option -> 'Auu____428
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
  'Auu____542 .
    FStar_Pprint.document ->
      ('Auu____542 -> FStar_Pprint.document) ->
        'Auu____542 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____567 =
          let uu____568 =
            let uu____569 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____569  in
          FStar_Pprint.separate_map uu____568 f l  in
        FStar_Pprint.group uu____567
  
let precede_break_separate_map :
  'Auu____581 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____581 -> FStar_Pprint.document) ->
          'Auu____581 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____611 =
            let uu____612 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____613 =
              let uu____614 = FStar_List.hd l  in
              FStar_All.pipe_right uu____614 f  in
            FStar_Pprint.precede uu____612 uu____613  in
          let uu____615 =
            let uu____616 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____622 =
                   let uu____623 =
                     let uu____624 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____624  in
                   FStar_Pprint.op_Hat_Hat sep uu____623  in
                 FStar_Pprint.op_Hat_Hat break1 uu____622) uu____616
             in
          FStar_Pprint.op_Hat_Hat uu____611 uu____615
  
let concat_break_map :
  'Auu____632 .
    ('Auu____632 -> FStar_Pprint.document) ->
      'Auu____632 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____652 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____656 = f x  in FStar_Pprint.op_Hat_Hat uu____656 break1)
          l
         in
      FStar_Pprint.group uu____652
  
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
    let uu____719 = str "begin"  in
    let uu____721 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____719 contents uu____721
  
let separate_map_last :
  'Auu____734 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____734 -> FStar_Pprint.document) ->
        'Auu____734 Prims.list -> FStar_Pprint.document
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
  'Auu____792 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____792 -> FStar_Pprint.document) ->
        'Auu____792 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____824 =
          let uu____825 =
            let uu____826 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____826  in
          separate_map_last uu____825 f l  in
        FStar_Pprint.group uu____824
  
let separate_map_or_flow :
  'Auu____836 .
    FStar_Pprint.document ->
      ('Auu____836 -> FStar_Pprint.document) ->
        'Auu____836 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____874 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____874 -> FStar_Pprint.document) ->
        'Auu____874 Prims.list -> FStar_Pprint.document
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
  'Auu____932 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____932 -> FStar_Pprint.document) ->
        'Auu____932 Prims.list -> FStar_Pprint.document
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
              let uu____1014 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____1014
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1036 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1036 -> FStar_Pprint.document) ->
                  'Auu____1036 Prims.list -> FStar_Pprint.document
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
                    (let uu____1095 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1095
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1115 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1115 -> FStar_Pprint.document) ->
                  'Auu____1115 Prims.list -> FStar_Pprint.document
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
                    (let uu____1174 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1174
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1193  ->
    match uu____1193 with
    | (comment,keywords) ->
        let uu____1227 =
          let uu____1228 =
            let uu____1231 = str comment  in
            let uu____1232 =
              let uu____1235 =
                let uu____1238 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1249  ->
                       match uu____1249 with
                       | (k,v1) ->
                           let uu____1262 =
                             let uu____1265 = str k  in
                             let uu____1266 =
                               let uu____1269 =
                                 let uu____1272 = str v1  in [uu____1272]  in
                               FStar_Pprint.rarrow :: uu____1269  in
                             uu____1265 :: uu____1266  in
                           FStar_Pprint.concat uu____1262) keywords
                   in
                [uu____1238]  in
              FStar_Pprint.space :: uu____1235  in
            uu____1231 :: uu____1232  in
          FStar_Pprint.concat uu____1228  in
        FStar_Pprint.group uu____1227
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1282 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1298 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1298
      | uu____1301 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1352::(e2,uu____1354)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1377 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1401,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1412,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1433 = extract_from_list e2  in e1 :: uu____1433
    | uu____1436 ->
        let uu____1437 =
          let uu____1439 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1439  in
        failwith uu____1437
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1453;
           FStar_Parser_AST.level = uu____1454;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1456 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1468;
           FStar_Parser_AST.level = uu____1469;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1471;
                                                         FStar_Parser_AST.level
                                                           = uu____1472;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1474;
                                                    FStar_Parser_AST.level =
                                                      uu____1475;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1477;
                FStar_Parser_AST.level = uu____1478;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1480;
           FStar_Parser_AST.level = uu____1481;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1483 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1495 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1496;
           FStar_Parser_AST.range = uu____1497;
           FStar_Parser_AST.level = uu____1498;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1499;
                                                         FStar_Parser_AST.range
                                                           = uu____1500;
                                                         FStar_Parser_AST.level
                                                           = uu____1501;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1503;
                                                    FStar_Parser_AST.level =
                                                      uu____1504;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1505;
                FStar_Parser_AST.range = uu____1506;
                FStar_Parser_AST.level = uu____1507;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1509;
           FStar_Parser_AST.level = uu____1510;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1512 = extract_from_ref_set e1  in
        let uu____1515 = extract_from_ref_set e2  in
        FStar_List.append uu____1512 uu____1515
    | uu____1518 ->
        let uu____1519 =
          let uu____1521 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1521  in
        failwith uu____1519
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1533 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1533
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1542 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1542
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1553 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1553 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1563 = FStar_Ident.text_of_id op  in uu____1563 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1633 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1653 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1664 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1675 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___28_1701  ->
    match uu___28_1701 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___29_1736  ->
      match uu___29_1736 with
      | FStar_Util.Inl c ->
          let uu____1749 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1749 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1765 .
    Prims.string ->
      ('Auu____1765 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____1789  ->
      match uu____1789 with
      | (assoc_levels,tokens) ->
          let uu____1821 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1821 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___30_1993 =
    match uu___30_1993 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2043  ->
         match uu____2043 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2118 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2118 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2170) ->
          assoc_levels
      | uu____2208 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2241 . ('Auu____2241 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2290 =
        FStar_List.tryFind
          (fun uu____2326  ->
             match uu____2326 with
             | (uu____2343,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2290 with
      | FStar_Pervasives_Native.Some ((uu____2372,l1,uu____2374),uu____2375)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2425 =
            let uu____2427 =
              let uu____2429 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2429  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2427
             in
          failwith uu____2425
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2464 = assign_levels level_associativity_spec op  in
    match uu____2464 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2523 =
      let uu____2526 =
        let uu____2532 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2532  in
      FStar_List.tryFind uu____2526 operatorInfix0ad12  in
    uu____2523 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2599 =
      let uu____2614 =
        let uu____2632 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2632  in
      FStar_List.tryFind uu____2614 opinfix34  in
    uu____2599 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2698 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2698
    then (Prims.parse_int "1")
    else
      (let uu____2711 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2711
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2757 . FStar_Ident.ident -> 'Auu____2757 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2775 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2775 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2784 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2784
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2806 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2806 [".()<-"; ".[]<-"]
      | uu____2814 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2860 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2913 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2956 -> true
      | uu____2962 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2995 = FStar_List.for_all is_binder_annot bs  in
          if uu____2995
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____3010 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____3015 = all_binders e (Prims.parse_int "0")  in
    match uu____3015 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3054 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3054
  
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
  'Auu____3214 .
    ('Auu____3214 -> FStar_Pprint.document) ->
      'Auu____3214 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3256 = FStar_ST.op_Bang comment_stack  in
          match uu____3256 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3327 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3327 FStar_Pprint.hardline  in
              let uu____3328 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3328
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3370 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3370 print_pos lookahead_pos))
              else
                (let uu____3373 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3373))
           in
        let uu____3376 =
          let uu____3382 =
            let uu____3383 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3383  in
          let uu____3384 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3382 uu____3384  in
        match uu____3376 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3393 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3393
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3405 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3405)
  
let with_comment_sep :
  'Auu____3417 'Auu____3418 .
    ('Auu____3417 -> 'Auu____3418) ->
      'Auu____3417 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3418)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3464 = FStar_ST.op_Bang comment_stack  in
          match uu____3464 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3535 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3535
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3577 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3581 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3581)
                     in
                  comments_before_pos uu____3577 print_pos lookahead_pos))
              else
                (let uu____3584 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3584))
           in
        let uu____3587 =
          let uu____3593 =
            let uu____3594 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3594  in
          let uu____3595 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3593 uu____3595  in
        match uu____3587 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3608 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3608
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
                let uu____3661 = FStar_ST.op_Bang comment_stack  in
                match uu____3661 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3755 =
                          let uu____3757 =
                            let uu____3759 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3759  in
                          uu____3757 - lbegin  in
                        max k uu____3755  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3764 =
                          let uu____3765 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3766 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3765 uu____3766  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3764  in
                      let uu____3767 =
                        let uu____3769 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3769  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3767 pos meta_decl doc2 true init1))
                | uu____3772 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3785 = FStar_Range.line_of_pos pos  in
                         uu____3785 - lbegin  in
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
                       let uu____3827 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3827)
  
let separate_map_with_comments :
  'Auu____3841 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3841 -> FStar_Pprint.document) ->
          'Auu____3841 Prims.list ->
            ('Auu____3841 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3900 x =
              match uu____3900 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3919 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3919 meta_decl doc1 false false
                     in
                  let uu____3923 =
                    let uu____3925 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3925  in
                  let uu____3926 =
                    let uu____3927 =
                      let uu____3928 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3928  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3927  in
                  (uu____3923, uu____3926)
               in
            let uu____3930 =
              let uu____3937 = FStar_List.hd xs  in
              let uu____3938 = FStar_List.tl xs  in (uu____3937, uu____3938)
               in
            match uu____3930 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3956 =
                    let uu____3958 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3958  in
                  let uu____3959 =
                    let uu____3960 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3960  in
                  (uu____3956, uu____3959)  in
                let uu____3962 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3962
  
let separate_map_with_comments_kw :
  'Auu____3989 'Auu____3990 .
    'Auu____3989 ->
      'Auu____3989 ->
        ('Auu____3989 -> 'Auu____3990 -> FStar_Pprint.document) ->
          'Auu____3990 Prims.list ->
            ('Auu____3990 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4054 x =
              match uu____4054 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4073 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4073 meta_decl doc1 false false
                     in
                  let uu____4077 =
                    let uu____4079 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4079  in
                  let uu____4080 =
                    let uu____4081 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4081  in
                  (uu____4077, uu____4080)
               in
            let uu____4083 =
              let uu____4090 = FStar_List.hd xs  in
              let uu____4091 = FStar_List.tl xs  in (uu____4090, uu____4091)
               in
            match uu____4083 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4109 =
                    let uu____4111 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4111  in
                  let uu____4112 = f prefix1 x  in (uu____4109, uu____4112)
                   in
                let uu____4114 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4114
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5100)) ->
          let uu____5103 =
            let uu____5105 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5105 FStar_Util.is_upper  in
          if uu____5103
          then
            let uu____5111 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5111 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5114 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5121 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5124 =
      let uu____5125 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5126 =
        let uu____5127 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5127  in
      FStar_Pprint.op_Hat_Hat uu____5125 uu____5126  in
    FStar_Pprint.op_Hat_Hat uu____5121 uu____5124

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5129 ->
        let uu____5130 =
          let uu____5131 = str "@ "  in
          let uu____5133 =
            let uu____5134 =
              let uu____5135 =
                let uu____5136 =
                  let uu____5137 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5137  in
                FStar_Pprint.op_Hat_Hat uu____5136 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5135  in
            FStar_Pprint.op_Hat_Hat uu____5134 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5131 uu____5133  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5130

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5140  ->
    match uu____5140 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5188 =
                match uu____5188 with
                | (kwd,arg) ->
                    let uu____5201 = str "@"  in
                    let uu____5203 =
                      let uu____5204 = str kwd  in
                      let uu____5205 =
                        let uu____5206 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5206
                         in
                      FStar_Pprint.op_Hat_Hat uu____5204 uu____5205  in
                    FStar_Pprint.op_Hat_Hat uu____5201 uu____5203
                 in
              let uu____5207 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5207 FStar_Pprint.hardline
           in
        let uu____5214 =
          let uu____5215 =
            let uu____5216 =
              let uu____5217 = str doc1  in
              let uu____5218 =
                let uu____5219 =
                  let uu____5220 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5220  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5219  in
              FStar_Pprint.op_Hat_Hat uu____5217 uu____5218  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5216  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5215  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5214

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5224 =
          let uu____5225 = str "val"  in
          let uu____5227 =
            let uu____5228 =
              let uu____5229 = p_lident lid  in
              let uu____5230 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5229 uu____5230  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5228  in
          FStar_Pprint.op_Hat_Hat uu____5225 uu____5227  in
        let uu____5231 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5224 uu____5231
    | FStar_Parser_AST.TopLevelLet (uu____5234,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5259 =
               let uu____5260 = str "let"  in p_letlhs uu____5260 lb false
                in
             FStar_Pprint.group uu____5259) lbs
    | uu____5263 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___31_5278 =
          match uu___31_5278 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5286 = f x  in
              let uu____5287 =
                let uu____5288 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5288  in
              FStar_Pprint.op_Hat_Hat uu____5286 uu____5287
           in
        let uu____5289 = str "["  in
        let uu____5291 =
          let uu____5292 = p_list' l  in
          let uu____5293 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5292 uu____5293  in
        FStar_Pprint.op_Hat_Hat uu____5289 uu____5291

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5297 =
          let uu____5298 = str "open"  in
          let uu____5300 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5298 uu____5300  in
        FStar_Pprint.group uu____5297
    | FStar_Parser_AST.Include uid ->
        let uu____5302 =
          let uu____5303 = str "include"  in
          let uu____5305 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5303 uu____5305  in
        FStar_Pprint.group uu____5302
    | FStar_Parser_AST.Friend uid ->
        let uu____5307 =
          let uu____5308 = str "friend"  in
          let uu____5310 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5308 uu____5310  in
        FStar_Pprint.group uu____5307
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5313 =
          let uu____5314 = str "module"  in
          let uu____5316 =
            let uu____5317 =
              let uu____5318 = p_uident uid1  in
              let uu____5319 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5318 uu____5319  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5317  in
          FStar_Pprint.op_Hat_Hat uu____5314 uu____5316  in
        let uu____5320 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5313 uu____5320
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5322 =
          let uu____5323 = str "module"  in
          let uu____5325 =
            let uu____5326 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5326  in
          FStar_Pprint.op_Hat_Hat uu____5323 uu____5325  in
        FStar_Pprint.group uu____5322
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5327,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5364 = str "effect"  in
          let uu____5366 =
            let uu____5367 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5367  in
          FStar_Pprint.op_Hat_Hat uu____5364 uu____5366  in
        let uu____5368 =
          let uu____5369 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5369 FStar_Pprint.equals
           in
        let uu____5372 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5368 uu____5372
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5403 =
          let uu____5404 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5404  in
        let uu____5417 =
          let uu____5418 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5456 =
                    let uu____5457 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5457 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5456)) uu____5418
           in
        FStar_Pprint.op_Hat_Hat uu____5403 uu____5417
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5474 = str "let"  in
          let uu____5476 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5474 uu____5476  in
        let uu____5477 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5477 p_letbinding lbs
          (fun uu____5487  ->
             match uu____5487 with
             | (p,t) ->
                 let uu____5494 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5494;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5500 =
          let uu____5501 = str "val"  in
          let uu____5503 =
            let uu____5504 =
              let uu____5505 = p_lident lid  in
              let uu____5506 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5505 uu____5506  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5504  in
          FStar_Pprint.op_Hat_Hat uu____5501 uu____5503  in
        FStar_All.pipe_left FStar_Pprint.group uu____5500
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5511 =
            let uu____5513 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5513 FStar_Util.is_upper  in
          if uu____5511
          then FStar_Pprint.empty
          else
            (let uu____5521 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5521 FStar_Pprint.space)
           in
        let uu____5523 =
          let uu____5524 = p_ident id1  in
          let uu____5525 =
            let uu____5526 =
              let uu____5527 =
                let uu____5528 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5528  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5527  in
            FStar_Pprint.group uu____5526  in
          FStar_Pprint.op_Hat_Hat uu____5524 uu____5525  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5523
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5537 = str "exception"  in
        let uu____5539 =
          let uu____5540 =
            let uu____5541 = p_uident uid  in
            let uu____5542 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5546 =
                     let uu____5547 = str "of"  in
                     let uu____5549 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5547 uu____5549  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5546) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5541 uu____5542  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5540  in
        FStar_Pprint.op_Hat_Hat uu____5537 uu____5539
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5553 = str "new_effect"  in
        let uu____5555 =
          let uu____5556 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5556  in
        FStar_Pprint.op_Hat_Hat uu____5553 uu____5555
    | FStar_Parser_AST.SubEffect se ->
        let uu____5558 = str "sub_effect"  in
        let uu____5560 =
          let uu____5561 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5561  in
        FStar_Pprint.op_Hat_Hat uu____5558 uu____5560
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5564 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5566,uu____5567) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5595 = str "%splice"  in
        let uu____5597 =
          let uu____5598 =
            let uu____5599 = str ";"  in p_list p_uident uu____5599 ids  in
          let uu____5601 =
            let uu____5602 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5602  in
          FStar_Pprint.op_Hat_Hat uu____5598 uu____5601  in
        FStar_Pprint.op_Hat_Hat uu____5595 uu____5597

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___32_5605  ->
    match uu___32_5605 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5608 = str "#set-options"  in
        let uu____5610 =
          let uu____5611 =
            let uu____5612 = str s  in FStar_Pprint.dquotes uu____5612  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5611  in
        FStar_Pprint.op_Hat_Hat uu____5608 uu____5610
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5617 = str "#reset-options"  in
        let uu____5619 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5625 =
                 let uu____5626 = str s  in FStar_Pprint.dquotes uu____5626
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5625) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5617 uu____5619
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5631 = str "#push-options"  in
        let uu____5633 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5639 =
                 let uu____5640 = str s  in FStar_Pprint.dquotes uu____5640
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5639) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5631 uu____5633
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
    fun uu____5671  ->
      match uu____5671 with
      | (typedecl,fsdoc_opt) ->
          let uu____5684 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5684 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5709 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5709
               else
                 (let uu____5712 =
                    let uu____5713 =
                      let uu____5714 =
                        let uu____5715 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5715 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5714  in
                    let uu____5716 =
                      let uu____5717 =
                        let uu____5718 =
                          let uu____5719 =
                            let uu____5720 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5720  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5719
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5718
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5717  in
                    FStar_Pprint.ifflat uu____5713 uu____5716  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5712))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___33_5723  ->
      match uu___33_5723 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5752 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5752, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5769 = p_typ_sep false false t  in
          (match uu____5769 with
           | (comm,doc1) ->
               let uu____5789 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5789, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5845 =
            match uu____5845 with
            | (lid1,t,doc_opt) ->
                let uu____5862 =
                  let uu____5867 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5867
                   in
                (match uu____5862 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5885 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5885  in
          let uu____5894 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5894, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5961 =
            match uu____5961 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5990 =
                    let uu____5991 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5991  in
                  FStar_Range.extend_to_end_of_line uu____5990  in
                let uu____5996 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5996 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6035 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6035, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6040  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6040 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6075 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6075  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6077 =
                        let uu____6080 =
                          let uu____6083 = p_fsdoc fsdoc  in
                          let uu____6084 =
                            let uu____6087 = cont lid_doc  in [uu____6087]
                             in
                          uu____6083 :: uu____6084  in
                        kw :: uu____6080  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6077
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6094 =
                        let uu____6095 =
                          let uu____6096 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6096 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6095
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6094
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6116 =
                          let uu____6117 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6117  in
                        prefix2 uu____6116 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6119  ->
      match uu____6119 with
      | (lid,t,doc_opt) ->
          let uu____6136 =
            let uu____6137 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6138 =
              let uu____6139 = p_lident lid  in
              let uu____6140 =
                let uu____6141 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6141  in
              FStar_Pprint.op_Hat_Hat uu____6139 uu____6140  in
            FStar_Pprint.op_Hat_Hat uu____6137 uu____6138  in
          FStar_Pprint.group uu____6136

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6143  ->
    match uu____6143 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6177 =
            let uu____6178 =
              let uu____6179 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6179  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6178  in
          FStar_Pprint.group uu____6177  in
        let uu____6180 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6181 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6185 =
                 let uu____6186 =
                   let uu____6187 =
                     let uu____6188 =
                       let uu____6189 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6189
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6188  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6187  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6186  in
               FStar_Pprint.group uu____6185) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6180 uu____6181

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6193  ->
      fun inner_let  ->
        match uu____6193 with
        | (pat,uu____6201) ->
            let uu____6202 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6254 =
                    let uu____6261 =
                      let uu____6266 =
                        let uu____6267 =
                          let uu____6268 =
                            let uu____6269 = str "by"  in
                            let uu____6271 =
                              let uu____6272 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6272
                               in
                            FStar_Pprint.op_Hat_Hat uu____6269 uu____6271  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6268
                           in
                        FStar_Pprint.group uu____6267  in
                      (t, uu____6266)  in
                    FStar_Pervasives_Native.Some uu____6261  in
                  (pat1, uu____6254)
              | uu____6283 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6202 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6309);
                         FStar_Parser_AST.prange = uu____6310;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6327 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6327 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6333 =
                        if inner_let
                        then
                          let uu____6347 = pats_as_binders_if_possible pats
                             in
                          match uu____6347 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6370 = pats_as_binders_if_possible pats
                              in
                           match uu____6370 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6333 with
                       | (terms,style) ->
                           let uu____6397 =
                             let uu____6398 =
                               let uu____6399 =
                                 let uu____6400 = p_lident lid  in
                                 let uu____6401 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6400
                                   uu____6401
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6399
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6398  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6397)
                  | uu____6404 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6412 =
                              let uu____6413 =
                                let uu____6414 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6414
                                 in
                              FStar_Pprint.group uu____6413  in
                            FStar_Pprint.op_Hat_Hat uu____6412 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6425 =
                        let uu____6426 =
                          let uu____6427 =
                            let uu____6428 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6428  in
                          FStar_Pprint.group uu____6427  in
                        FStar_Pprint.op_Hat_Hat uu____6426 ascr_doc  in
                      FStar_Pprint.group uu____6425))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6430  ->
      match uu____6430 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6439 = p_term_sep false false e  in
          (match uu____6439 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6449 =
                 let uu____6450 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6450  in
               let uu____6451 =
                 let uu____6452 =
                   let uu____6453 =
                     let uu____6454 =
                       let uu____6455 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6455
                        in
                     FStar_Pprint.group uu____6454  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6453  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6452  in
               FStar_Pprint.ifflat uu____6449 uu____6451)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___34_6456  ->
    match uu___34_6456 with
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
        let uu____6481 = p_uident uid  in
        let uu____6482 = p_binders true bs  in
        let uu____6484 =
          let uu____6485 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6485  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6481 uu____6482 uu____6484

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
          let uu____6500 =
            let uu____6501 =
              let uu____6502 =
                let uu____6503 = p_uident uid  in
                let uu____6504 = p_binders true bs  in
                let uu____6506 =
                  let uu____6507 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6507  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6503 uu____6504 uu____6506
                 in
              FStar_Pprint.group uu____6502  in
            let uu____6512 =
              let uu____6513 = str "with"  in
              let uu____6515 =
                let uu____6516 =
                  let uu____6517 =
                    let uu____6518 =
                      let uu____6519 =
                        let uu____6520 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6520
                         in
                      separate_map_last uu____6519 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6518  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6517  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6516  in
              FStar_Pprint.op_Hat_Hat uu____6513 uu____6515  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6501 uu____6512  in
          braces_with_nesting uu____6500

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6524,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6557 =
            let uu____6558 = p_lident lid  in
            let uu____6559 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6558 uu____6559  in
          let uu____6560 = p_simpleTerm ps false e  in
          prefix2 uu____6557 uu____6560
      | uu____6562 ->
          let uu____6563 =
            let uu____6565 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6565
             in
          failwith uu____6563

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6648 =
        match uu____6648 with
        | (kwd,t) ->
            let uu____6659 =
              let uu____6660 = str kwd  in
              let uu____6661 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6660 uu____6661  in
            let uu____6662 = p_simpleTerm ps false t  in
            prefix2 uu____6659 uu____6662
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6669 =
      let uu____6670 =
        let uu____6671 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6672 =
          let uu____6673 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6673  in
        FStar_Pprint.op_Hat_Hat uu____6671 uu____6672  in
      let uu____6675 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6670 uu____6675  in
    let uu____6676 =
      let uu____6677 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6677  in
    FStar_Pprint.op_Hat_Hat uu____6669 uu____6676

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___35_6678  ->
    match uu___35_6678 with
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
        let uu____6698 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6698 FStar_Pprint.hardline
    | uu____6699 ->
        let uu____6700 =
          let uu____6701 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6701  in
        FStar_Pprint.op_Hat_Hat uu____6700 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___36_6704  ->
    match uu___36_6704 with
    | FStar_Parser_AST.Rec  ->
        let uu____6705 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6705
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___37_6707  ->
    match uu___37_6707 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6712,e) -> e
          | uu____6718 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6719 = str "#["  in
        let uu____6721 =
          let uu____6722 = p_term false false t1  in
          let uu____6725 =
            let uu____6726 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6726 break1  in
          FStar_Pprint.op_Hat_Hat uu____6722 uu____6725  in
        FStar_Pprint.op_Hat_Hat uu____6719 uu____6721

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6732 =
          let uu____6733 =
            let uu____6734 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6734  in
          FStar_Pprint.separate_map uu____6733 p_tuplePattern pats  in
        FStar_Pprint.group uu____6732
    | uu____6735 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6744 =
          let uu____6745 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6745 p_constructorPattern pats  in
        FStar_Pprint.group uu____6744
    | uu____6746 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6749;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6754 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6755 = p_constructorPattern hd1  in
        let uu____6756 = p_constructorPattern tl1  in
        infix0 uu____6754 uu____6755 uu____6756
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6758;_},pats)
        ->
        let uu____6764 = p_quident uid  in
        let uu____6765 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6764 uu____6765
    | uu____6766 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6782;
               FStar_Parser_AST.blevel = uu____6783;
               FStar_Parser_AST.aqual = uu____6784;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6793 =
               let uu____6794 = p_ident lid  in
               p_refinement aqual uu____6794 t1 phi  in
             soft_parens_with_nesting uu____6793
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6797;
               FStar_Parser_AST.blevel = uu____6798;
               FStar_Parser_AST.aqual = uu____6799;_},phi))
             ->
             let uu____6805 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6805
         | uu____6806 ->
             let uu____6811 =
               let uu____6812 = p_tuplePattern pat  in
               let uu____6813 =
                 let uu____6814 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6814
                  in
               FStar_Pprint.op_Hat_Hat uu____6812 uu____6813  in
             soft_parens_with_nesting uu____6811)
    | FStar_Parser_AST.PatList pats ->
        let uu____6818 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6818 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6837 =
          match uu____6837 with
          | (lid,pat) ->
              let uu____6844 = p_qlident lid  in
              let uu____6845 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6844 uu____6845
           in
        let uu____6846 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6846
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6858 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6859 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6860 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6858 uu____6859 uu____6860
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6871 =
          let uu____6872 =
            let uu____6873 =
              let uu____6874 = FStar_Ident.text_of_id op  in str uu____6874
               in
            let uu____6876 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6873 uu____6876  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6872  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6871
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6880 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6880 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6888 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6889 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6888 uu____6889
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6891 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6895;
           FStar_Parser_AST.prange = uu____6896;_},uu____6897)
        ->
        let uu____6902 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6902
    | FStar_Parser_AST.PatTuple (uu____6903,false ) ->
        let uu____6910 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6910
    | uu____6911 ->
        let uu____6912 =
          let uu____6914 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6914  in
        failwith uu____6912

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6919;_},uu____6920)
        -> true
    | uu____6927 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6933) -> true
    | uu____6935 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6942 = p_binder' is_atomic b  in
      match uu____6942 with
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
          let uu____6981 =
            let uu____6982 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6983 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6982 uu____6983  in
          (uu____6981, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6989 = p_lident lid  in
          (uu____6989, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6996 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____7007;
                   FStar_Parser_AST.blevel = uu____7008;
                   FStar_Parser_AST.aqual = uu____7009;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____7014 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____7014 t1 phi
            | uu____7015 ->
                let t' =
                  let uu____7017 = is_typ_tuple t  in
                  if uu____7017
                  then
                    let uu____7020 = p_tmFormula t  in
                    soft_parens_with_nesting uu____7020
                  else p_tmFormula t  in
                let uu____7023 =
                  let uu____7024 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____7025 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____7024 uu____7025  in
                (uu____7023, t')
             in
          (match uu____6996 with
           | (b',t') ->
               let catf =
                 let uu____7043 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7043
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7050 =
                         let uu____7051 =
                           let uu____7052 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7052
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7051
                          in
                       FStar_Pprint.group uu____7050
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7057 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7057)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7066 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7094;
                  FStar_Parser_AST.blevel = uu____7095;
                  FStar_Parser_AST.aqual = uu____7096;_},phi)
               ->
               let uu____7100 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7100 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7121 ->
               if is_atomic
               then
                 let uu____7133 = p_atomicTerm t  in
                 (uu____7133, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7140 = p_appTerm t  in
                  (uu____7140, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7151 = p_refinement' aqual_opt binder t phi  in
          match uu____7151 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7167 -> false
            | FStar_Parser_AST.App uu____7179 -> false
            | FStar_Parser_AST.Op uu____7187 -> false
            | uu____7195 -> true  in
          let uu____7197 = p_noSeqTerm false false phi  in
          match uu____7197 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7214 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7214)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7223 =
                let uu____7224 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7224 binder  in
              let uu____7225 =
                let uu____7226 = p_appTerm t  in
                let uu____7227 =
                  let uu____7228 =
                    let uu____7229 =
                      let uu____7230 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7231 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7230 uu____7231  in
                    FStar_Pprint.group uu____7229  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7228
                   in
                FStar_Pprint.op_Hat_Hat uu____7226 uu____7227  in
              (uu____7223, uu____7225)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7245 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7245

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7249 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7252 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7252)
       in
    if uu____7249
    then FStar_Pprint.underscore
    else (let uu____7257 = FStar_Ident.text_of_id lid  in str uu____7257)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7260 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7263 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7263)
       in
    if uu____7260
    then FStar_Pprint.underscore
    else (let uu____7268 = FStar_Ident.text_of_lid lid  in str uu____7268)

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
          let uu____7289 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7289
        else
          (let uu____7292 =
             let uu____7293 =
               let uu____7294 =
                 let uu____7295 =
                   let uu____7296 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7296  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7295  in
               FStar_Pprint.group uu____7294  in
             let uu____7297 =
               let uu____7298 =
                 let uu____7299 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7299  in
               FStar_Pprint.op_Hat_Hat comm uu____7298  in
             FStar_Pprint.ifflat uu____7293 uu____7297  in
           FStar_All.pipe_left FStar_Pprint.group uu____7292)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7307 = p_noSeqTerm true false e1  in
            (match uu____7307 with
             | (comm,t1) ->
                 let uu____7316 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7317 =
                   let uu____7318 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7318
                    in
                 FStar_Pprint.op_Hat_Hat uu____7316 uu____7317)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7322 =
              let uu____7323 =
                let uu____7324 =
                  let uu____7325 = p_lident x  in
                  let uu____7326 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7325 uu____7326  in
                let uu____7327 =
                  let uu____7328 = p_noSeqTermAndComment true false e1  in
                  let uu____7331 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7328 uu____7331  in
                op_Hat_Slash_Plus_Hat uu____7324 uu____7327  in
              FStar_Pprint.group uu____7323  in
            let uu____7332 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7322 uu____7332
        | uu____7333 ->
            let uu____7334 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7334

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
            let uu____7346 = p_noSeqTerm true false e1  in
            (match uu____7346 with
             | (comm,t1) ->
                 let uu____7359 =
                   let uu____7360 =
                     let uu____7361 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7361  in
                   let uu____7362 =
                     let uu____7363 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7363
                      in
                   FStar_Pprint.op_Hat_Hat uu____7360 uu____7362  in
                 (comm, uu____7359))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7367 =
              let uu____7368 =
                let uu____7369 =
                  let uu____7370 =
                    let uu____7371 = p_lident x  in
                    let uu____7372 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7371 uu____7372  in
                  let uu____7373 =
                    let uu____7374 = p_noSeqTermAndComment true false e1  in
                    let uu____7377 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7374 uu____7377  in
                  op_Hat_Slash_Plus_Hat uu____7370 uu____7373  in
                FStar_Pprint.group uu____7369  in
              let uu____7378 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7368 uu____7378  in
            (FStar_Pprint.empty, uu____7367)
        | uu____7379 -> p_noSeqTerm ps pb e

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
            let uu____7399 =
              let uu____7400 = p_tmIff e1  in
              let uu____7401 =
                let uu____7402 =
                  let uu____7403 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7403
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7402  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7400 uu____7401  in
            FStar_Pprint.group uu____7399
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7409 =
              let uu____7410 = p_tmIff e1  in
              let uu____7411 =
                let uu____7412 =
                  let uu____7413 =
                    let uu____7414 = p_typ false false t  in
                    let uu____7417 =
                      let uu____7418 = str "by"  in
                      let uu____7420 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7418 uu____7420  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7414 uu____7417  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7413
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7412  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7410 uu____7411  in
            FStar_Pprint.group uu____7409
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7421;_},e1::e2::e3::[])
            ->
            let uu____7428 =
              let uu____7429 =
                let uu____7430 =
                  let uu____7431 = p_atomicTermNotQUident e1  in
                  let uu____7432 =
                    let uu____7433 =
                      let uu____7434 =
                        let uu____7435 = p_term false false e2  in
                        soft_parens_with_nesting uu____7435  in
                      let uu____7438 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7434 uu____7438  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7433  in
                  FStar_Pprint.op_Hat_Hat uu____7431 uu____7432  in
                FStar_Pprint.group uu____7430  in
              let uu____7439 =
                let uu____7440 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7440  in
              FStar_Pprint.op_Hat_Hat uu____7429 uu____7439  in
            FStar_Pprint.group uu____7428
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7441;_},e1::e2::e3::[])
            ->
            let uu____7448 =
              let uu____7449 =
                let uu____7450 =
                  let uu____7451 = p_atomicTermNotQUident e1  in
                  let uu____7452 =
                    let uu____7453 =
                      let uu____7454 =
                        let uu____7455 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7455  in
                      let uu____7458 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7454 uu____7458  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7453  in
                  FStar_Pprint.op_Hat_Hat uu____7451 uu____7452  in
                FStar_Pprint.group uu____7450  in
              let uu____7459 =
                let uu____7460 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7460  in
              FStar_Pprint.op_Hat_Hat uu____7449 uu____7459  in
            FStar_Pprint.group uu____7448
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7470 =
              let uu____7471 = str "requires"  in
              let uu____7473 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7471 uu____7473  in
            FStar_Pprint.group uu____7470
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7483 =
              let uu____7484 = str "ensures"  in
              let uu____7486 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7484 uu____7486  in
            FStar_Pprint.group uu____7483
        | FStar_Parser_AST.Attributes es ->
            let uu____7490 =
              let uu____7491 = str "attributes"  in
              let uu____7493 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7491 uu____7493  in
            FStar_Pprint.group uu____7490
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7498 =
                let uu____7499 =
                  let uu____7500 = str "if"  in
                  let uu____7502 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7500 uu____7502  in
                let uu____7505 =
                  let uu____7506 = str "then"  in
                  let uu____7508 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7506 uu____7508  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7499 uu____7505  in
              FStar_Pprint.group uu____7498
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7512,uu____7513,e31) when
                     is_unit e31 ->
                     let uu____7515 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7515
                 | uu____7518 -> p_noSeqTermAndComment false false e2  in
               let uu____7521 =
                 let uu____7522 =
                   let uu____7523 = str "if"  in
                   let uu____7525 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7523 uu____7525  in
                 let uu____7528 =
                   let uu____7529 =
                     let uu____7530 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7530 e2_doc  in
                   let uu____7532 =
                     let uu____7533 = str "else"  in
                     let uu____7535 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7533 uu____7535  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7529 uu____7532  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7522 uu____7528  in
               FStar_Pprint.group uu____7521)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7558 =
              let uu____7559 =
                let uu____7560 =
                  let uu____7561 = str "try"  in
                  let uu____7563 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7561 uu____7563  in
                let uu____7566 =
                  let uu____7567 = str "with"  in
                  let uu____7569 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7567 uu____7569  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7560 uu____7566  in
              FStar_Pprint.group uu____7559  in
            let uu____7578 = paren_if (ps || pb)  in uu____7578 uu____7558
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7605 =
              let uu____7606 =
                let uu____7607 =
                  let uu____7608 = str "match"  in
                  let uu____7610 = p_noSeqTermAndComment false false e1  in
                  let uu____7613 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7608 uu____7610 uu____7613
                   in
                let uu____7617 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7607 uu____7617  in
              FStar_Pprint.group uu____7606  in
            let uu____7626 = paren_if (ps || pb)  in uu____7626 uu____7605
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7633 =
              let uu____7634 =
                let uu____7635 =
                  let uu____7636 = str "let open"  in
                  let uu____7638 = p_quident uid  in
                  let uu____7639 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7636 uu____7638 uu____7639
                   in
                let uu____7643 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7635 uu____7643  in
              FStar_Pprint.group uu____7634  in
            let uu____7645 = paren_if ps  in uu____7645 uu____7633
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7710 is_last =
              match uu____7710 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7744 =
                          let uu____7745 = str "let"  in
                          let uu____7747 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7745 uu____7747
                           in
                        FStar_Pprint.group uu____7744
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7750 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7756 = p_term_sep false false e2  in
                  (match uu____7756 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7766 =
                         if is_last
                         then
                           let uu____7768 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7769 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7768 doc_expr1
                             uu____7769
                         else
                           (let uu____7775 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7775)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7766)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7826 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7826
                     else
                       (let uu____7837 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7837)) lbs
               in
            let lbs_doc =
              let uu____7847 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7847  in
            let uu____7848 =
              let uu____7849 =
                let uu____7850 =
                  let uu____7851 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7851
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7850  in
              FStar_Pprint.group uu____7849  in
            let uu____7853 = paren_if ps  in uu____7853 uu____7848
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7860;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7863;
                                                             FStar_Parser_AST.level
                                                               = uu____7864;_})
            when matches_var maybe_x x ->
            let uu____7891 =
              let uu____7892 =
                let uu____7893 = str "function"  in
                let uu____7895 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7893 uu____7895  in
              FStar_Pprint.group uu____7892  in
            let uu____7904 = paren_if (ps || pb)  in uu____7904 uu____7891
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7910 =
              let uu____7911 = str "quote"  in
              let uu____7913 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7911 uu____7913  in
            FStar_Pprint.group uu____7910
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7915 =
              let uu____7916 = str "`"  in
              let uu____7918 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7916 uu____7918  in
            FStar_Pprint.group uu____7915
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7920 =
              let uu____7921 = str "`%"  in
              let uu____7923 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7921 uu____7923  in
            FStar_Pprint.group uu____7920
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7925;
              FStar_Parser_AST.level = uu____7926;_}
            ->
            let uu____7927 =
              let uu____7928 = str "`@"  in
              let uu____7930 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7928 uu____7930  in
            FStar_Pprint.group uu____7927
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7932 =
              let uu____7933 = str "`#"  in
              let uu____7935 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7933 uu____7935  in
            FStar_Pprint.group uu____7932
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7944 = str "calc"  in
              let uu____7946 =
                let uu____7947 =
                  let uu____7948 = p_noSeqTermAndComment false false rel  in
                  let uu____7951 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7948 uu____7951  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7947  in
              FStar_Pprint.op_Hat_Hat uu____7944 uu____7946  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7953 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7954 =
              let uu____7955 =
                let uu____7956 =
                  let uu____7957 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7960 =
                    let uu____7961 = str ";"  in
                    let uu____7963 =
                      let uu____7964 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7964
                       in
                    FStar_Pprint.op_Hat_Hat uu____7961 uu____7963  in
                  FStar_Pprint.op_Hat_Hat uu____7957 uu____7960  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7956  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7955
               in
            FStar_Pprint.enclose head1 uu____7953 uu____7954
        | uu____7966 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7967  ->
    fun uu____7968  ->
      match uu____7968 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7973 =
            let uu____7974 = p_noSeqTermAndComment false false rel  in
            let uu____7977 =
              let uu____7978 =
                let uu____7979 =
                  let uu____7980 =
                    let uu____7981 = p_noSeqTermAndComment false false just
                       in
                    let uu____7984 =
                      let uu____7985 =
                        let uu____7986 =
                          let uu____7987 =
                            let uu____7988 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7991 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7988 uu____7991  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7987
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7986
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7985
                       in
                    FStar_Pprint.op_Hat_Hat uu____7981 uu____7984  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7980  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7979  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7978  in
            FStar_Pprint.op_Hat_Hat uu____7974 uu____7977  in
          FStar_Pprint.group uu____7973

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___38_7993  ->
    match uu___38_7993 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____8005 =
          let uu____8006 = str "[@"  in
          let uu____8008 =
            let uu____8009 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____8010 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____8009 uu____8010  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8006 uu____8008  in
        FStar_Pprint.group uu____8005

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
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8047 =
                   let uu____8048 =
                     let uu____8049 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8049 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8048 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8047 term_doc
             | pats ->
                 let uu____8057 =
                   let uu____8058 =
                     let uu____8059 =
                       let uu____8060 =
                         let uu____8061 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8061
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8060 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8064 = p_trigger trigger  in
                     prefix2 uu____8059 uu____8064  in
                   FStar_Pprint.group uu____8058  in
                 prefix2 uu____8057 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8085 =
                   let uu____8086 =
                     let uu____8087 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8087 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8086 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8085 term_doc
             | pats ->
                 let uu____8095 =
                   let uu____8096 =
                     let uu____8097 =
                       let uu____8098 =
                         let uu____8099 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8099
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8098 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8102 = p_trigger trigger  in
                     prefix2 uu____8097 uu____8102  in
                   FStar_Pprint.group uu____8096  in
                 prefix2 uu____8095 term_doc)
        | uu____8103 -> p_simpleTerm ps pb e

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
      let uu____8124 = all_binders_annot t  in
      if uu____8124
      then
        let uu____8127 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8127
      else
        (let uu____8138 =
           let uu____8139 =
             let uu____8140 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8140  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8139  in
         FStar_Pprint.group uu____8138)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8199 = x  in
      match uu____8199 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8264 = hd1  in
               (match uu____8264 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8336 = cb  in
      match uu____8336 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8355 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8361 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8361) hd1 tl1
                  in
               cat_with_colon uu____8355 typ)
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
                 FStar_Parser_AST.brange = uu____8440;
                 FStar_Parser_AST.blevel = uu____8441;
                 FStar_Parser_AST.aqual = uu____8442;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8451 =
                 let uu____8456 = p_ident lid  in
                 p_refinement' aqual uu____8456 t1 phi  in
               FStar_Pervasives_Native.Some uu____8451
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8463) ->
               let uu____8468 =
                 let uu____8473 =
                   let uu____8474 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8475 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8474 uu____8475  in
                 let uu____8476 = p_tmEqNoRefinement t  in
                 (uu____8473, uu____8476)  in
               FStar_Pervasives_Native.Some uu____8468
           | uu____8481 -> FStar_Pervasives_Native.None)
      | uu____8490 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8503 -> false
      | uu____8515 -> true  in
    let uu____8517 = map_if_all all_binders pats  in
    match uu____8517 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8549 = collapse_pats bs  in
        (uu____8549,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8566 = FStar_List.map p_atomicPattern pats  in
        (uu____8566,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8578 -> str "forall"
    | FStar_Parser_AST.QExists uu____8592 -> str "exists"
    | uu____8606 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___39_8608  ->
    match uu___39_8608 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8620 =
          let uu____8621 =
            let uu____8622 =
              let uu____8623 = str "pattern"  in
              let uu____8625 =
                let uu____8626 =
                  let uu____8627 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8627
                   in
                FStar_Pprint.op_Hat_Hat uu____8626 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8623 uu____8625  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8622  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8621  in
        FStar_Pprint.group uu____8620

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8635 = str "\\/"  in
    FStar_Pprint.separate_map uu____8635 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8642 =
      let uu____8643 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8643 p_appTerm pats  in
    FStar_Pprint.group uu____8642

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8655 = p_term_sep false pb e1  in
            (match uu____8655 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8664 = str "fun"  in
                   let uu____8666 =
                     let uu____8667 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8667
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8664 uu____8666  in
                 let uu____8668 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8670 =
                       let uu____8671 =
                         let uu____8672 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8672  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8671
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8670
                   else
                     (let uu____8675 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8675)
                    in
                 let uu____8676 = paren_if ps  in uu____8676 uu____8668)
        | uu____8681 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8689  ->
      match uu____8689 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8713 =
                    let uu____8714 =
                      let uu____8715 =
                        let uu____8716 = p_tuplePattern p  in
                        let uu____8717 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8716 uu____8717  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8715
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8714  in
                  FStar_Pprint.group uu____8713
              | FStar_Pervasives_Native.Some f ->
                  let uu____8719 =
                    let uu____8720 =
                      let uu____8721 =
                        let uu____8722 =
                          let uu____8723 =
                            let uu____8724 = p_tuplePattern p  in
                            let uu____8725 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8724
                              uu____8725
                             in
                          FStar_Pprint.group uu____8723  in
                        let uu____8727 =
                          let uu____8728 =
                            let uu____8731 = p_tmFormula f  in
                            [uu____8731; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8728  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8722 uu____8727
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8721
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8720  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8719
               in
            let uu____8733 = p_term_sep false pb e  in
            match uu____8733 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8743 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8743
                   else
                     (let uu____8746 =
                        let uu____8747 =
                          let uu____8748 =
                            let uu____8749 =
                              let uu____8750 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8750  in
                            op_Hat_Slash_Plus_Hat branch uu____8749  in
                          FStar_Pprint.group uu____8748  in
                        let uu____8751 =
                          let uu____8752 =
                            let uu____8753 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8753  in
                          FStar_Pprint.op_Hat_Hat branch uu____8752  in
                        FStar_Pprint.ifflat uu____8747 uu____8751  in
                      FStar_Pprint.group uu____8746))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8757 =
                       let uu____8758 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8758  in
                     op_Hat_Slash_Plus_Hat branch uu____8757)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8769 =
                      let uu____8770 =
                        let uu____8771 =
                          let uu____8772 =
                            let uu____8773 =
                              let uu____8774 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8774  in
                            FStar_Pprint.separate_map uu____8773
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8772
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8771
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8770  in
                    FStar_Pprint.group uu____8769
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8776 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8778;_},e1::e2::[])
        ->
        let uu____8784 = str "<==>"  in
        let uu____8786 = p_tmImplies e1  in
        let uu____8787 = p_tmIff e2  in
        infix0 uu____8784 uu____8786 uu____8787
    | uu____8788 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8790;_},e1::e2::[])
        ->
        let uu____8796 = str "==>"  in
        let uu____8798 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8804 = p_tmImplies e2  in
        infix0 uu____8796 uu____8798 uu____8804
    | uu____8805 ->
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
          let uu____8819 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8819 with
          | (terms',last1) ->
              let uu____8839 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8874 =
                      let uu____8875 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8875
                       in
                    let uu____8876 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8874, uu____8876)
                | Binders (n1,ln,parens1) ->
                    let uu____8890 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8898 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8890, break1, uu____8898)
                 in
              (match uu____8839 with
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
                    | _0_5 when _0_5 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____8931 ->
                        let uu____8932 =
                          let uu____8933 =
                            let uu____8934 =
                              let uu____8935 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8936 =
                                let uu____8937 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8937
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8935 uu____8936
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8934  in
                          let uu____8938 =
                            let uu____8939 =
                              let uu____8940 =
                                let uu____8941 =
                                  let uu____8942 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8942  in
                                let uu____8943 =
                                  let uu____8944 =
                                    let uu____8945 =
                                      let uu____8946 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8947 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8953 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8953)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8946
                                        uu____8947
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8945
                                     in
                                  jump2 uu____8944  in
                                FStar_Pprint.ifflat uu____8941 uu____8943  in
                              FStar_Pprint.group uu____8940  in
                            let uu____8955 =
                              let uu____8956 =
                                let uu____8957 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8957  in
                              FStar_Pprint.align uu____8956  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8939 uu____8955
                             in
                          FStar_Pprint.ifflat uu____8933 uu____8938  in
                        FStar_Pprint.group uu____8932))

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
            | Arrows uu____8971 -> p_tmArrow' p_Tm e
            | Binders uu____8978 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____9001 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9007 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____9001 uu____9007
      | uu____9010 -> let uu____9011 = p_Tm e  in [uu____9011]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9064 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9090 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9064 uu____9090
        | uu____9113 ->
            let uu____9114 =
              let uu____9125 = p_Tm1 e1  in
              (uu____9125, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9114]
         in
      let fold_fun bs x =
        let uu____9223 = x  in
        match uu____9223 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9359 = hd1  in
                 (match uu____9359 with
                  | (b2s,t2,uu____9388) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9498 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9559 = cb  in
        match uu____9559 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9588 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9601 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9607 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9607) hd1 tl1
                         in
                      f uu____9601 typ))
         in
      let binders =
        let uu____9625 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9625  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9688 =
        let uu____9689 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9689 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9688  in
    let disj =
      let uu____9692 =
        let uu____9693 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9693 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9692  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9713;_},e1::e2::[])
        ->
        let uu____9719 = p_tmDisjunction e1  in
        let uu____9724 = let uu____9729 = p_tmConjunction e2  in [uu____9729]
           in
        FStar_List.append uu____9719 uu____9724
    | uu____9738 -> let uu____9739 = p_tmConjunction e  in [uu____9739]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9749;_},e1::e2::[])
        ->
        let uu____9755 = p_tmConjunction e1  in
        let uu____9758 = let uu____9761 = p_tmTuple e2  in [uu____9761]  in
        FStar_List.append uu____9755 uu____9758
    | uu____9762 -> let uu____9763 = p_tmTuple e  in [uu____9763]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9780 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9780
          (fun uu____9788  ->
             match uu____9788 with | (e1,uu____9794) -> p_tmEq e1) args
    | uu____9795 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9804 =
             let uu____9805 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9805  in
           FStar_Pprint.group uu____9804)

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
               (let uu____9824 = FStar_Ident.text_of_id op  in
                uu____9824 = "="))
              ||
              (let uu____9829 = FStar_Ident.text_of_id op  in
               uu____9829 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9835 = levels op1  in
            (match uu____9835 with
             | (left1,mine,right1) ->
                 let uu____9854 =
                   let uu____9855 = FStar_All.pipe_left str op1  in
                   let uu____9857 = p_tmEqWith' p_X left1 e1  in
                   let uu____9858 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9855 uu____9857 uu____9858  in
                 paren_if_gt curr mine uu____9854)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9859;_},e1::e2::[])
            ->
            let uu____9865 =
              let uu____9866 = p_tmEqWith p_X e1  in
              let uu____9867 =
                let uu____9868 =
                  let uu____9869 =
                    let uu____9870 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9870  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9869  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9868  in
              FStar_Pprint.op_Hat_Hat uu____9866 uu____9867  in
            FStar_Pprint.group uu____9865
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9871;_},e1::[])
            ->
            let uu____9876 = levels "-"  in
            (match uu____9876 with
             | (left1,mine,right1) ->
                 let uu____9896 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9896)
        | uu____9897 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9945)::(e2,uu____9947)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9967 = is_list e  in Prims.op_Negation uu____9967)
              ->
              let op = "::"  in
              let uu____9972 = levels op  in
              (match uu____9972 with
               | (left1,mine,right1) ->
                   let uu____9991 =
                     let uu____9992 = str op  in
                     let uu____9993 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9995 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9992 uu____9993 uu____9995  in
                   paren_if_gt curr mine uu____9991)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____10014 = levels op  in
              (match uu____10014 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10048 = p_binder false b  in
                         let uu____10050 =
                           let uu____10051 =
                             let uu____10052 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10052 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10051
                            in
                         FStar_Pprint.op_Hat_Hat uu____10048 uu____10050
                     | FStar_Util.Inr t ->
                         let uu____10054 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10056 =
                           let uu____10057 =
                             let uu____10058 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10058 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10057
                            in
                         FStar_Pprint.op_Hat_Hat uu____10054 uu____10056
                      in
                   let uu____10059 =
                     let uu____10060 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10065 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10060 uu____10065  in
                   paren_if_gt curr mine uu____10059)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10067;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10097 = levels op  in
              (match uu____10097 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10117 = str op  in
                     let uu____10118 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10120 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10117 uu____10118 uu____10120
                   else
                     (let uu____10124 =
                        let uu____10125 = str op  in
                        let uu____10126 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10128 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10125 uu____10126 uu____10128  in
                      paren_if_gt curr mine uu____10124))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10137 = levels op1  in
              (match uu____10137 with
               | (left1,mine,right1) ->
                   let uu____10156 =
                     let uu____10157 = str op1  in
                     let uu____10158 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10160 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10157 uu____10158 uu____10160  in
                   paren_if_gt curr mine uu____10156)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10180 =
                let uu____10181 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10182 =
                  let uu____10183 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10183 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10181 uu____10182  in
              braces_with_nesting uu____10180
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10188;_},e1::[])
              ->
              let uu____10193 =
                let uu____10194 = str "~"  in
                let uu____10196 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10194 uu____10196  in
              FStar_Pprint.group uu____10193
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10198;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10207 = levels op  in
                   (match uu____10207 with
                    | (left1,mine,right1) ->
                        let uu____10226 =
                          let uu____10227 = str op  in
                          let uu____10228 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10230 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10227 uu____10228 uu____10230  in
                        paren_if_gt curr mine uu____10226)
               | uu____10232 -> p_X e)
          | uu____10233 -> p_X e

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
        let uu____10240 =
          let uu____10241 = p_lident lid  in
          let uu____10242 =
            let uu____10243 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10243  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10241 uu____10242  in
        FStar_Pprint.group uu____10240
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10246 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10248 = p_appTerm e  in
    let uu____10249 =
      let uu____10250 =
        let uu____10251 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10251 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10250  in
    FStar_Pprint.op_Hat_Hat uu____10248 uu____10249

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10257 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10257 t phi
      | FStar_Parser_AST.TAnnotated uu____10258 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10264 ->
          let uu____10265 =
            let uu____10267 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10267
             in
          failwith uu____10265
      | FStar_Parser_AST.TVariable uu____10270 ->
          let uu____10271 =
            let uu____10273 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10273
             in
          failwith uu____10271
      | FStar_Parser_AST.NoName uu____10276 ->
          let uu____10277 =
            let uu____10279 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10279
             in
          failwith uu____10277

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10283  ->
      match uu____10283 with
      | (lid,e) ->
          let uu____10291 =
            let uu____10292 = p_qlident lid  in
            let uu____10293 =
              let uu____10294 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10294
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10292 uu____10293  in
          FStar_Pprint.group uu____10291

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10297 when is_general_application e ->
        let uu____10304 = head_and_args e  in
        (match uu____10304 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10351 = p_argTerm e1  in
                  let uu____10352 =
                    let uu____10353 =
                      let uu____10354 =
                        let uu____10355 = str "`"  in
                        let uu____10357 =
                          let uu____10358 = p_indexingTerm head1  in
                          let uu____10359 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10358 uu____10359  in
                        FStar_Pprint.op_Hat_Hat uu____10355 uu____10357  in
                      FStar_Pprint.group uu____10354  in
                    let uu____10361 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10353 uu____10361  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10351 uu____10352
              | uu____10362 ->
                  let uu____10369 =
                    let uu____10380 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10380
                    then
                      let uu____10414 =
                        FStar_Util.take
                          (fun uu____10438  ->
                             match uu____10438 with
                             | (uu____10444,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10414 with
                      | (fs_typ_args,args1) ->
                          let uu____10482 =
                            let uu____10483 = p_indexingTerm head1  in
                            let uu____10484 =
                              let uu____10485 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10485
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10483 uu____10484
                             in
                          (uu____10482, args1)
                    else
                      (let uu____10500 = p_indexingTerm head1  in
                       (uu____10500, args))
                     in
                  (match uu____10369 with
                   | (head_doc,args1) ->
                       let uu____10521 =
                         let uu____10522 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10522 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10521)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10544 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10544)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10563 =
               let uu____10564 = p_quident lid  in
               let uu____10565 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10564 uu____10565  in
             FStar_Pprint.group uu____10563
         | hd1::tl1 ->
             let uu____10582 =
               let uu____10583 =
                 let uu____10584 =
                   let uu____10585 = p_quident lid  in
                   let uu____10586 = p_argTerm hd1  in
                   prefix2 uu____10585 uu____10586  in
                 FStar_Pprint.group uu____10584  in
               let uu____10587 =
                 let uu____10588 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10588  in
               FStar_Pprint.op_Hat_Hat uu____10583 uu____10587  in
             FStar_Pprint.group uu____10582)
    | uu____10593 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10604 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10604 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10608 = str "#"  in
        let uu____10610 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10608 uu____10610
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10613 = str "#["  in
        let uu____10615 =
          let uu____10616 = p_indexingTerm t  in
          let uu____10617 =
            let uu____10618 = str "]"  in
            let uu____10620 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10618 uu____10620  in
          FStar_Pprint.op_Hat_Hat uu____10616 uu____10617  in
        FStar_Pprint.op_Hat_Hat uu____10613 uu____10615
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10623  ->
    match uu____10623 with | (e,uu____10629) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10634;_},e1::e2::[])
          ->
          let uu____10640 =
            let uu____10641 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10642 =
              let uu____10643 =
                let uu____10644 = p_term false false e2  in
                soft_parens_with_nesting uu____10644  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10643  in
            FStar_Pprint.op_Hat_Hat uu____10641 uu____10642  in
          FStar_Pprint.group uu____10640
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10647;_},e1::e2::[])
          ->
          let uu____10653 =
            let uu____10654 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10655 =
              let uu____10656 =
                let uu____10657 = p_term false false e2  in
                soft_brackets_with_nesting uu____10657  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10656  in
            FStar_Pprint.op_Hat_Hat uu____10654 uu____10655  in
          FStar_Pprint.group uu____10653
      | uu____10660 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10665 = p_quident lid  in
        let uu____10666 =
          let uu____10667 =
            let uu____10668 = p_term false false e1  in
            soft_parens_with_nesting uu____10668  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10667  in
        FStar_Pprint.op_Hat_Hat uu____10665 uu____10666
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10676 =
          let uu____10677 = FStar_Ident.text_of_id op  in str uu____10677  in
        let uu____10679 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10676 uu____10679
    | uu____10680 -> p_atomicTermNotQUident e

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
         | uu____10693 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10702 =
          let uu____10703 = FStar_Ident.text_of_id op  in str uu____10703  in
        let uu____10705 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10702 uu____10705
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10709 =
          let uu____10710 =
            let uu____10711 =
              let uu____10712 = FStar_Ident.text_of_id op  in str uu____10712
               in
            let uu____10714 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10711 uu____10714  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10710  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10709
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10729 = all_explicit args  in
        if uu____10729
        then
          let uu____10732 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10733 =
            let uu____10734 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10735 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10734 p_tmEq uu____10735  in
          let uu____10742 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10732 uu____10733 uu____10742
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10764 =
                 let uu____10765 = p_quident lid  in
                 let uu____10766 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10765 uu____10766  in
               FStar_Pprint.group uu____10764
           | hd1::tl1 ->
               let uu____10783 =
                 let uu____10784 =
                   let uu____10785 =
                     let uu____10786 = p_quident lid  in
                     let uu____10787 = p_argTerm hd1  in
                     prefix2 uu____10786 uu____10787  in
                   FStar_Pprint.group uu____10785  in
                 let uu____10788 =
                   let uu____10789 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10789  in
                 FStar_Pprint.op_Hat_Hat uu____10784 uu____10788  in
               FStar_Pprint.group uu____10783)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10796 =
          let uu____10797 = p_atomicTermNotQUident e1  in
          let uu____10798 =
            let uu____10799 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10799  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10797 uu____10798
           in
        FStar_Pprint.group uu____10796
    | uu____10802 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10807 = p_quident constr_lid  in
        let uu____10808 =
          let uu____10809 =
            let uu____10810 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10810  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10809  in
        FStar_Pprint.op_Hat_Hat uu____10807 uu____10808
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10812 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10812 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10814 = p_term_sep false false e1  in
        (match uu____10814 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10827 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10827))
    | uu____10828 when is_array e ->
        let es = extract_from_list e  in
        let uu____10832 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10833 =
          let uu____10834 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10834
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10839 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10832 uu____10833 uu____10839
    | uu____10842 when is_list e ->
        let uu____10843 =
          let uu____10844 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10845 = extract_from_list e  in
          separate_map_or_flow_last uu____10844
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10845
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10843 FStar_Pprint.rbracket
    | uu____10854 when is_lex_list e ->
        let uu____10855 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10856 =
          let uu____10857 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10858 = extract_from_list e  in
          separate_map_or_flow_last uu____10857
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10858
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10855 uu____10856 FStar_Pprint.rbracket
    | uu____10867 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10871 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10872 =
          let uu____10873 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10873 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10871 uu____10872 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10883 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____10886 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10883 uu____10886
    | FStar_Parser_AST.Op (op,args) when
        let uu____10895 = handleable_op op args  in
        Prims.op_Negation uu____10895 ->
        let uu____10897 =
          let uu____10899 =
            let uu____10901 = FStar_Ident.text_of_id op  in
            let uu____10903 =
              let uu____10905 =
                let uu____10907 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____10907
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____10905  in
            Prims.op_Hat uu____10901 uu____10903  in
          Prims.op_Hat "Operation " uu____10899  in
        failwith uu____10897
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10914 = p_term false false e  in
        soft_parens_with_nesting uu____10914
    | FStar_Parser_AST.Const uu____10917 ->
        let uu____10918 = p_term false false e  in
        soft_parens_with_nesting uu____10918
    | FStar_Parser_AST.Op uu____10921 ->
        let uu____10928 = p_term false false e  in
        soft_parens_with_nesting uu____10928
    | FStar_Parser_AST.Tvar uu____10931 ->
        let uu____10932 = p_term false false e  in
        soft_parens_with_nesting uu____10932
    | FStar_Parser_AST.Var uu____10935 ->
        let uu____10936 = p_term false false e  in
        soft_parens_with_nesting uu____10936
    | FStar_Parser_AST.Name uu____10939 ->
        let uu____10940 = p_term false false e  in
        soft_parens_with_nesting uu____10940
    | FStar_Parser_AST.Construct uu____10943 ->
        let uu____10954 = p_term false false e  in
        soft_parens_with_nesting uu____10954
    | FStar_Parser_AST.Abs uu____10957 ->
        let uu____10964 = p_term false false e  in
        soft_parens_with_nesting uu____10964
    | FStar_Parser_AST.App uu____10967 ->
        let uu____10974 = p_term false false e  in
        soft_parens_with_nesting uu____10974
    | FStar_Parser_AST.Let uu____10977 ->
        let uu____10998 = p_term false false e  in
        soft_parens_with_nesting uu____10998
    | FStar_Parser_AST.LetOpen uu____11001 ->
        let uu____11006 = p_term false false e  in
        soft_parens_with_nesting uu____11006
    | FStar_Parser_AST.Seq uu____11009 ->
        let uu____11014 = p_term false false e  in
        soft_parens_with_nesting uu____11014
    | FStar_Parser_AST.Bind uu____11017 ->
        let uu____11024 = p_term false false e  in
        soft_parens_with_nesting uu____11024
    | FStar_Parser_AST.If uu____11027 ->
        let uu____11034 = p_term false false e  in
        soft_parens_with_nesting uu____11034
    | FStar_Parser_AST.Match uu____11037 ->
        let uu____11052 = p_term false false e  in
        soft_parens_with_nesting uu____11052
    | FStar_Parser_AST.TryWith uu____11055 ->
        let uu____11070 = p_term false false e  in
        soft_parens_with_nesting uu____11070
    | FStar_Parser_AST.Ascribed uu____11073 ->
        let uu____11082 = p_term false false e  in
        soft_parens_with_nesting uu____11082
    | FStar_Parser_AST.Record uu____11085 ->
        let uu____11098 = p_term false false e  in
        soft_parens_with_nesting uu____11098
    | FStar_Parser_AST.Project uu____11101 ->
        let uu____11106 = p_term false false e  in
        soft_parens_with_nesting uu____11106
    | FStar_Parser_AST.Product uu____11109 ->
        let uu____11116 = p_term false false e  in
        soft_parens_with_nesting uu____11116
    | FStar_Parser_AST.Sum uu____11119 ->
        let uu____11130 = p_term false false e  in
        soft_parens_with_nesting uu____11130
    | FStar_Parser_AST.QForall uu____11133 ->
        let uu____11146 = p_term false false e  in
        soft_parens_with_nesting uu____11146
    | FStar_Parser_AST.QExists uu____11149 ->
        let uu____11162 = p_term false false e  in
        soft_parens_with_nesting uu____11162
    | FStar_Parser_AST.Refine uu____11165 ->
        let uu____11170 = p_term false false e  in
        soft_parens_with_nesting uu____11170
    | FStar_Parser_AST.NamedTyp uu____11173 ->
        let uu____11178 = p_term false false e  in
        soft_parens_with_nesting uu____11178
    | FStar_Parser_AST.Requires uu____11181 ->
        let uu____11189 = p_term false false e  in
        soft_parens_with_nesting uu____11189
    | FStar_Parser_AST.Ensures uu____11192 ->
        let uu____11200 = p_term false false e  in
        soft_parens_with_nesting uu____11200
    | FStar_Parser_AST.Attributes uu____11203 ->
        let uu____11206 = p_term false false e  in
        soft_parens_with_nesting uu____11206
    | FStar_Parser_AST.Quote uu____11209 ->
        let uu____11214 = p_term false false e  in
        soft_parens_with_nesting uu____11214
    | FStar_Parser_AST.VQuote uu____11217 ->
        let uu____11218 = p_term false false e  in
        soft_parens_with_nesting uu____11218
    | FStar_Parser_AST.Antiquote uu____11221 ->
        let uu____11222 = p_term false false e  in
        soft_parens_with_nesting uu____11222
    | FStar_Parser_AST.CalcProof uu____11225 ->
        let uu____11234 = p_term false false e  in
        soft_parens_with_nesting uu____11234

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___42_11237  ->
    match uu___42_11237 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.strcat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11249) ->
        let uu____11252 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11252
    | FStar_Const.Const_bytearray (bytes,uu____11254) ->
        let uu____11259 =
          let uu____11260 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11260  in
        let uu____11261 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11259 uu____11261
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___40_11284 =
          match uu___40_11284 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___41_11291 =
          match uu___41_11291 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11306  ->
               match uu____11306 with
               | (s,w) ->
                   let uu____11313 = signedness s  in
                   let uu____11314 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11313 uu____11314)
            sign_width_opt
           in
        let uu____11315 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11315 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11319 = FStar_Range.string_of_range r  in str uu____11319
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11323 = p_quident lid  in
        let uu____11324 =
          let uu____11325 =
            let uu____11326 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11326  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11325  in
        FStar_Pprint.op_Hat_Hat uu____11323 uu____11324

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11329 = str "u#"  in
    let uu____11331 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11329 uu____11331

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11333;_},u1::u2::[])
        ->
        let uu____11339 =
          let uu____11340 = p_universeFrom u1  in
          let uu____11341 =
            let uu____11342 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11342  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11340 uu____11341  in
        FStar_Pprint.group uu____11339
    | FStar_Parser_AST.App uu____11343 ->
        let uu____11350 = head_and_args u  in
        (match uu____11350 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11376 =
                    let uu____11377 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11378 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11386  ->
                           match uu____11386 with
                           | (u1,uu____11392) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11377 uu____11378  in
                  FStar_Pprint.group uu____11376
              | uu____11393 ->
                  let uu____11394 =
                    let uu____11396 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11396
                     in
                  failwith uu____11394))
    | uu____11399 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11425 = FStar_Ident.text_of_id id1  in str uu____11425
    | FStar_Parser_AST.Paren u1 ->
        let uu____11428 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11428
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11429;_},uu____11430::uu____11431::[])
        ->
        let uu____11435 = p_universeFrom u  in
        soft_parens_with_nesting uu____11435
    | FStar_Parser_AST.App uu____11436 ->
        let uu____11443 = p_universeFrom u  in
        soft_parens_with_nesting uu____11443
    | uu____11444 ->
        let uu____11445 =
          let uu____11447 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11447
           in
        failwith uu____11445

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
       | FStar_Parser_AST.Module (uu____11536,decls) ->
           let uu____11542 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11542
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11551,decls,uu____11553) ->
           let uu____11560 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11560
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11620  ->
         match uu____11620 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11642)) -> false
      | ([],uu____11646) -> false
      | uu____11650 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11660 -> true
         | uu____11662 -> false)
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
        | FStar_Parser_AST.Module (uu____11705,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11711,decls,uu____11713) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11765 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11778;
                 FStar_Parser_AST.doc = uu____11779;
                 FStar_Parser_AST.quals = uu____11780;
                 FStar_Parser_AST.attrs = uu____11781;_}::uu____11782 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11788 =
                   let uu____11791 =
                     let uu____11794 = FStar_List.tl ds  in d :: uu____11794
                      in
                   d0 :: uu____11791  in
                 (uu____11788, (d0.FStar_Parser_AST.drange))
             | uu____11799 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11765 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11856 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11856 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11965 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11965, comments1))))))
  