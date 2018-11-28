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
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.bool)
  =
  fun args  ->
    FStar_Util.for_all
      (fun uu___110_275  ->
         match uu___110_275 with
         | (uu____281,FStar_Parser_AST.Nothing ) -> true
         | uu____283 -> false) args
  
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
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
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
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2)
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
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___111_1701  ->
    match uu___111_1701 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___112_1736  ->
      match uu___112_1736 with
      | FStar_Util.Inl c ->
          let uu____1749 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1749 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1765 .
    Prims.string ->
      ('Auu____1765,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
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
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,token
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___113_1993 =
    match uu___113_1993 with
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
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2118 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2118 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2170) ->
          assoc_levels
      | uu____2208 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____2241 .
    ('Auu____2241,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
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
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
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
  | Binders of (Prims.int,Prims.int,Prims.bool)
  FStar_Pervasives_Native.tuple3 
  | Arrows of (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2860 -> false
  
let (__proj__Binders__item___0 :
  annotation_style ->
    (Prims.int,Prims.int,Prims.bool) FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2913 -> false
  
let (__proj__Arrows__item___0 :
  annotation_style -> (Prims.int,Prims.int) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Arrows _0 -> _0 
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
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
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
  'Auu____3218 'Auu____3219 .
    ('Auu____3218 -> FStar_Pprint.document) ->
      'Auu____3218 ->
        FStar_Range.range -> 'Auu____3219 -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____3266 = FStar_ST.op_Bang comment_stack  in
            match uu____3266 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment =
                  if FStar_Util.starts_with c "//"
                  then
                    let uu____3339 = str c  in
                    FStar_Pprint.op_Hat_Hat uu____3339 FStar_Pprint.hardline
                  else
                    (let uu____3342 = str c  in
                     FStar_Pprint.op_Hat_Hat uu____3342 FStar_Pprint.hardline)
                   in
                let uu____3343 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____3343
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____3385 = FStar_Pprint.op_Hat_Hat acc comment  in
                    comments_before_pos uu____3385 print_pos lookahead_pos))
                else
                  (let uu____3388 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____3388))
             in
          let uu____3391 =
            let uu____3397 =
              let uu____3398 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____3398  in
            let uu____3399 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____3397 uu____3399  in
          match uu____3391 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____3408 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____3408
                else comments  in
              if comments1 = FStar_Pprint.empty
              then printed_e
              else
                (let uu____3420 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                    in
                 FStar_Pprint.group uu____3420)
  
let with_comment_sep :
  'Auu____3436 'Auu____3437 'Auu____3438 .
    ('Auu____3436 -> 'Auu____3437) ->
      'Auu____3436 ->
        FStar_Range.range ->
          'Auu____3438 ->
            (FStar_Pprint.document,'Auu____3437)
              FStar_Pervasives_Native.tuple2
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        fun origin  ->
          let rec comments_before_pos acc print_pos lookahead_pos =
            let uu____3489 = FStar_ST.op_Bang comment_stack  in
            match uu____3489 with
            | [] -> (acc, false)
            | (c,crange)::cs ->
                let comment = str c  in
                let uu____3560 =
                  FStar_Range.range_before_pos crange print_pos  in
                if uu____3560
                then
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let uu____3602 =
                      if acc = FStar_Pprint.empty
                      then comment
                      else
                        (let uu____3606 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                             comment
                            in
                         FStar_Pprint.op_Hat_Hat acc uu____3606)
                       in
                    comments_before_pos uu____3602 print_pos lookahead_pos))
                else
                  (let uu____3609 =
                     FStar_Range.range_before_pos crange lookahead_pos  in
                   (acc, uu____3609))
             in
          let uu____3612 =
            let uu____3618 =
              let uu____3619 = FStar_Range.start_of_range tmrange  in
              FStar_Range.end_of_line uu____3619  in
            let uu____3620 = FStar_Range.end_of_range tmrange  in
            comments_before_pos FStar_Pprint.empty uu____3618 uu____3620  in
          match uu____3612 with
          | (comments,has_lookahead) ->
              let printed_e = printer tm  in
              let comments1 =
                if has_lookahead
                then
                  let pos = FStar_Range.end_of_range tmrange  in
                  let uu____3633 = comments_before_pos comments pos pos  in
                  FStar_Pervasives_Native.fst uu____3633
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
                let uu____3686 = FStar_ST.op_Bang comment_stack  in
                match uu____3686 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3780 =
                          let uu____3782 =
                            let uu____3784 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3784  in
                          uu____3782 - lbegin  in
                        max k uu____3780  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3789 =
                          let uu____3790 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3791 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3790 uu____3791  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3789  in
                      let uu____3792 =
                        let uu____3794 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3794  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3792 pos meta_decl doc2 true init1))
                | uu____3797 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3810 = FStar_Range.line_of_pos pos  in
                         uu____3810 - lbegin  in
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
                       let uu____3852 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3852)
  
let separate_map_with_comments :
  'Auu____3866 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3866 -> FStar_Pprint.document) ->
          'Auu____3866 Prims.list ->
            ('Auu____3866 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3925 x =
              match uu____3925 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3944 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3944 meta_decl doc1 false false
                     in
                  let uu____3948 =
                    let uu____3950 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3950  in
                  let uu____3951 =
                    let uu____3952 =
                      let uu____3953 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3953  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3952  in
                  (uu____3948, uu____3951)
               in
            let uu____3955 =
              let uu____3962 = FStar_List.hd xs  in
              let uu____3963 = FStar_List.tl xs  in (uu____3962, uu____3963)
               in
            match uu____3955 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3981 =
                    let uu____3983 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3983  in
                  let uu____3984 =
                    let uu____3985 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3985  in
                  (uu____3981, uu____3984)  in
                let uu____3987 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3987
  
let separate_map_with_comments_kw :
  'Auu____4014 'Auu____4015 .
    'Auu____4014 ->
      'Auu____4014 ->
        ('Auu____4014 -> 'Auu____4015 -> FStar_Pprint.document) ->
          'Auu____4015 Prims.list ->
            ('Auu____4015 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4079 x =
              match uu____4079 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4098 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4098 meta_decl doc1 false false
                     in
                  let uu____4102 =
                    let uu____4104 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4104  in
                  let uu____4105 =
                    let uu____4106 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4106  in
                  (uu____4102, uu____4105)
               in
            let uu____4108 =
              let uu____4115 = FStar_List.hd xs  in
              let uu____4116 = FStar_List.tl xs  in (uu____4115, uu____4116)
               in
            match uu____4108 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4134 =
                    let uu____4136 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4136  in
                  let uu____4137 = f prefix1 x  in (uu____4134, uu____4137)
                   in
                let uu____4139 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4139
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5116)) ->
          let uu____5119 =
            let uu____5121 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5121 FStar_Util.is_upper  in
          if uu____5119
          then
            let uu____5127 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5127 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5130 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5137 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5140 =
      let uu____5141 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5142 =
        let uu____5143 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5143  in
      FStar_Pprint.op_Hat_Hat uu____5141 uu____5142  in
    FStar_Pprint.op_Hat_Hat uu____5137 uu____5140

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5145 ->
        let uu____5146 =
          let uu____5147 = str "@ "  in
          let uu____5149 =
            let uu____5150 =
              let uu____5151 =
                let uu____5152 =
                  let uu____5153 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5153  in
                FStar_Pprint.op_Hat_Hat uu____5152 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5151  in
            FStar_Pprint.op_Hat_Hat uu____5150 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5147 uu____5149  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5146

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5156  ->
    match uu____5156 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5204 =
                match uu____5204 with
                | (kwd,arg) ->
                    let uu____5217 = str "@"  in
                    let uu____5219 =
                      let uu____5220 = str kwd  in
                      let uu____5221 =
                        let uu____5222 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5222
                         in
                      FStar_Pprint.op_Hat_Hat uu____5220 uu____5221  in
                    FStar_Pprint.op_Hat_Hat uu____5217 uu____5219
                 in
              let uu____5223 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5223 FStar_Pprint.hardline
           in
        let uu____5230 =
          let uu____5231 =
            let uu____5232 =
              let uu____5233 = str doc1  in
              let uu____5234 =
                let uu____5235 =
                  let uu____5236 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5236  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5235  in
              FStar_Pprint.op_Hat_Hat uu____5233 uu____5234  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5232  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5231  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5230

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5240 =
          let uu____5241 = str "val"  in
          let uu____5243 =
            let uu____5244 =
              let uu____5245 = p_lident lid  in
              let uu____5246 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5245 uu____5246  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5244  in
          FStar_Pprint.op_Hat_Hat uu____5241 uu____5243  in
        let uu____5247 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5240 uu____5247
    | FStar_Parser_AST.TopLevelLet (uu____5250,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5275 =
               let uu____5276 = str "let"  in p_letlhs uu____5276 lb false
                in
             FStar_Pprint.group uu____5275) lbs
    | uu____5279 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_5294 =
          match uu___114_5294 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5302 = f x  in
              let uu____5303 =
                let uu____5304 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5304  in
              FStar_Pprint.op_Hat_Hat uu____5302 uu____5303
           in
        let uu____5305 = str "["  in
        let uu____5307 =
          let uu____5308 = p_list' l  in
          let uu____5309 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5308 uu____5309  in
        FStar_Pprint.op_Hat_Hat uu____5305 uu____5307

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5313 =
          let uu____5314 = str "open"  in
          let uu____5316 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5314 uu____5316  in
        FStar_Pprint.group uu____5313
    | FStar_Parser_AST.Include uid ->
        let uu____5318 =
          let uu____5319 = str "include"  in
          let uu____5321 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5319 uu____5321  in
        FStar_Pprint.group uu____5318
    | FStar_Parser_AST.Friend uid ->
        let uu____5323 =
          let uu____5324 = str "friend"  in
          let uu____5326 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5324 uu____5326  in
        FStar_Pprint.group uu____5323
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5329 =
          let uu____5330 = str "module"  in
          let uu____5332 =
            let uu____5333 =
              let uu____5334 = p_uident uid1  in
              let uu____5335 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5334 uu____5335  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5333  in
          FStar_Pprint.op_Hat_Hat uu____5330 uu____5332  in
        let uu____5336 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5329 uu____5336
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5338 =
          let uu____5339 = str "module"  in
          let uu____5341 =
            let uu____5342 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5342  in
          FStar_Pprint.op_Hat_Hat uu____5339 uu____5341  in
        FStar_Pprint.group uu____5338
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5343,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5380 = str "effect"  in
          let uu____5382 =
            let uu____5383 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5383  in
          FStar_Pprint.op_Hat_Hat uu____5380 uu____5382  in
        let uu____5384 =
          let uu____5385 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5385 FStar_Pprint.equals
           in
        let uu____5388 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5384 uu____5388
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5419 =
          let uu____5420 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5420  in
        let uu____5433 =
          let uu____5434 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5472 =
                    let uu____5473 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5473 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5472)) uu____5434
           in
        FStar_Pprint.op_Hat_Hat uu____5419 uu____5433
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5490 = str "let"  in
          let uu____5492 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5490 uu____5492  in
        let uu____5493 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5493 p_letbinding lbs
          (fun uu____5503  ->
             match uu____5503 with
             | (p,t) ->
                 let uu____5510 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5510;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5516 =
          let uu____5517 = str "val"  in
          let uu____5519 =
            let uu____5520 =
              let uu____5521 = p_lident lid  in
              let uu____5522 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5521 uu____5522  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5520  in
          FStar_Pprint.op_Hat_Hat uu____5517 uu____5519  in
        FStar_All.pipe_left FStar_Pprint.group uu____5516
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5527 =
            let uu____5529 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5529 FStar_Util.is_upper  in
          if uu____5527
          then FStar_Pprint.empty
          else
            (let uu____5537 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5537 FStar_Pprint.space)
           in
        let uu____5539 =
          let uu____5540 = p_ident id1  in
          let uu____5541 =
            let uu____5542 =
              let uu____5543 =
                let uu____5544 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5544  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5543  in
            FStar_Pprint.group uu____5542  in
          FStar_Pprint.op_Hat_Hat uu____5540 uu____5541  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5539
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5553 = str "exception"  in
        let uu____5555 =
          let uu____5556 =
            let uu____5557 = p_uident uid  in
            let uu____5558 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5562 =
                     let uu____5563 = str "of"  in
                     let uu____5565 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5563 uu____5565  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5562) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5557 uu____5558  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5556  in
        FStar_Pprint.op_Hat_Hat uu____5553 uu____5555
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5569 = str "new_effect"  in
        let uu____5571 =
          let uu____5572 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5572  in
        FStar_Pprint.op_Hat_Hat uu____5569 uu____5571
    | FStar_Parser_AST.SubEffect se ->
        let uu____5574 = str "sub_effect"  in
        let uu____5576 =
          let uu____5577 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5577  in
        FStar_Pprint.op_Hat_Hat uu____5574 uu____5576
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5580 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5582,uu____5583) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5611 = str "%splice"  in
        let uu____5613 =
          let uu____5614 =
            let uu____5615 = str ";"  in p_list p_uident uu____5615 ids  in
          let uu____5617 =
            let uu____5618 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5618  in
          FStar_Pprint.op_Hat_Hat uu____5614 uu____5617  in
        FStar_Pprint.op_Hat_Hat uu____5611 uu____5613

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_5621  ->
    match uu___115_5621 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5624 = str "#set-options"  in
        let uu____5626 =
          let uu____5627 =
            let uu____5628 = str s  in FStar_Pprint.dquotes uu____5628  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5627  in
        FStar_Pprint.op_Hat_Hat uu____5624 uu____5626
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5633 = str "#reset-options"  in
        let uu____5635 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5641 =
                 let uu____5642 = str s  in FStar_Pprint.dquotes uu____5642
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5641) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5633 uu____5635
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5647 = str "#push-options"  in
        let uu____5649 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5655 =
                 let uu____5656 = str s  in FStar_Pprint.dquotes uu____5656
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5655) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5647 uu____5649
    | FStar_Parser_AST.PopOptions  -> str "#pop-options"
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5687  ->
      match uu____5687 with
      | (typedecl,fsdoc_opt) ->
          let uu____5700 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5700 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5725 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5725
               else
                 (let uu____5728 =
                    let uu____5729 =
                      let uu____5730 =
                        let uu____5731 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5731 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5730  in
                    let uu____5732 =
                      let uu____5733 =
                        let uu____5734 =
                          let uu____5735 =
                            let uu____5736 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5736  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5735
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5734
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5733  in
                    FStar_Pprint.ifflat uu____5729 uu____5732  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5728))

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,FStar_Pprint.document,FStar_Pprint.document,
        FStar_Pprint.document -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple4)
  =
  fun pre  ->
    fun uu___116_5739  ->
      match uu___116_5739 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5768 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5768, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5785 = p_typ_sep false false t  in
          (match uu____5785 with
           | (comm,doc1) ->
               let uu____5805 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5805, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5861 =
            match uu____5861 with
            | (lid1,t,doc_opt) ->
                let uu____5878 =
                  let uu____5883 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5883 "!1"
                   in
                (match uu____5878 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5903 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5903  in
          let uu____5912 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5912, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5979 =
            match uu____5979 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____6008 =
                    let uu____6009 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____6009  in
                  FStar_Range.extend_to_end_of_line uu____6008  in
                let uu____6014 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range "!2"
                   in
                (match uu____6014 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6055 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6055, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6060  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6060 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6095 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6095  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6097 =
                        let uu____6100 =
                          let uu____6103 = p_fsdoc fsdoc  in
                          let uu____6104 =
                            let uu____6107 = cont lid_doc  in [uu____6107]
                             in
                          uu____6103 :: uu____6104  in
                        kw :: uu____6100  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6097
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6114 =
                        let uu____6115 =
                          let uu____6116 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6116 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6115
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6114
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6136 =
                          let uu____6137 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6137  in
                        prefix2 uu____6136 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6139  ->
      match uu____6139 with
      | (lid,t,doc_opt) ->
          let uu____6156 =
            let uu____6157 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6158 =
              let uu____6159 = p_lident lid  in
              let uu____6160 =
                let uu____6161 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6161  in
              FStar_Pprint.op_Hat_Hat uu____6159 uu____6160  in
            FStar_Pprint.op_Hat_Hat uu____6157 uu____6158  in
          FStar_Pprint.group uu____6156

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____6163  ->
    match uu____6163 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6197 =
            let uu____6198 =
              let uu____6199 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6199  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6198  in
          FStar_Pprint.group uu____6197  in
        let uu____6200 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6201 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6205 =
                 let uu____6206 =
                   let uu____6207 =
                     let uu____6208 =
                       let uu____6209 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6209
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6208  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6207  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6206  in
               FStar_Pprint.group uu____6205) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6200 uu____6201

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6213  ->
      fun inner_let  ->
        match uu____6213 with
        | (pat,uu____6221) ->
            let uu____6222 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6274 =
                    let uu____6281 =
                      let uu____6286 =
                        let uu____6287 =
                          let uu____6288 =
                            let uu____6289 = str "by"  in
                            let uu____6291 =
                              let uu____6292 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6292
                               in
                            FStar_Pprint.op_Hat_Hat uu____6289 uu____6291  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6288
                           in
                        FStar_Pprint.group uu____6287  in
                      (t, uu____6286)  in
                    FStar_Pervasives_Native.Some uu____6281  in
                  (pat1, uu____6274)
              | uu____6303 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6222 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6329);
                         FStar_Parser_AST.prange = uu____6330;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6347 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6347 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6353 =
                        if inner_let
                        then
                          let uu____6367 = pats_as_binders_if_possible pats
                             in
                          match uu____6367 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6390 = pats_as_binders_if_possible pats
                              in
                           match uu____6390 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6353 with
                       | (terms,style) ->
                           let uu____6417 =
                             let uu____6418 =
                               let uu____6419 =
                                 let uu____6420 = p_lident lid  in
                                 let uu____6421 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6420
                                   uu____6421
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6419
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6418  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6417)
                  | uu____6424 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6432 =
                              let uu____6433 =
                                let uu____6434 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6434
                                 in
                              FStar_Pprint.group uu____6433  in
                            FStar_Pprint.op_Hat_Hat uu____6432 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6445 =
                        let uu____6446 =
                          let uu____6447 =
                            let uu____6448 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6448  in
                          FStar_Pprint.group uu____6447  in
                        FStar_Pprint.op_Hat_Hat uu____6446 ascr_doc  in
                      FStar_Pprint.group uu____6445))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6450  ->
      match uu____6450 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6459 = p_term_sep false false e  in
          (match uu____6459 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6469 =
                 let uu____6470 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6470  in
               let uu____6471 =
                 let uu____6472 =
                   let uu____6473 =
                     let uu____6474 =
                       let uu____6475 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6475
                        in
                     FStar_Pprint.group uu____6474  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6473  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6472  in
               FStar_Pprint.ifflat uu____6469 uu____6471)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_6476  ->
    match uu___117_6476 with
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
        let uu____6501 = p_uident uid  in
        let uu____6502 = p_binders true bs  in
        let uu____6504 =
          let uu____6505 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6505  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6501 uu____6502 uu____6504

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
          let uu____6520 =
            let uu____6521 =
              let uu____6522 =
                let uu____6523 = p_uident uid  in
                let uu____6524 = p_binders true bs  in
                let uu____6526 =
                  let uu____6527 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6527  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6523 uu____6524 uu____6526
                 in
              FStar_Pprint.group uu____6522  in
            let uu____6532 =
              let uu____6533 = str "with"  in
              let uu____6535 =
                let uu____6536 =
                  let uu____6537 =
                    let uu____6538 =
                      let uu____6539 =
                        let uu____6540 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6540
                         in
                      separate_map_last uu____6539 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6538  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6537  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6536  in
              FStar_Pprint.op_Hat_Hat uu____6533 uu____6535  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6521 uu____6532  in
          braces_with_nesting uu____6520

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6544,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6577 =
            let uu____6578 = p_lident lid  in
            let uu____6579 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6578 uu____6579  in
          let uu____6580 = p_simpleTerm ps false e  in
          prefix2 uu____6577 uu____6580
      | uu____6582 ->
          let uu____6583 =
            let uu____6585 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6585
             in
          failwith uu____6583

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6668 =
        match uu____6668 with
        | (kwd,t) ->
            let uu____6679 =
              let uu____6680 = str kwd  in
              let uu____6681 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6680 uu____6681  in
            let uu____6682 = p_simpleTerm ps false t  in
            prefix2 uu____6679 uu____6682
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6689 =
      let uu____6690 =
        let uu____6691 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6692 =
          let uu____6693 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6693  in
        FStar_Pprint.op_Hat_Hat uu____6691 uu____6692  in
      let uu____6695 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6690 uu____6695  in
    let uu____6696 =
      let uu____6697 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6697  in
    FStar_Pprint.op_Hat_Hat uu____6689 uu____6696

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_6698  ->
    match uu___118_6698 with
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
        let uu____6718 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6718 FStar_Pprint.hardline
    | uu____6719 ->
        let uu____6720 =
          let uu____6721 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6721  in
        FStar_Pprint.op_Hat_Hat uu____6720 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_6724  ->
    match uu___119_6724 with
    | FStar_Parser_AST.Rec  ->
        let uu____6725 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6725
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_6727  ->
    match uu___120_6727 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____6731,e) ->
             let uu____6737 = str "#["  in
             let uu____6739 =
               let uu____6740 = p_term false false e  in
               let uu____6743 =
                 let uu____6744 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____6744 break1  in
               FStar_Pprint.op_Hat_Hat uu____6740 uu____6743  in
             FStar_Pprint.op_Hat_Hat uu____6737 uu____6739
         | uu____6746 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6752 =
          let uu____6753 =
            let uu____6754 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6754  in
          FStar_Pprint.separate_map uu____6753 p_tuplePattern pats  in
        FStar_Pprint.group uu____6752
    | uu____6755 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6764 =
          let uu____6765 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6765 p_constructorPattern pats  in
        FStar_Pprint.group uu____6764
    | uu____6766 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6769;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6774 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6775 = p_constructorPattern hd1  in
        let uu____6776 = p_constructorPattern tl1  in
        infix0 uu____6774 uu____6775 uu____6776
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6778;_},pats)
        ->
        let uu____6784 = p_quident uid  in
        let uu____6785 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6784 uu____6785
    | uu____6786 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6802;
               FStar_Parser_AST.blevel = uu____6803;
               FStar_Parser_AST.aqual = uu____6804;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6813 =
               let uu____6814 = p_ident lid  in
               p_refinement aqual uu____6814 t1 phi  in
             soft_parens_with_nesting uu____6813
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6817;
               FStar_Parser_AST.blevel = uu____6818;
               FStar_Parser_AST.aqual = uu____6819;_},phi))
             ->
             let uu____6825 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6825
         | uu____6826 ->
             let uu____6831 =
               let uu____6832 = p_tuplePattern pat  in
               let uu____6833 =
                 let uu____6834 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6834
                  in
               FStar_Pprint.op_Hat_Hat uu____6832 uu____6833  in
             soft_parens_with_nesting uu____6831)
    | FStar_Parser_AST.PatList pats ->
        let uu____6838 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6838 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6857 =
          match uu____6857 with
          | (lid,pat) ->
              let uu____6864 = p_qlident lid  in
              let uu____6865 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6864 uu____6865
           in
        let uu____6866 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6866
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6878 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6879 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6880 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6878 uu____6879 uu____6880
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6891 =
          let uu____6892 =
            let uu____6893 =
              let uu____6894 = FStar_Ident.text_of_id op  in str uu____6894
               in
            let uu____6896 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6893 uu____6896  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6892  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6891
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6900 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6900 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6908 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6909 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6908 uu____6909
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6911 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6915;
           FStar_Parser_AST.prange = uu____6916;_},uu____6917)
        ->
        let uu____6922 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6922
    | FStar_Parser_AST.PatTuple (uu____6923,false ) ->
        let uu____6930 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6930
    | uu____6931 ->
        let uu____6932 =
          let uu____6934 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6934  in
        failwith uu____6932

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6939;_},uu____6940)
        -> true
    | uu____6947 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6953) -> true
    | uu____6955 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6962 = p_binder' is_atomic b  in
      match uu____6962 with
      | (b',t',catf) ->
          (match t' with
           | FStar_Pervasives_Native.Some typ -> catf b' typ
           | FStar_Pervasives_Native.None  -> b')

and (p_binder' :
  Prims.bool ->
    FStar_Parser_AST.binder ->
      (FStar_Pprint.document,FStar_Pprint.document
                               FStar_Pervasives_Native.option,catf)
        FStar_Pervasives_Native.tuple3)
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____7001 =
            let uu____7002 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____7003 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____7002 uu____7003  in
          (uu____7001, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____7009 = p_lident lid  in
          (uu____7009, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____7016 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____7027;
                   FStar_Parser_AST.blevel = uu____7028;
                   FStar_Parser_AST.aqual = uu____7029;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____7034 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____7034 t1 phi
            | uu____7035 ->
                let t' =
                  let uu____7037 = is_typ_tuple t  in
                  if uu____7037
                  then
                    let uu____7040 = p_tmFormula t  in
                    soft_parens_with_nesting uu____7040
                  else p_tmFormula t  in
                let uu____7043 =
                  let uu____7044 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____7045 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____7044 uu____7045  in
                (uu____7043, t')
             in
          (match uu____7016 with
           | (b',t') ->
               let catf =
                 let uu____7063 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7063
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7070 =
                         let uu____7071 =
                           let uu____7072 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7072
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7071
                          in
                       FStar_Pprint.group uu____7070
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7077 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7077)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7086 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7114;
                  FStar_Parser_AST.blevel = uu____7115;
                  FStar_Parser_AST.aqual = uu____7116;_},phi)
               ->
               let uu____7120 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7120 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7141 ->
               if is_atomic
               then
                 let uu____7153 = p_atomicTerm t  in
                 (uu____7153, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7160 = p_appTerm t  in
                  (uu____7160, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7171 = p_refinement' aqual_opt binder t phi  in
          match uu____7171 with | (b,typ) -> cat_with_colon b typ

and (p_refinement' :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.term ->
          (FStar_Pprint.document,FStar_Pprint.document)
            FStar_Pervasives_Native.tuple2)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____7187 -> false
            | FStar_Parser_AST.App uu____7199 -> false
            | FStar_Parser_AST.Op uu____7207 -> false
            | uu____7215 -> true  in
          let uu____7217 = p_noSeqTerm false false phi  in
          match uu____7217 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7234 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7234)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7243 =
                let uu____7244 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7244 binder  in
              let uu____7245 =
                let uu____7246 = p_appTerm t  in
                let uu____7247 =
                  let uu____7248 =
                    let uu____7249 =
                      let uu____7250 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7251 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7250 uu____7251  in
                    FStar_Pprint.group uu____7249  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7248
                   in
                FStar_Pprint.op_Hat_Hat uu____7246 uu____7247  in
              (uu____7243, uu____7245)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7265 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7265

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7269 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7272 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7272)
       in
    if uu____7269
    then FStar_Pprint.underscore
    else (let uu____7277 = FStar_Ident.text_of_id lid  in str uu____7277)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7280 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7283 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7283)
       in
    if uu____7280
    then FStar_Pprint.underscore
    else (let uu____7288 = FStar_Ident.text_of_lid lid  in str uu____7288)

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
          let uu____7309 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7309
        else
          (let uu____7312 =
             let uu____7313 =
               let uu____7314 =
                 let uu____7315 =
                   let uu____7316 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7316  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7315  in
               FStar_Pprint.group uu____7314  in
             let uu____7317 =
               let uu____7318 =
                 let uu____7319 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7319  in
               FStar_Pprint.op_Hat_Hat comm uu____7318  in
             FStar_Pprint.ifflat uu____7313 uu____7317  in
           FStar_All.pipe_left FStar_Pprint.group uu____7312)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7327 = p_noSeqTerm true false e1  in
            (match uu____7327 with
             | (comm,t1) ->
                 let uu____7336 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7337 =
                   let uu____7338 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7338
                    in
                 FStar_Pprint.op_Hat_Hat uu____7336 uu____7337)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7342 =
              let uu____7343 =
                let uu____7344 =
                  let uu____7345 = p_lident x  in
                  let uu____7346 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7345 uu____7346  in
                let uu____7347 =
                  let uu____7348 = p_noSeqTermAndComment true false e1  in
                  let uu____7351 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7348 uu____7351  in
                op_Hat_Slash_Plus_Hat uu____7344 uu____7347  in
              FStar_Pprint.group uu____7343  in
            let uu____7352 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7342 uu____7352
        | uu____7353 ->
            let uu____7354 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7354

and (p_term_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7366 = p_noSeqTerm true false e1  in
            (match uu____7366 with
             | (comm,t1) ->
                 let uu____7379 =
                   let uu____7380 =
                     let uu____7381 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7381  in
                   let uu____7382 =
                     let uu____7383 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7383
                      in
                   FStar_Pprint.op_Hat_Hat uu____7380 uu____7382  in
                 (comm, uu____7379))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7387 =
              let uu____7388 =
                let uu____7389 =
                  let uu____7390 =
                    let uu____7391 = p_lident x  in
                    let uu____7392 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7391 uu____7392  in
                  let uu____7393 =
                    let uu____7394 = p_noSeqTermAndComment true false e1  in
                    let uu____7397 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7394 uu____7397  in
                  op_Hat_Slash_Plus_Hat uu____7390 uu____7393  in
                FStar_Pprint.group uu____7389  in
              let uu____7398 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7388 uu____7398  in
            (FStar_Pprint.empty, uu____7387)
        | uu____7399 -> p_noSeqTerm ps pb e

and (p_noSeqTerm :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range "!3"

and (p_noSeqTermAndComment :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range "!3"

and (p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____7423 =
              let uu____7424 = p_tmIff e1  in
              let uu____7425 =
                let uu____7426 =
                  let uu____7427 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7427
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7426  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7424 uu____7425  in
            FStar_Pprint.group uu____7423
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7433 =
              let uu____7434 = p_tmIff e1  in
              let uu____7435 =
                let uu____7436 =
                  let uu____7437 =
                    let uu____7438 = p_typ false false t  in
                    let uu____7441 =
                      let uu____7442 = str "by"  in
                      let uu____7444 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7442 uu____7444  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7438 uu____7441  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7437
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7436  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7434 uu____7435  in
            FStar_Pprint.group uu____7433
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7445;_},e1::e2::e3::[])
            ->
            let uu____7452 =
              let uu____7453 =
                let uu____7454 =
                  let uu____7455 = p_atomicTermNotQUident e1  in
                  let uu____7456 =
                    let uu____7457 =
                      let uu____7458 =
                        let uu____7459 = p_term false false e2  in
                        soft_parens_with_nesting uu____7459  in
                      let uu____7462 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7458 uu____7462  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7457  in
                  FStar_Pprint.op_Hat_Hat uu____7455 uu____7456  in
                FStar_Pprint.group uu____7454  in
              let uu____7463 =
                let uu____7464 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7464  in
              FStar_Pprint.op_Hat_Hat uu____7453 uu____7463  in
            FStar_Pprint.group uu____7452
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7465;_},e1::e2::e3::[])
            ->
            let uu____7472 =
              let uu____7473 =
                let uu____7474 =
                  let uu____7475 = p_atomicTermNotQUident e1  in
                  let uu____7476 =
                    let uu____7477 =
                      let uu____7478 =
                        let uu____7479 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7479  in
                      let uu____7482 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7478 uu____7482  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7477  in
                  FStar_Pprint.op_Hat_Hat uu____7475 uu____7476  in
                FStar_Pprint.group uu____7474  in
              let uu____7483 =
                let uu____7484 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7484  in
              FStar_Pprint.op_Hat_Hat uu____7473 uu____7483  in
            FStar_Pprint.group uu____7472
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7494 =
              let uu____7495 = str "requires"  in
              let uu____7497 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7495 uu____7497  in
            FStar_Pprint.group uu____7494
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7507 =
              let uu____7508 = str "ensures"  in
              let uu____7510 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7508 uu____7510  in
            FStar_Pprint.group uu____7507
        | FStar_Parser_AST.Attributes es ->
            let uu____7514 =
              let uu____7515 = str "attributes"  in
              let uu____7517 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7515 uu____7517  in
            FStar_Pprint.group uu____7514
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7522 =
                let uu____7523 =
                  let uu____7524 = str "if"  in
                  let uu____7526 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7524 uu____7526  in
                let uu____7529 =
                  let uu____7530 = str "then"  in
                  let uu____7532 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7530 uu____7532  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7523 uu____7529  in
              FStar_Pprint.group uu____7522
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7536,uu____7537,e31) when
                     is_unit e31 ->
                     let uu____7539 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7539
                 | uu____7542 -> p_noSeqTermAndComment false false e2  in
               let uu____7545 =
                 let uu____7546 =
                   let uu____7547 = str "if"  in
                   let uu____7549 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7547 uu____7549  in
                 let uu____7552 =
                   let uu____7553 =
                     let uu____7554 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7554 e2_doc  in
                   let uu____7556 =
                     let uu____7557 = str "else"  in
                     let uu____7559 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7557 uu____7559  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7553 uu____7556  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7546 uu____7552  in
               FStar_Pprint.group uu____7545)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7582 =
              let uu____7583 =
                let uu____7584 =
                  let uu____7585 = str "try"  in
                  let uu____7587 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7585 uu____7587  in
                let uu____7590 =
                  let uu____7591 = str "with"  in
                  let uu____7593 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7591 uu____7593  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7584 uu____7590  in
              FStar_Pprint.group uu____7583  in
            let uu____7602 = paren_if (ps || pb)  in uu____7602 uu____7582
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7629 =
              let uu____7630 =
                let uu____7631 =
                  let uu____7632 = str "match"  in
                  let uu____7634 = p_noSeqTermAndComment false false e1  in
                  let uu____7637 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7632 uu____7634 uu____7637
                   in
                let uu____7641 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7631 uu____7641  in
              FStar_Pprint.group uu____7630  in
            let uu____7650 = paren_if (ps || pb)  in uu____7650 uu____7629
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7657 =
              let uu____7658 =
                let uu____7659 =
                  let uu____7660 = str "let open"  in
                  let uu____7662 = p_quident uid  in
                  let uu____7663 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7660 uu____7662 uu____7663
                   in
                let uu____7667 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7659 uu____7667  in
              FStar_Pprint.group uu____7658  in
            let uu____7669 = paren_if ps  in uu____7669 uu____7657
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7734 is_last =
              match uu____7734 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7768 =
                          let uu____7769 = str "let"  in
                          let uu____7771 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7769 uu____7771
                           in
                        FStar_Pprint.group uu____7768
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7774 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7780 = p_term_sep false false e2  in
                  (match uu____7780 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7790 =
                         if is_last
                         then
                           let uu____7792 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7793 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7792 doc_expr1
                             uu____7793
                         else
                           (let uu____7799 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7799)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7790)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7850 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7850
                     else
                       (let uu____7861 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7861)) lbs
               in
            let lbs_doc =
              let uu____7871 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7871  in
            let uu____7872 =
              let uu____7873 =
                let uu____7874 =
                  let uu____7875 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7875
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7874  in
              FStar_Pprint.group uu____7873  in
            let uu____7877 = paren_if ps  in uu____7877 uu____7872
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7884;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7887;
                                                             FStar_Parser_AST.level
                                                               = uu____7888;_})
            when matches_var maybe_x x ->
            let uu____7915 =
              let uu____7916 =
                let uu____7917 = str "function"  in
                let uu____7919 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7917 uu____7919  in
              FStar_Pprint.group uu____7916  in
            let uu____7928 = paren_if (ps || pb)  in uu____7928 uu____7915
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7934 =
              let uu____7935 = str "quote"  in
              let uu____7937 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7935 uu____7937  in
            FStar_Pprint.group uu____7934
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7939 =
              let uu____7940 = str "`"  in
              let uu____7942 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7940 uu____7942  in
            FStar_Pprint.group uu____7939
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7944 =
              let uu____7945 = str "`%"  in
              let uu____7947 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7945 uu____7947  in
            FStar_Pprint.group uu____7944
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7949;
              FStar_Parser_AST.level = uu____7950;_}
            ->
            let uu____7951 =
              let uu____7952 = str "`@"  in
              let uu____7954 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7952 uu____7954  in
            FStar_Pprint.group uu____7951
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7956 =
              let uu____7957 = str "`#"  in
              let uu____7959 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7957 uu____7959  in
            FStar_Pprint.group uu____7956
        | uu____7960 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_7961  ->
    match uu___121_7961 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7973 =
          let uu____7974 = str "[@"  in
          let uu____7976 =
            let uu____7977 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7978 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7977 uu____7978  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7974 uu____7976  in
        FStar_Pprint.group uu____7973

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range "!4"

and (p_typ_sep :
  Prims.bool ->
    Prims.bool ->
      FStar_Parser_AST.term ->
        (FStar_Pprint.document,FStar_Pprint.document)
          FStar_Pervasives_Native.tuple2)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        with_comment_sep (p_typ' ps pb) e e.FStar_Parser_AST.range "!4"

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
                 let uu____8019 =
                   let uu____8020 =
                     let uu____8021 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8021 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8020 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8019 term_doc
             | pats ->
                 let uu____8029 =
                   let uu____8030 =
                     let uu____8031 =
                       let uu____8032 =
                         let uu____8033 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8033
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8032 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8036 = p_trigger trigger  in
                     prefix2 uu____8031 uu____8036  in
                   FStar_Pprint.group uu____8030  in
                 prefix2 uu____8029 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8057 =
                   let uu____8058 =
                     let uu____8059 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8059 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8058 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8057 term_doc
             | pats ->
                 let uu____8067 =
                   let uu____8068 =
                     let uu____8069 =
                       let uu____8070 =
                         let uu____8071 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8071
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8070 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8074 = p_trigger trigger  in
                     prefix2 uu____8069 uu____8074  in
                   FStar_Pprint.group uu____8068  in
                 prefix2 uu____8067 term_doc)
        | uu____8075 -> p_simpleTerm ps pb e

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
            "!41"

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
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8101
      else
        (let uu____8112 =
           let uu____8113 =
             let uu____8114 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8114  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8113  in
         FStar_Pprint.group uu____8112)

and (collapse_pats :
  (FStar_Pprint.document,FStar_Pprint.document)
    FStar_Pervasives_Native.tuple2 Prims.list ->
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
    (FStar_Pprint.document Prims.list,annotation_style)
      FStar_Pervasives_Native.tuple2)
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
        (uu____8523,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8540 = FStar_List.map p_atomicPattern pats  in
        (uu____8540,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8552 -> str "forall"
    | FStar_Parser_AST.QExists uu____8566 -> str "exists"
    | uu____8580 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_8582  ->
    match uu___122_8582 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8594 =
          let uu____8595 =
            let uu____8596 =
              let uu____8597 = str "pattern"  in
              let uu____8599 =
                let uu____8600 =
                  let uu____8601 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8601
                   in
                FStar_Pprint.op_Hat_Hat uu____8600 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8597 uu____8599  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8596  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8595  in
        FStar_Pprint.group uu____8594

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8609 = str "\\/"  in
    FStar_Pprint.separate_map uu____8609 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8616 =
      let uu____8617 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8617 p_appTerm pats  in
    FStar_Pprint.group uu____8616

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8629 = p_term_sep false pb e1  in
            (match uu____8629 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8638 = str "fun"  in
                   let uu____8640 =
                     let uu____8641 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8641
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8638 uu____8640  in
                 let uu____8642 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8644 =
                       let uu____8645 =
                         let uu____8646 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8646  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8645
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8644
                   else
                     (let uu____8649 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8649)
                    in
                 let uu____8650 = paren_if ps  in uu____8650 uu____8642)
        | uu____8655 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8663  ->
      match uu____8663 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8687 =
                    let uu____8688 =
                      let uu____8689 =
                        let uu____8690 = p_tuplePattern p  in
                        let uu____8691 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8690 uu____8691  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8689
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8688  in
                  FStar_Pprint.group uu____8687
              | FStar_Pervasives_Native.Some f ->
                  let uu____8693 =
                    let uu____8694 =
                      let uu____8695 =
                        let uu____8696 =
                          let uu____8697 =
                            let uu____8698 = p_tuplePattern p  in
                            let uu____8699 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8698
                              uu____8699
                             in
                          FStar_Pprint.group uu____8697  in
                        let uu____8701 =
                          let uu____8702 =
                            let uu____8705 = p_tmFormula f  in
                            [uu____8705; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8702  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8696 uu____8701
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8695
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8694  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8693
               in
            let uu____8707 = p_term_sep false pb e  in
            match uu____8707 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8717 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8717
                   else
                     (let uu____8720 =
                        let uu____8721 =
                          let uu____8722 =
                            let uu____8723 =
                              let uu____8724 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8724  in
                            op_Hat_Slash_Plus_Hat branch uu____8723  in
                          FStar_Pprint.group uu____8722  in
                        let uu____8725 =
                          let uu____8726 =
                            let uu____8727 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8727  in
                          FStar_Pprint.op_Hat_Hat branch uu____8726  in
                        FStar_Pprint.ifflat uu____8721 uu____8725  in
                      FStar_Pprint.group uu____8720))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8731 =
                       let uu____8732 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8732  in
                     op_Hat_Slash_Plus_Hat branch uu____8731)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8743 =
                      let uu____8744 =
                        let uu____8745 =
                          let uu____8746 =
                            let uu____8747 =
                              let uu____8748 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8748  in
                            FStar_Pprint.separate_map uu____8747
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8746
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8745
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8744  in
                    FStar_Pprint.group uu____8743
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8750 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8752;_},e1::e2::[])
        ->
        let uu____8758 = str "<==>"  in
        let uu____8760 = p_tmImplies e1  in
        let uu____8761 = p_tmIff e2  in
        infix0 uu____8758 uu____8760 uu____8761
    | uu____8762 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8764;_},e1::e2::[])
        ->
        let uu____8770 = str "==>"  in
        let uu____8772 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8778 = p_tmImplies e2  in
        infix0 uu____8770 uu____8772 uu____8778
    | uu____8779 ->
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
          let uu____8793 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8793 with
          | (terms',last1) ->
              let uu____8813 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8848 =
                      let uu____8849 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8849
                       in
                    let uu____8850 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8848, uu____8850)
                | Binders (n1,ln,parens1) ->
                    let uu____8864 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8872 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8864, break1, uu____8872)
                 in
              (match uu____8813 with
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
                    | uu____8905 ->
                        let uu____8906 =
                          let uu____8907 =
                            let uu____8908 =
                              let uu____8909 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8910 =
                                let uu____8911 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8911
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8909 uu____8910
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8908  in
                          let uu____8912 =
                            let uu____8913 =
                              let uu____8914 =
                                let uu____8915 =
                                  let uu____8916 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8916  in
                                let uu____8917 =
                                  let uu____8918 =
                                    let uu____8919 =
                                      let uu____8920 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8921 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8927 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8927)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8920
                                        uu____8921
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8919
                                     in
                                  jump2 uu____8918  in
                                FStar_Pprint.ifflat uu____8915 uu____8917  in
                              FStar_Pprint.group uu____8914  in
                            let uu____8929 =
                              let uu____8930 =
                                let uu____8931 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8931  in
                              FStar_Pprint.align uu____8930  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8913 uu____8929
                             in
                          FStar_Pprint.ifflat uu____8907 uu____8912  in
                        FStar_Pprint.group uu____8906))

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
            | Arrows uu____8945 -> p_tmArrow' p_Tm e
            | Binders uu____8952 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8975 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8981 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8975 uu____8981
      | uu____8984 -> let uu____8985 = p_Tm e  in [uu____8985]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9038 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9064 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9038 uu____9064
        | uu____9087 ->
            let uu____9088 =
              let uu____9099 = p_Tm1 e1  in
              (uu____9099, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9088]
         in
      let fold_fun bs x =
        let uu____9197 = x  in
        match uu____9197 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9333 = hd1  in
                 (match uu____9333 with
                  | (b2s,t2,uu____9362) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9472 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9533 = cb  in
        match uu____9533 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9562 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9575 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9581 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9581) hd1 tl1
                         in
                      f uu____9575 typ))
         in
      let binders =
        let uu____9599 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9599  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9662 =
        let uu____9663 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9663 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9662  in
    let disj =
      let uu____9666 =
        let uu____9667 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9667 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9666  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9687;_},e1::e2::[])
        ->
        let uu____9693 = p_tmDisjunction e1  in
        let uu____9698 = let uu____9703 = p_tmConjunction e2  in [uu____9703]
           in
        FStar_List.append uu____9693 uu____9698
    | uu____9712 -> let uu____9713 = p_tmConjunction e  in [uu____9713]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9723;_},e1::e2::[])
        ->
        let uu____9729 = p_tmConjunction e1  in
        let uu____9732 = let uu____9735 = p_tmTuple e2  in [uu____9735]  in
        FStar_List.append uu____9729 uu____9732
    | uu____9736 -> let uu____9737 = p_tmTuple e  in [uu____9737]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range "!5"

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9756 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9756
          (fun uu____9764  ->
             match uu____9764 with | (e1,uu____9770) -> p_tmEq e1) args
    | uu____9771 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9780 =
             let uu____9781 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9781  in
           FStar_Pprint.group uu____9780)

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
               (let uu____9800 = FStar_Ident.text_of_id op  in
                uu____9800 = "="))
              ||
              (let uu____9805 = FStar_Ident.text_of_id op  in
               uu____9805 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9811 = levels op1  in
            (match uu____9811 with
             | (left1,mine,right1) ->
                 let uu____9830 =
                   let uu____9831 = FStar_All.pipe_left str op1  in
                   let uu____9833 = p_tmEqWith' p_X left1 e1  in
                   let uu____9834 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9831 uu____9833 uu____9834  in
                 paren_if_gt curr mine uu____9830)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9835;_},e1::e2::[])
            ->
            let uu____9841 =
              let uu____9842 = p_tmEqWith p_X e1  in
              let uu____9843 =
                let uu____9844 =
                  let uu____9845 =
                    let uu____9846 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9846  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9845  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9844  in
              FStar_Pprint.op_Hat_Hat uu____9842 uu____9843  in
            FStar_Pprint.group uu____9841
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9847;_},e1::[])
            ->
            let uu____9852 = levels "-"  in
            (match uu____9852 with
             | (left1,mine,right1) ->
                 let uu____9872 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9872)
        | uu____9873 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9921)::(e2,uu____9923)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9943 = is_list e  in Prims.op_Negation uu____9943)
              ->
              let op = "::"  in
              let uu____9948 = levels op  in
              (match uu____9948 with
               | (left1,mine,right1) ->
                   let uu____9967 =
                     let uu____9968 = str op  in
                     let uu____9969 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9971 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9968 uu____9969 uu____9971  in
                   paren_if_gt curr mine uu____9967)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9990 = levels op  in
              (match uu____9990 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10024 = p_binder false b  in
                         let uu____10026 =
                           let uu____10027 =
                             let uu____10028 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10028 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10027
                            in
                         FStar_Pprint.op_Hat_Hat uu____10024 uu____10026
                     | FStar_Util.Inr t ->
                         let uu____10030 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10032 =
                           let uu____10033 =
                             let uu____10034 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10034 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10033
                            in
                         FStar_Pprint.op_Hat_Hat uu____10030 uu____10032
                      in
                   let uu____10035 =
                     let uu____10036 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10041 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10036 uu____10041  in
                   paren_if_gt curr mine uu____10035)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10043;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10073 = levels op  in
              (match uu____10073 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10093 = str op  in
                     let uu____10094 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10096 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10093 uu____10094 uu____10096
                   else
                     (let uu____10100 =
                        let uu____10101 = str op  in
                        let uu____10102 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10104 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10101 uu____10102 uu____10104  in
                      paren_if_gt curr mine uu____10100))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10113 = levels op1  in
              (match uu____10113 with
               | (left1,mine,right1) ->
                   let uu____10132 =
                     let uu____10133 = str op1  in
                     let uu____10134 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10136 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10133 uu____10134 uu____10136  in
                   paren_if_gt curr mine uu____10132)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10156 =
                let uu____10157 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10158 =
                  let uu____10159 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10159 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10157 uu____10158  in
              braces_with_nesting uu____10156
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10164;_},e1::[])
              ->
              let uu____10169 =
                let uu____10170 = str "~"  in
                let uu____10172 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10170 uu____10172  in
              FStar_Pprint.group uu____10169
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10174;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10183 = levels op  in
                   (match uu____10183 with
                    | (left1,mine,right1) ->
                        let uu____10202 =
                          let uu____10203 = str op  in
                          let uu____10204 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10206 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10203 uu____10204 uu____10206  in
                        paren_if_gt curr mine uu____10202)
               | uu____10208 -> p_X e)
          | uu____10209 -> p_X e

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
        let uu____10216 =
          let uu____10217 = p_lident lid  in
          let uu____10218 =
            let uu____10219 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10219  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10217 uu____10218  in
        FStar_Pprint.group uu____10216
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10222 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10224 = p_appTerm e  in
    let uu____10225 =
      let uu____10226 =
        let uu____10227 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10227 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10226  in
    FStar_Pprint.op_Hat_Hat uu____10224 uu____10225

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10233 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10233 t phi
      | FStar_Parser_AST.TAnnotated uu____10234 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10240 ->
          let uu____10241 =
            let uu____10243 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10243
             in
          failwith uu____10241
      | FStar_Parser_AST.TVariable uu____10246 ->
          let uu____10247 =
            let uu____10249 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10249
             in
          failwith uu____10247
      | FStar_Parser_AST.NoName uu____10252 ->
          let uu____10253 =
            let uu____10255 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10255
             in
          failwith uu____10253

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10259  ->
      match uu____10259 with
      | (lid,e) ->
          let uu____10267 =
            let uu____10268 = p_qlident lid  in
            let uu____10269 =
              let uu____10270 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10270
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10268 uu____10269  in
          FStar_Pprint.group uu____10267

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10273 when is_general_application e ->
        let uu____10280 = head_and_args e  in
        (match uu____10280 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10327 = p_argTerm e1  in
                  let uu____10328 =
                    let uu____10329 =
                      let uu____10330 =
                        let uu____10331 = str "`"  in
                        let uu____10333 =
                          let uu____10334 = p_indexingTerm head1  in
                          let uu____10335 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10334 uu____10335  in
                        FStar_Pprint.op_Hat_Hat uu____10331 uu____10333  in
                      FStar_Pprint.group uu____10330  in
                    let uu____10337 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10329 uu____10337  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10327 uu____10328
              | uu____10338 ->
                  let uu____10345 =
                    let uu____10356 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10356
                    then
                      let uu____10390 =
                        FStar_Util.take
                          (fun uu____10414  ->
                             match uu____10414 with
                             | (uu____10420,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10390 with
                      | (fs_typ_args,args1) ->
                          let uu____10458 =
                            let uu____10459 = p_indexingTerm head1  in
                            let uu____10460 =
                              let uu____10461 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10461
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10459 uu____10460
                             in
                          (uu____10458, args1)
                    else
                      (let uu____10476 = p_indexingTerm head1  in
                       (uu____10476, args))
                     in
                  (match uu____10345 with
                   | (head_doc,args1) ->
                       let uu____10497 =
                         let uu____10498 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10498 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10497)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10520 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10520)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10539 =
               let uu____10540 = p_quident lid  in
               let uu____10541 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10540 uu____10541  in
             FStar_Pprint.group uu____10539
         | hd1::tl1 ->
             let uu____10558 =
               let uu____10559 =
                 let uu____10560 =
                   let uu____10561 = p_quident lid  in
                   let uu____10562 = p_argTerm hd1  in
                   prefix2 uu____10561 uu____10562  in
                 FStar_Pprint.group uu____10560  in
               let uu____10563 =
                 let uu____10564 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10564  in
               FStar_Pprint.op_Hat_Hat uu____10559 uu____10563  in
             FStar_Pprint.group uu____10558)
    | uu____10569 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10580 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10580 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10584 = str "#"  in
        let uu____10586 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10584 uu____10586
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10589 = str "#["  in
        let uu____10591 =
          let uu____10592 = p_indexingTerm t  in
          let uu____10593 =
            let uu____10594 = str "]"  in
            let uu____10596 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10594 uu____10596  in
          FStar_Pprint.op_Hat_Hat uu____10592 uu____10593  in
        FStar_Pprint.op_Hat_Hat uu____10589 uu____10591
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____10599  ->
    match uu____10599 with | (e,uu____10605) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10610;_},e1::e2::[])
          ->
          let uu____10616 =
            let uu____10617 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10618 =
              let uu____10619 =
                let uu____10620 = p_term false false e2  in
                soft_parens_with_nesting uu____10620  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10619  in
            FStar_Pprint.op_Hat_Hat uu____10617 uu____10618  in
          FStar_Pprint.group uu____10616
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10623;_},e1::e2::[])
          ->
          let uu____10629 =
            let uu____10630 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10631 =
              let uu____10632 =
                let uu____10633 = p_term false false e2  in
                soft_brackets_with_nesting uu____10633  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10632  in
            FStar_Pprint.op_Hat_Hat uu____10630 uu____10631  in
          FStar_Pprint.group uu____10629
      | uu____10636 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10641 = p_quident lid  in
        let uu____10642 =
          let uu____10643 =
            let uu____10644 = p_term false false e1  in
            soft_parens_with_nesting uu____10644  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10643  in
        FStar_Pprint.op_Hat_Hat uu____10641 uu____10642
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10652 =
          let uu____10653 = FStar_Ident.text_of_id op  in str uu____10653  in
        let uu____10655 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10652 uu____10655
    | uu____10656 -> p_atomicTermNotQUident e

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
         | uu____10669 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10678 =
          let uu____10679 = FStar_Ident.text_of_id op  in str uu____10679  in
        let uu____10681 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10678 uu____10681
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10685 =
          let uu____10686 =
            let uu____10687 =
              let uu____10688 = FStar_Ident.text_of_id op  in str uu____10688
               in
            let uu____10690 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10687 uu____10690  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10686  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10685
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10705 = all_explicit args  in
        if uu____10705
        then
          let uu____10708 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10709 =
            let uu____10710 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10711 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10710 p_tmEq uu____10711  in
          let uu____10718 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10708 uu____10709 uu____10718
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10740 =
                 let uu____10741 = p_quident lid  in
                 let uu____10742 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10741 uu____10742  in
               FStar_Pprint.group uu____10740
           | hd1::tl1 ->
               let uu____10759 =
                 let uu____10760 =
                   let uu____10761 =
                     let uu____10762 = p_quident lid  in
                     let uu____10763 = p_argTerm hd1  in
                     prefix2 uu____10762 uu____10763  in
                   FStar_Pprint.group uu____10761  in
                 let uu____10764 =
                   let uu____10765 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10765  in
                 FStar_Pprint.op_Hat_Hat uu____10760 uu____10764  in
               FStar_Pprint.group uu____10759)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10772 =
          let uu____10773 = p_atomicTermNotQUident e1  in
          let uu____10774 =
            let uu____10775 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10775  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10773 uu____10774
           in
        FStar_Pprint.group uu____10772
    | uu____10778 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10783 = p_quident constr_lid  in
        let uu____10784 =
          let uu____10785 =
            let uu____10786 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10786  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10785  in
        FStar_Pprint.op_Hat_Hat uu____10783 uu____10784
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10788 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10788 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10790 = p_term_sep false false e1  in
        (match uu____10790 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10803 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10803))
    | uu____10804 when is_array e ->
        let es = extract_from_list e  in
        let uu____10808 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10809 =
          let uu____10810 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10810
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10815 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10808 uu____10809 uu____10815
    | uu____10818 when is_list e ->
        let uu____10819 =
          let uu____10820 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10821 = extract_from_list e  in
          separate_map_or_flow_last uu____10820
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10821
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10819 FStar_Pprint.rbracket
    | uu____10830 when is_lex_list e ->
        let uu____10831 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10832 =
          let uu____10833 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10834 = extract_from_list e  in
          separate_map_or_flow_last uu____10833
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10834
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10831 uu____10832 FStar_Pprint.rbracket
    | uu____10843 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10847 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10848 =
          let uu____10849 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10849 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10847 uu____10848 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10859 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____10862 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10859 uu____10862
    | FStar_Parser_AST.Op (op,args) when
        let uu____10871 = handleable_op op args  in
        Prims.op_Negation uu____10871 ->
        let uu____10873 =
          let uu____10875 =
            let uu____10877 = FStar_Ident.text_of_id op  in
            let uu____10879 =
              let uu____10881 =
                let uu____10883 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____10883
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____10881  in
            Prims.strcat uu____10877 uu____10879  in
          Prims.strcat "Operation " uu____10875  in
        failwith uu____10873
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10889 = str "u#"  in
        let uu____10891 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____10889 uu____10891
    | FStar_Parser_AST.Wild  ->
        let uu____10892 = p_term false false e  in
        soft_parens_with_nesting uu____10892
    | FStar_Parser_AST.Const uu____10895 ->
        let uu____10896 = p_term false false e  in
        soft_parens_with_nesting uu____10896
    | FStar_Parser_AST.Op uu____10899 ->
        let uu____10906 = p_term false false e  in
        soft_parens_with_nesting uu____10906
    | FStar_Parser_AST.Tvar uu____10909 ->
        let uu____10910 = p_term false false e  in
        soft_parens_with_nesting uu____10910
    | FStar_Parser_AST.Var uu____10913 ->
        let uu____10914 = p_term false false e  in
        soft_parens_with_nesting uu____10914
    | FStar_Parser_AST.Name uu____10917 ->
        let uu____10918 = p_term false false e  in
        soft_parens_with_nesting uu____10918
    | FStar_Parser_AST.Construct uu____10921 ->
        let uu____10932 = p_term false false e  in
        soft_parens_with_nesting uu____10932
    | FStar_Parser_AST.Abs uu____10935 ->
        let uu____10942 = p_term false false e  in
        soft_parens_with_nesting uu____10942
    | FStar_Parser_AST.App uu____10945 ->
        let uu____10952 = p_term false false e  in
        soft_parens_with_nesting uu____10952
    | FStar_Parser_AST.Let uu____10955 ->
        let uu____10976 = p_term false false e  in
        soft_parens_with_nesting uu____10976
    | FStar_Parser_AST.LetOpen uu____10979 ->
        let uu____10984 = p_term false false e  in
        soft_parens_with_nesting uu____10984
    | FStar_Parser_AST.Seq uu____10987 ->
        let uu____10992 = p_term false false e  in
        soft_parens_with_nesting uu____10992
    | FStar_Parser_AST.Bind uu____10995 ->
        let uu____11002 = p_term false false e  in
        soft_parens_with_nesting uu____11002
    | FStar_Parser_AST.If uu____11005 ->
        let uu____11012 = p_term false false e  in
        soft_parens_with_nesting uu____11012
    | FStar_Parser_AST.Match uu____11015 ->
        let uu____11030 = p_term false false e  in
        soft_parens_with_nesting uu____11030
    | FStar_Parser_AST.TryWith uu____11033 ->
        let uu____11048 = p_term false false e  in
        soft_parens_with_nesting uu____11048
    | FStar_Parser_AST.Ascribed uu____11051 ->
        let uu____11060 = p_term false false e  in
        soft_parens_with_nesting uu____11060
    | FStar_Parser_AST.Record uu____11063 ->
        let uu____11076 = p_term false false e  in
        soft_parens_with_nesting uu____11076
    | FStar_Parser_AST.Project uu____11079 ->
        let uu____11084 = p_term false false e  in
        soft_parens_with_nesting uu____11084
    | FStar_Parser_AST.Product uu____11087 ->
        let uu____11094 = p_term false false e  in
        soft_parens_with_nesting uu____11094
    | FStar_Parser_AST.Sum uu____11097 ->
        let uu____11108 = p_term false false e  in
        soft_parens_with_nesting uu____11108
    | FStar_Parser_AST.QForall uu____11111 ->
        let uu____11124 = p_term false false e  in
        soft_parens_with_nesting uu____11124
    | FStar_Parser_AST.QExists uu____11127 ->
        let uu____11140 = p_term false false e  in
        soft_parens_with_nesting uu____11140
    | FStar_Parser_AST.Refine uu____11143 ->
        let uu____11148 = p_term false false e  in
        soft_parens_with_nesting uu____11148
    | FStar_Parser_AST.NamedTyp uu____11151 ->
        let uu____11156 = p_term false false e  in
        soft_parens_with_nesting uu____11156
    | FStar_Parser_AST.Requires uu____11159 ->
        let uu____11167 = p_term false false e  in
        soft_parens_with_nesting uu____11167
    | FStar_Parser_AST.Ensures uu____11170 ->
        let uu____11178 = p_term false false e  in
        soft_parens_with_nesting uu____11178
    | FStar_Parser_AST.Attributes uu____11181 ->
        let uu____11184 = p_term false false e  in
        soft_parens_with_nesting uu____11184
    | FStar_Parser_AST.Quote uu____11187 ->
        let uu____11192 = p_term false false e  in
        soft_parens_with_nesting uu____11192
    | FStar_Parser_AST.VQuote uu____11195 ->
        let uu____11196 = p_term false false e  in
        soft_parens_with_nesting uu____11196
    | FStar_Parser_AST.Antiquote uu____11199 ->
        let uu____11200 = p_term false false e  in
        soft_parens_with_nesting uu____11200

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_11203  ->
    match uu___125_11203 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11212) ->
        let uu____11215 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11215
    | FStar_Const.Const_bytearray (bytes,uu____11217) ->
        let uu____11222 =
          let uu____11223 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11223  in
        let uu____11224 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11222 uu____11224
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_11247 =
          match uu___123_11247 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_11254 =
          match uu___124_11254 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11269  ->
               match uu____11269 with
               | (s,w) ->
                   let uu____11276 = signedness s  in
                   let uu____11277 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11276 uu____11277)
            sign_width_opt
           in
        let uu____11278 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11278 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11282 = FStar_Range.string_of_range r  in str uu____11282
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11286 = p_quident lid  in
        let uu____11287 =
          let uu____11288 =
            let uu____11289 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11289  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11288  in
        FStar_Pprint.op_Hat_Hat uu____11286 uu____11287

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11292 = str "u#"  in
    let uu____11294 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11292 uu____11294

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11296;_},u1::u2::[])
        ->
        let uu____11302 =
          let uu____11303 = p_universeFrom u1  in
          let uu____11304 =
            let uu____11305 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11305  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11303 uu____11304  in
        FStar_Pprint.group uu____11302
    | FStar_Parser_AST.App uu____11306 ->
        let uu____11313 = head_and_args u  in
        (match uu____11313 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11339 =
                    let uu____11340 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11341 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11349  ->
                           match uu____11349 with
                           | (u1,uu____11355) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11340 uu____11341  in
                  FStar_Pprint.group uu____11339
              | uu____11356 ->
                  let uu____11357 =
                    let uu____11359 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11359
                     in
                  failwith uu____11357))
    | uu____11362 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11388 = FStar_Ident.text_of_id id1  in str uu____11388
    | FStar_Parser_AST.Paren u1 ->
        let uu____11391 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11391
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11392;_},uu____11393::uu____11394::[])
        ->
        let uu____11398 = p_universeFrom u  in
        soft_parens_with_nesting uu____11398
    | FStar_Parser_AST.App uu____11399 ->
        let uu____11406 = p_universeFrom u  in
        soft_parens_with_nesting uu____11406
    | uu____11407 ->
        let uu____11408 =
          let uu____11410 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11410
           in
        failwith uu____11408

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
       | FStar_Parser_AST.Module (uu____11499,decls) ->
           let uu____11505 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11505
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11514,decls,uu____11516) ->
           let uu____11523 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11523
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11583  ->
         match uu____11583 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11605)) -> false
      | ([],uu____11609) -> false
      | uu____11613 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11623 -> true
         | uu____11625 -> false)
    }
  
let (modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____11668,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11674,decls,uu____11676) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11728 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11741;
                 FStar_Parser_AST.doc = uu____11742;
                 FStar_Parser_AST.quals = uu____11743;
                 FStar_Parser_AST.attrs = uu____11744;_}::uu____11745 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11751 =
                   let uu____11754 =
                     let uu____11757 = FStar_List.tl ds  in d :: uu____11757
                      in
                   d0 :: uu____11754  in
                 (uu____11751, (d0.FStar_Parser_AST.drange))
             | uu____11762 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11728 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11819 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11819 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11928 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11928, comments1))))))
  