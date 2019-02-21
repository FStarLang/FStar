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
      (fun uu___17_258  ->
         match uu___17_258 with
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
  fun uu___18_1701  ->
    match uu___18_1701 with
    | FStar_Util.Inl c ->
        FStar_String.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___19_1736  ->
      match uu___19_1736 with
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
  let levels_from_associativity l uu___20_1993 =
    match uu___20_1993 with
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
      | uu____2208 ->
          let uu____2226 = FStar_String.op_Hat "Unrecognized operator " s  in
          failwith uu____2226
  
let max_level :
  'Auu____2243 . ('Auu____2243 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2292 =
        FStar_List.tryFind
          (fun uu____2328  ->
             match uu____2328 with
             | (uu____2345,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2292 with
      | FStar_Pervasives_Native.Some ((uu____2374,l1,uu____2376),uu____2377)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2427 =
            let uu____2429 =
              let uu____2431 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2431  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2429
             in
          failwith uu____2427
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2466 = assign_levels level_associativity_spec op  in
    match uu____2466 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2525 =
      let uu____2528 =
        let uu____2534 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2534  in
      FStar_List.tryFind uu____2528 operatorInfix0ad12  in
    uu____2525 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2601 =
      let uu____2616 =
        let uu____2634 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2634  in
      FStar_List.tryFind uu____2616 opinfix34  in
    uu____2601 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2700 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2700
    then (Prims.parse_int "1")
    else
      (let uu____2713 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2713
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2759 . FStar_Ident.ident -> 'Auu____2759 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2777 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2777 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2786 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2786
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2808 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2808 [".()<-"; ".[]<-"]
      | uu____2816 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____2862 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____2915 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____2958 -> true
      | uu____2964 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____2997 = FStar_List.for_all is_binder_annot bs  in
          if uu____2997
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____3012 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____3017 = all_binders e (Prims.parse_int "0")  in
    match uu____3017 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3056 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3056
  
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
  'Auu____3216 .
    ('Auu____3216 -> FStar_Pprint.document) ->
      'Auu____3216 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3258 = FStar_ST.op_Bang comment_stack  in
          match uu____3258 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3329 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3329 FStar_Pprint.hardline  in
              let uu____3330 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3330
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3372 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3372 print_pos lookahead_pos))
              else
                (let uu____3375 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3375))
           in
        let uu____3378 =
          let uu____3384 =
            let uu____3385 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3385  in
          let uu____3386 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3384 uu____3386  in
        match uu____3378 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3395 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3395
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3407 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3407)
  
let with_comment_sep :
  'Auu____3419 'Auu____3420 .
    ('Auu____3419 -> 'Auu____3420) ->
      'Auu____3419 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3420)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3466 = FStar_ST.op_Bang comment_stack  in
          match uu____3466 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____3537 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3537
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3579 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____3583 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____3583)
                     in
                  comments_before_pos uu____3579 print_pos lookahead_pos))
              else
                (let uu____3586 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3586))
           in
        let uu____3589 =
          let uu____3595 =
            let uu____3596 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3596  in
          let uu____3597 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3595 uu____3597  in
        match uu____3589 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3610 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3610
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
                let uu____3663 = FStar_ST.op_Bang comment_stack  in
                match uu____3663 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____3757 =
                          let uu____3759 =
                            let uu____3761 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____3761  in
                          uu____3759 - lbegin  in
                        max k uu____3757  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____3766 =
                          let uu____3767 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____3768 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____3767 uu____3768  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____3766  in
                      let uu____3769 =
                        let uu____3771 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____3771  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____3769 pos meta_decl doc2 true init1))
                | uu____3774 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____3787 = FStar_Range.line_of_pos pos  in
                         uu____3787 - lbegin  in
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
                       let uu____3829 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____3829)
  
let separate_map_with_comments :
  'Auu____3843 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3843 -> FStar_Pprint.document) ->
          'Auu____3843 Prims.list ->
            ('Auu____3843 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____3902 x =
              match uu____3902 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____3921 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3921 meta_decl doc1 false false
                     in
                  let uu____3925 =
                    let uu____3927 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3927  in
                  let uu____3928 =
                    let uu____3929 =
                      let uu____3930 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3930  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3929  in
                  (uu____3925, uu____3928)
               in
            let uu____3932 =
              let uu____3939 = FStar_List.hd xs  in
              let uu____3940 = FStar_List.tl xs  in (uu____3939, uu____3940)
               in
            match uu____3932 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____3958 =
                    let uu____3960 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____3960  in
                  let uu____3961 =
                    let uu____3962 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3962  in
                  (uu____3958, uu____3961)  in
                let uu____3964 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3964
  
let separate_map_with_comments_kw :
  'Auu____3991 'Auu____3992 .
    'Auu____3991 ->
      'Auu____3991 ->
        ('Auu____3991 -> 'Auu____3992 -> FStar_Pprint.document) ->
          'Auu____3992 Prims.list ->
            ('Auu____3992 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4056 x =
              match uu____4056 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4075 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4075 meta_decl doc1 false false
                     in
                  let uu____4079 =
                    let uu____4081 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4081  in
                  let uu____4082 =
                    let uu____4083 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4083  in
                  (uu____4079, uu____4082)
               in
            let uu____4085 =
              let uu____4092 = FStar_List.hd xs  in
              let uu____4093 = FStar_List.tl xs  in (uu____4092, uu____4093)
               in
            match uu____4085 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4111 =
                    let uu____4113 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4113  in
                  let uu____4114 = f prefix1 x  in (uu____4111, uu____4114)
                   in
                let uu____4116 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4116
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____5102)) ->
          let uu____5105 =
            let uu____5107 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5107 FStar_Util.is_upper  in
          if uu____5105
          then
            let uu____5113 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5113 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5116 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5123 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5126 =
      let uu____5127 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5128 =
        let uu____5129 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5129  in
      FStar_Pprint.op_Hat_Hat uu____5127 uu____5128  in
    FStar_Pprint.op_Hat_Hat uu____5123 uu____5126

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5131 ->
        let uu____5132 =
          let uu____5133 = str "@ "  in
          let uu____5135 =
            let uu____5136 =
              let uu____5137 =
                let uu____5138 =
                  let uu____5139 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5139  in
                FStar_Pprint.op_Hat_Hat uu____5138 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5137  in
            FStar_Pprint.op_Hat_Hat uu____5136 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5133 uu____5135  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5132

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5142  ->
    match uu____5142 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5190 =
                match uu____5190 with
                | (kwd,arg) ->
                    let uu____5203 = str "@"  in
                    let uu____5205 =
                      let uu____5206 = str kwd  in
                      let uu____5207 =
                        let uu____5208 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5208
                         in
                      FStar_Pprint.op_Hat_Hat uu____5206 uu____5207  in
                    FStar_Pprint.op_Hat_Hat uu____5203 uu____5205
                 in
              let uu____5209 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5209 FStar_Pprint.hardline
           in
        let uu____5216 =
          let uu____5217 =
            let uu____5218 =
              let uu____5219 = str doc1  in
              let uu____5220 =
                let uu____5221 =
                  let uu____5222 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5222  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5221  in
              FStar_Pprint.op_Hat_Hat uu____5219 uu____5220  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5218  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5217  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5216

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5226 =
          let uu____5227 = str "val"  in
          let uu____5229 =
            let uu____5230 =
              let uu____5231 = p_lident lid  in
              let uu____5232 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5231 uu____5232  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5230  in
          FStar_Pprint.op_Hat_Hat uu____5227 uu____5229  in
        let uu____5233 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5226 uu____5233
    | FStar_Parser_AST.TopLevelLet (uu____5236,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5261 =
               let uu____5262 = str "let"  in p_letlhs uu____5262 lb false
                in
             FStar_Pprint.group uu____5261) lbs
    | uu____5265 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___21_5280 =
          match uu___21_5280 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5288 = f x  in
              let uu____5289 =
                let uu____5290 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5290  in
              FStar_Pprint.op_Hat_Hat uu____5288 uu____5289
           in
        let uu____5291 = str "["  in
        let uu____5293 =
          let uu____5294 = p_list' l  in
          let uu____5295 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5294 uu____5295  in
        FStar_Pprint.op_Hat_Hat uu____5291 uu____5293

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5299 =
          let uu____5300 = str "open"  in
          let uu____5302 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5300 uu____5302  in
        FStar_Pprint.group uu____5299
    | FStar_Parser_AST.Include uid ->
        let uu____5304 =
          let uu____5305 = str "include"  in
          let uu____5307 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5305 uu____5307  in
        FStar_Pprint.group uu____5304
    | FStar_Parser_AST.Friend uid ->
        let uu____5309 =
          let uu____5310 = str "friend"  in
          let uu____5312 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5310 uu____5312  in
        FStar_Pprint.group uu____5309
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5315 =
          let uu____5316 = str "module"  in
          let uu____5318 =
            let uu____5319 =
              let uu____5320 = p_uident uid1  in
              let uu____5321 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5320 uu____5321  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5319  in
          FStar_Pprint.op_Hat_Hat uu____5316 uu____5318  in
        let uu____5322 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5315 uu____5322
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5324 =
          let uu____5325 = str "module"  in
          let uu____5327 =
            let uu____5328 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5328  in
          FStar_Pprint.op_Hat_Hat uu____5325 uu____5327  in
        FStar_Pprint.group uu____5324
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5329,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5366 = str "effect"  in
          let uu____5368 =
            let uu____5369 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5369  in
          FStar_Pprint.op_Hat_Hat uu____5366 uu____5368  in
        let uu____5370 =
          let uu____5371 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5371 FStar_Pprint.equals
           in
        let uu____5374 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5370 uu____5374
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5405 =
          let uu____5406 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5406  in
        let uu____5419 =
          let uu____5420 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5458 =
                    let uu____5459 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5459 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5458)) uu____5420
           in
        FStar_Pprint.op_Hat_Hat uu____5405 uu____5419
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5476 = str "let"  in
          let uu____5478 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5476 uu____5478  in
        let uu____5479 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5479 p_letbinding lbs
          (fun uu____5489  ->
             match uu____5489 with
             | (p,t) ->
                 let uu____5496 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5496;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5502 =
          let uu____5503 = str "val"  in
          let uu____5505 =
            let uu____5506 =
              let uu____5507 = p_lident lid  in
              let uu____5508 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5507 uu____5508  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5506  in
          FStar_Pprint.op_Hat_Hat uu____5503 uu____5505  in
        FStar_All.pipe_left FStar_Pprint.group uu____5502
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5513 =
            let uu____5515 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5515 FStar_Util.is_upper  in
          if uu____5513
          then FStar_Pprint.empty
          else
            (let uu____5523 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5523 FStar_Pprint.space)
           in
        let uu____5525 =
          let uu____5526 = p_ident id1  in
          let uu____5527 =
            let uu____5528 =
              let uu____5529 =
                let uu____5530 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5530  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5529  in
            FStar_Pprint.group uu____5528  in
          FStar_Pprint.op_Hat_Hat uu____5526 uu____5527  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5525
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5539 = str "exception"  in
        let uu____5541 =
          let uu____5542 =
            let uu____5543 = p_uident uid  in
            let uu____5544 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5548 =
                     let uu____5549 = str "of"  in
                     let uu____5551 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5549 uu____5551  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5548) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5543 uu____5544  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5542  in
        FStar_Pprint.op_Hat_Hat uu____5539 uu____5541
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5555 = str "new_effect"  in
        let uu____5557 =
          let uu____5558 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5558  in
        FStar_Pprint.op_Hat_Hat uu____5555 uu____5557
    | FStar_Parser_AST.SubEffect se ->
        let uu____5560 = str "sub_effect"  in
        let uu____5562 =
          let uu____5563 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5563  in
        FStar_Pprint.op_Hat_Hat uu____5560 uu____5562
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5566 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5568,uu____5569) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5597 = str "%splice"  in
        let uu____5599 =
          let uu____5600 =
            let uu____5601 = str ";"  in p_list p_uident uu____5601 ids  in
          let uu____5603 =
            let uu____5604 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5604  in
          FStar_Pprint.op_Hat_Hat uu____5600 uu____5603  in
        FStar_Pprint.op_Hat_Hat uu____5597 uu____5599

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___22_5607  ->
    match uu___22_5607 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5610 = str "#set-options"  in
        let uu____5612 =
          let uu____5613 =
            let uu____5614 = str s  in FStar_Pprint.dquotes uu____5614  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5613  in
        FStar_Pprint.op_Hat_Hat uu____5610 uu____5612
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5619 = str "#reset-options"  in
        let uu____5621 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5627 =
                 let uu____5628 = str s  in FStar_Pprint.dquotes uu____5628
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5627) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5619 uu____5621
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5633 = str "#push-options"  in
        let uu____5635 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5641 =
                 let uu____5642 = str s  in FStar_Pprint.dquotes uu____5642
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5641) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5633 uu____5635
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
    fun uu____5673  ->
      match uu____5673 with
      | (typedecl,fsdoc_opt) ->
          let uu____5686 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5686 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5711 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5711
               else
                 (let uu____5714 =
                    let uu____5715 =
                      let uu____5716 =
                        let uu____5717 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5717 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5716  in
                    let uu____5718 =
                      let uu____5719 =
                        let uu____5720 =
                          let uu____5721 =
                            let uu____5722 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5722  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5721
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5720
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5719  in
                    FStar_Pprint.ifflat uu____5715 uu____5718  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5714))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___23_5725  ->
      match uu___23_5725 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5754 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5754, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5771 = p_typ_sep false false t  in
          (match uu____5771 with
           | (comm,doc1) ->
               let uu____5791 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5791, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5847 =
            match uu____5847 with
            | (lid1,t,doc_opt) ->
                let uu____5864 =
                  let uu____5869 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5869
                   in
                (match uu____5864 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5887 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5887  in
          let uu____5896 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5896, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5963 =
            match uu____5963 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5992 =
                    let uu____5993 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5993  in
                  FStar_Range.extend_to_end_of_line uu____5992  in
                let uu____5998 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5998 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6037 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6037, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6042  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6042 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6077 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6077  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6079 =
                        let uu____6082 =
                          let uu____6085 = p_fsdoc fsdoc  in
                          let uu____6086 =
                            let uu____6089 = cont lid_doc  in [uu____6089]
                             in
                          uu____6085 :: uu____6086  in
                        kw :: uu____6082  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6079
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6096 =
                        let uu____6097 =
                          let uu____6098 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6098 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6097
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6096
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6118 =
                          let uu____6119 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6119  in
                        prefix2 uu____6118 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6121  ->
      match uu____6121 with
      | (lid,t,doc_opt) ->
          let uu____6138 =
            let uu____6139 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6140 =
              let uu____6141 = p_lident lid  in
              let uu____6142 =
                let uu____6143 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6143  in
              FStar_Pprint.op_Hat_Hat uu____6141 uu____6142  in
            FStar_Pprint.op_Hat_Hat uu____6139 uu____6140  in
          FStar_Pprint.group uu____6138

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6145  ->
    match uu____6145 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6179 =
            let uu____6180 =
              let uu____6181 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6181  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6180  in
          FStar_Pprint.group uu____6179  in
        let uu____6182 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6183 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6187 =
                 let uu____6188 =
                   let uu____6189 =
                     let uu____6190 =
                       let uu____6191 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6191
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6190  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6189  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6188  in
               FStar_Pprint.group uu____6187) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6182 uu____6183

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6195  ->
      fun inner_let  ->
        match uu____6195 with
        | (pat,uu____6203) ->
            let uu____6204 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6256 =
                    let uu____6263 =
                      let uu____6268 =
                        let uu____6269 =
                          let uu____6270 =
                            let uu____6271 = str "by"  in
                            let uu____6273 =
                              let uu____6274 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6274
                               in
                            FStar_Pprint.op_Hat_Hat uu____6271 uu____6273  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6270
                           in
                        FStar_Pprint.group uu____6269  in
                      (t, uu____6268)  in
                    FStar_Pervasives_Native.Some uu____6263  in
                  (pat1, uu____6256)
              | uu____6285 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6204 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6311);
                         FStar_Parser_AST.prange = uu____6312;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6329 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6329 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6335 =
                        if inner_let
                        then
                          let uu____6349 = pats_as_binders_if_possible pats
                             in
                          match uu____6349 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6372 = pats_as_binders_if_possible pats
                              in
                           match uu____6372 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6335 with
                       | (terms,style) ->
                           let uu____6399 =
                             let uu____6400 =
                               let uu____6401 =
                                 let uu____6402 = p_lident lid  in
                                 let uu____6403 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6402
                                   uu____6403
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6401
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6400  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6399)
                  | uu____6406 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6414 =
                              let uu____6415 =
                                let uu____6416 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6416
                                 in
                              FStar_Pprint.group uu____6415  in
                            FStar_Pprint.op_Hat_Hat uu____6414 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6427 =
                        let uu____6428 =
                          let uu____6429 =
                            let uu____6430 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6430  in
                          FStar_Pprint.group uu____6429  in
                        FStar_Pprint.op_Hat_Hat uu____6428 ascr_doc  in
                      FStar_Pprint.group uu____6427))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6432  ->
      match uu____6432 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6441 = p_term_sep false false e  in
          (match uu____6441 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6451 =
                 let uu____6452 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6452  in
               let uu____6453 =
                 let uu____6454 =
                   let uu____6455 =
                     let uu____6456 =
                       let uu____6457 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6457
                        in
                     FStar_Pprint.group uu____6456  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6455  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6454  in
               FStar_Pprint.ifflat uu____6451 uu____6453)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___24_6458  ->
    match uu___24_6458 with
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
        let uu____6483 = p_uident uid  in
        let uu____6484 = p_binders true bs  in
        let uu____6486 =
          let uu____6487 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6487  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6483 uu____6484 uu____6486

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
          let uu____6502 =
            let uu____6503 =
              let uu____6504 =
                let uu____6505 = p_uident uid  in
                let uu____6506 = p_binders true bs  in
                let uu____6508 =
                  let uu____6509 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6509  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6505 uu____6506 uu____6508
                 in
              FStar_Pprint.group uu____6504  in
            let uu____6514 =
              let uu____6515 = str "with"  in
              let uu____6517 =
                let uu____6518 =
                  let uu____6519 =
                    let uu____6520 =
                      let uu____6521 =
                        let uu____6522 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6522
                         in
                      separate_map_last uu____6521 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6520  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6519  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6518  in
              FStar_Pprint.op_Hat_Hat uu____6515 uu____6517  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6503 uu____6514  in
          braces_with_nesting uu____6502

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6526,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6559 =
            let uu____6560 = p_lident lid  in
            let uu____6561 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6560 uu____6561  in
          let uu____6562 = p_simpleTerm ps false e  in
          prefix2 uu____6559 uu____6562
      | uu____6564 ->
          let uu____6565 =
            let uu____6567 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6567
             in
          failwith uu____6565

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6650 =
        match uu____6650 with
        | (kwd,t) ->
            let uu____6661 =
              let uu____6662 = str kwd  in
              let uu____6663 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6662 uu____6663  in
            let uu____6664 = p_simpleTerm ps false t  in
            prefix2 uu____6661 uu____6664
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6671 =
      let uu____6672 =
        let uu____6673 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6674 =
          let uu____6675 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6675  in
        FStar_Pprint.op_Hat_Hat uu____6673 uu____6674  in
      let uu____6677 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6672 uu____6677  in
    let uu____6678 =
      let uu____6679 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6679  in
    FStar_Pprint.op_Hat_Hat uu____6671 uu____6678

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___25_6680  ->
    match uu___25_6680 with
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
        let uu____6700 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6700 FStar_Pprint.hardline
    | uu____6701 ->
        let uu____6702 =
          let uu____6703 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6703  in
        FStar_Pprint.op_Hat_Hat uu____6702 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___26_6706  ->
    match uu___26_6706 with
    | FStar_Parser_AST.Rec  ->
        let uu____6707 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6707
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___27_6709  ->
    match uu___27_6709 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____6714,e) -> e
          | uu____6720 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____6721 = str "#["  in
        let uu____6723 =
          let uu____6724 = p_term false false t1  in
          let uu____6727 =
            let uu____6728 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____6728 break1  in
          FStar_Pprint.op_Hat_Hat uu____6724 uu____6727  in
        FStar_Pprint.op_Hat_Hat uu____6721 uu____6723

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6734 =
          let uu____6735 =
            let uu____6736 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6736  in
          FStar_Pprint.separate_map uu____6735 p_tuplePattern pats  in
        FStar_Pprint.group uu____6734
    | uu____6737 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6746 =
          let uu____6747 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6747 p_constructorPattern pats  in
        FStar_Pprint.group uu____6746
    | uu____6748 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6751;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6756 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6757 = p_constructorPattern hd1  in
        let uu____6758 = p_constructorPattern tl1  in
        infix0 uu____6756 uu____6757 uu____6758
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6760;_},pats)
        ->
        let uu____6766 = p_quident uid  in
        let uu____6767 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6766 uu____6767
    | uu____6768 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6784;
               FStar_Parser_AST.blevel = uu____6785;
               FStar_Parser_AST.aqual = uu____6786;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6795 =
               let uu____6796 = p_ident lid  in
               p_refinement aqual uu____6796 t1 phi  in
             soft_parens_with_nesting uu____6795
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6799;
               FStar_Parser_AST.blevel = uu____6800;
               FStar_Parser_AST.aqual = uu____6801;_},phi))
             ->
             let uu____6807 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6807
         | uu____6808 ->
             let uu____6813 =
               let uu____6814 = p_tuplePattern pat  in
               let uu____6815 =
                 let uu____6816 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6816
                  in
               FStar_Pprint.op_Hat_Hat uu____6814 uu____6815  in
             soft_parens_with_nesting uu____6813)
    | FStar_Parser_AST.PatList pats ->
        let uu____6820 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6820 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6839 =
          match uu____6839 with
          | (lid,pat) ->
              let uu____6846 = p_qlident lid  in
              let uu____6847 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6846 uu____6847
           in
        let uu____6848 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6848
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6860 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6861 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6862 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6860 uu____6861 uu____6862
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6873 =
          let uu____6874 =
            let uu____6875 =
              let uu____6876 = FStar_Ident.text_of_id op  in str uu____6876
               in
            let uu____6878 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6875 uu____6878  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6874  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6873
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6882 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6882 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6890 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6891 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6890 uu____6891
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6893 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6897;
           FStar_Parser_AST.prange = uu____6898;_},uu____6899)
        ->
        let uu____6904 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6904
    | FStar_Parser_AST.PatTuple (uu____6905,false ) ->
        let uu____6912 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6912
    | uu____6913 ->
        let uu____6914 =
          let uu____6916 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6916  in
        failwith uu____6914

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6921;_},uu____6922)
        -> true
    | uu____6929 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6935) -> true
    | uu____6937 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6944 = p_binder' is_atomic b  in
      match uu____6944 with
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
          let uu____6983 =
            let uu____6984 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6985 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6984 uu____6985  in
          (uu____6983, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6991 = p_lident lid  in
          (uu____6991, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6998 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____7009;
                   FStar_Parser_AST.blevel = uu____7010;
                   FStar_Parser_AST.aqual = uu____7011;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____7016 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____7016 t1 phi
            | uu____7017 ->
                let t' =
                  let uu____7019 = is_typ_tuple t  in
                  if uu____7019
                  then
                    let uu____7022 = p_tmFormula t  in
                    soft_parens_with_nesting uu____7022
                  else p_tmFormula t  in
                let uu____7025 =
                  let uu____7026 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____7027 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____7026 uu____7027  in
                (uu____7025, t')
             in
          (match uu____6998 with
           | (b',t') ->
               let catf =
                 let uu____7045 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7045
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7052 =
                         let uu____7053 =
                           let uu____7054 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7054
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7053
                          in
                       FStar_Pprint.group uu____7052
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7059 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7059)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7068 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7096;
                  FStar_Parser_AST.blevel = uu____7097;
                  FStar_Parser_AST.aqual = uu____7098;_},phi)
               ->
               let uu____7102 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7102 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7123 ->
               if is_atomic
               then
                 let uu____7135 = p_atomicTerm t  in
                 (uu____7135, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7142 = p_appTerm t  in
                  (uu____7142, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7153 = p_refinement' aqual_opt binder t phi  in
          match uu____7153 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7169 -> false
            | FStar_Parser_AST.App uu____7181 -> false
            | FStar_Parser_AST.Op uu____7189 -> false
            | uu____7197 -> true  in
          let uu____7199 = p_noSeqTerm false false phi  in
          match uu____7199 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7216 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7216)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7225 =
                let uu____7226 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7226 binder  in
              let uu____7227 =
                let uu____7228 = p_appTerm t  in
                let uu____7229 =
                  let uu____7230 =
                    let uu____7231 =
                      let uu____7232 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7233 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7232 uu____7233  in
                    FStar_Pprint.group uu____7231  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7230
                   in
                FStar_Pprint.op_Hat_Hat uu____7228 uu____7229  in
              (uu____7225, uu____7227)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7247 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7247

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7251 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7254 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7254)
       in
    if uu____7251
    then FStar_Pprint.underscore
    else (let uu____7259 = FStar_Ident.text_of_id lid  in str uu____7259)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7262 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7265 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7265)
       in
    if uu____7262
    then FStar_Pprint.underscore
    else (let uu____7270 = FStar_Ident.text_of_lid lid  in str uu____7270)

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
          let uu____7291 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7291
        else
          (let uu____7294 =
             let uu____7295 =
               let uu____7296 =
                 let uu____7297 =
                   let uu____7298 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7298  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7297  in
               FStar_Pprint.group uu____7296  in
             let uu____7299 =
               let uu____7300 =
                 let uu____7301 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7301  in
               FStar_Pprint.op_Hat_Hat comm uu____7300  in
             FStar_Pprint.ifflat uu____7295 uu____7299  in
           FStar_All.pipe_left FStar_Pprint.group uu____7294)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7309 = p_noSeqTerm true false e1  in
            (match uu____7309 with
             | (comm,t1) ->
                 let uu____7318 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7319 =
                   let uu____7320 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7320
                    in
                 FStar_Pprint.op_Hat_Hat uu____7318 uu____7319)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7324 =
              let uu____7325 =
                let uu____7326 =
                  let uu____7327 = p_lident x  in
                  let uu____7328 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7327 uu____7328  in
                let uu____7329 =
                  let uu____7330 = p_noSeqTermAndComment true false e1  in
                  let uu____7333 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7330 uu____7333  in
                op_Hat_Slash_Plus_Hat uu____7326 uu____7329  in
              FStar_Pprint.group uu____7325  in
            let uu____7334 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7324 uu____7334
        | uu____7335 ->
            let uu____7336 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7336

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
            let uu____7348 = p_noSeqTerm true false e1  in
            (match uu____7348 with
             | (comm,t1) ->
                 let uu____7361 =
                   let uu____7362 =
                     let uu____7363 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7363  in
                   let uu____7364 =
                     let uu____7365 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7365
                      in
                   FStar_Pprint.op_Hat_Hat uu____7362 uu____7364  in
                 (comm, uu____7361))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7369 =
              let uu____7370 =
                let uu____7371 =
                  let uu____7372 =
                    let uu____7373 = p_lident x  in
                    let uu____7374 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7373 uu____7374  in
                  let uu____7375 =
                    let uu____7376 = p_noSeqTermAndComment true false e1  in
                    let uu____7379 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7376 uu____7379  in
                  op_Hat_Slash_Plus_Hat uu____7372 uu____7375  in
                FStar_Pprint.group uu____7371  in
              let uu____7380 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7370 uu____7380  in
            (FStar_Pprint.empty, uu____7369)
        | uu____7381 -> p_noSeqTerm ps pb e

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
            let uu____7401 =
              let uu____7402 = p_tmIff e1  in
              let uu____7403 =
                let uu____7404 =
                  let uu____7405 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7405
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7404  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7402 uu____7403  in
            FStar_Pprint.group uu____7401
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7411 =
              let uu____7412 = p_tmIff e1  in
              let uu____7413 =
                let uu____7414 =
                  let uu____7415 =
                    let uu____7416 = p_typ false false t  in
                    let uu____7419 =
                      let uu____7420 = str "by"  in
                      let uu____7422 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7420 uu____7422  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7416 uu____7419  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7415
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7414  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7412 uu____7413  in
            FStar_Pprint.group uu____7411
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7423;_},e1::e2::e3::[])
            ->
            let uu____7430 =
              let uu____7431 =
                let uu____7432 =
                  let uu____7433 = p_atomicTermNotQUident e1  in
                  let uu____7434 =
                    let uu____7435 =
                      let uu____7436 =
                        let uu____7437 = p_term false false e2  in
                        soft_parens_with_nesting uu____7437  in
                      let uu____7440 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7436 uu____7440  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7435  in
                  FStar_Pprint.op_Hat_Hat uu____7433 uu____7434  in
                FStar_Pprint.group uu____7432  in
              let uu____7441 =
                let uu____7442 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7442  in
              FStar_Pprint.op_Hat_Hat uu____7431 uu____7441  in
            FStar_Pprint.group uu____7430
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7443;_},e1::e2::e3::[])
            ->
            let uu____7450 =
              let uu____7451 =
                let uu____7452 =
                  let uu____7453 = p_atomicTermNotQUident e1  in
                  let uu____7454 =
                    let uu____7455 =
                      let uu____7456 =
                        let uu____7457 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7457  in
                      let uu____7460 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7456 uu____7460  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7455  in
                  FStar_Pprint.op_Hat_Hat uu____7453 uu____7454  in
                FStar_Pprint.group uu____7452  in
              let uu____7461 =
                let uu____7462 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7462  in
              FStar_Pprint.op_Hat_Hat uu____7451 uu____7461  in
            FStar_Pprint.group uu____7450
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7472 =
              let uu____7473 = str "requires"  in
              let uu____7475 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7473 uu____7475  in
            FStar_Pprint.group uu____7472
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7485 =
              let uu____7486 = str "ensures"  in
              let uu____7488 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7486 uu____7488  in
            FStar_Pprint.group uu____7485
        | FStar_Parser_AST.Attributes es ->
            let uu____7492 =
              let uu____7493 = str "attributes"  in
              let uu____7495 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7493 uu____7495  in
            FStar_Pprint.group uu____7492
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7500 =
                let uu____7501 =
                  let uu____7502 = str "if"  in
                  let uu____7504 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7502 uu____7504  in
                let uu____7507 =
                  let uu____7508 = str "then"  in
                  let uu____7510 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7508 uu____7510  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7501 uu____7507  in
              FStar_Pprint.group uu____7500
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7514,uu____7515,e31) when
                     is_unit e31 ->
                     let uu____7517 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7517
                 | uu____7520 -> p_noSeqTermAndComment false false e2  in
               let uu____7523 =
                 let uu____7524 =
                   let uu____7525 = str "if"  in
                   let uu____7527 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7525 uu____7527  in
                 let uu____7530 =
                   let uu____7531 =
                     let uu____7532 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7532 e2_doc  in
                   let uu____7534 =
                     let uu____7535 = str "else"  in
                     let uu____7537 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7535 uu____7537  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7531 uu____7534  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7524 uu____7530  in
               FStar_Pprint.group uu____7523)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7560 =
              let uu____7561 =
                let uu____7562 =
                  let uu____7563 = str "try"  in
                  let uu____7565 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7563 uu____7565  in
                let uu____7568 =
                  let uu____7569 = str "with"  in
                  let uu____7571 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7569 uu____7571  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7562 uu____7568  in
              FStar_Pprint.group uu____7561  in
            let uu____7580 = paren_if (ps || pb)  in uu____7580 uu____7560
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7607 =
              let uu____7608 =
                let uu____7609 =
                  let uu____7610 = str "match"  in
                  let uu____7612 = p_noSeqTermAndComment false false e1  in
                  let uu____7615 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7610 uu____7612 uu____7615
                   in
                let uu____7619 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7609 uu____7619  in
              FStar_Pprint.group uu____7608  in
            let uu____7628 = paren_if (ps || pb)  in uu____7628 uu____7607
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7635 =
              let uu____7636 =
                let uu____7637 =
                  let uu____7638 = str "let open"  in
                  let uu____7640 = p_quident uid  in
                  let uu____7641 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7638 uu____7640 uu____7641
                   in
                let uu____7645 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7637 uu____7645  in
              FStar_Pprint.group uu____7636  in
            let uu____7647 = paren_if ps  in uu____7647 uu____7635
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7712 is_last =
              match uu____7712 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7746 =
                          let uu____7747 = str "let"  in
                          let uu____7749 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7747 uu____7749
                           in
                        FStar_Pprint.group uu____7746
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7752 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7758 = p_term_sep false false e2  in
                  (match uu____7758 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7768 =
                         if is_last
                         then
                           let uu____7770 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7771 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7770 doc_expr1
                             uu____7771
                         else
                           (let uu____7777 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7777)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7768)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7828 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7828
                     else
                       (let uu____7839 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7839)) lbs
               in
            let lbs_doc =
              let uu____7849 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7849  in
            let uu____7850 =
              let uu____7851 =
                let uu____7852 =
                  let uu____7853 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7853
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7852  in
              FStar_Pprint.group uu____7851  in
            let uu____7855 = paren_if ps  in uu____7855 uu____7850
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7862;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7865;
                                                             FStar_Parser_AST.level
                                                               = uu____7866;_})
            when matches_var maybe_x x ->
            let uu____7893 =
              let uu____7894 =
                let uu____7895 = str "function"  in
                let uu____7897 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7895 uu____7897  in
              FStar_Pprint.group uu____7894  in
            let uu____7906 = paren_if (ps || pb)  in uu____7906 uu____7893
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7912 =
              let uu____7913 = str "quote"  in
              let uu____7915 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7913 uu____7915  in
            FStar_Pprint.group uu____7912
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7917 =
              let uu____7918 = str "`"  in
              let uu____7920 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7918 uu____7920  in
            FStar_Pprint.group uu____7917
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7922 =
              let uu____7923 = str "`%"  in
              let uu____7925 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7923 uu____7925  in
            FStar_Pprint.group uu____7922
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7927;
              FStar_Parser_AST.level = uu____7928;_}
            ->
            let uu____7929 =
              let uu____7930 = str "`@"  in
              let uu____7932 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7930 uu____7932  in
            FStar_Pprint.group uu____7929
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7934 =
              let uu____7935 = str "`#"  in
              let uu____7937 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7935 uu____7937  in
            FStar_Pprint.group uu____7934
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____7946 = str "calc"  in
              let uu____7948 =
                let uu____7949 =
                  let uu____7950 = p_noSeqTermAndComment false false rel  in
                  let uu____7953 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____7950 uu____7953  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7949  in
              FStar_Pprint.op_Hat_Hat uu____7946 uu____7948  in
            let bot = FStar_Pprint.rbrace  in
            let uu____7955 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____7956 =
              let uu____7957 =
                let uu____7958 =
                  let uu____7959 = p_noSeqTermAndComment false false init1
                     in
                  let uu____7962 =
                    let uu____7963 = str ";"  in
                    let uu____7965 =
                      let uu____7966 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____7966
                       in
                    FStar_Pprint.op_Hat_Hat uu____7963 uu____7965  in
                  FStar_Pprint.op_Hat_Hat uu____7959 uu____7962  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7958  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____7957
               in
            FStar_Pprint.enclose head1 uu____7955 uu____7956
        | uu____7968 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____7969  ->
    fun uu____7970  ->
      match uu____7970 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____7975 =
            let uu____7976 = p_noSeqTermAndComment false false rel  in
            let uu____7979 =
              let uu____7980 =
                let uu____7981 =
                  let uu____7982 =
                    let uu____7983 = p_noSeqTermAndComment false false just
                       in
                    let uu____7986 =
                      let uu____7987 =
                        let uu____7988 =
                          let uu____7989 =
                            let uu____7990 =
                              p_noSeqTermAndComment false false next  in
                            let uu____7993 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____7990 uu____7993  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____7989
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____7988
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7987
                       in
                    FStar_Pprint.op_Hat_Hat uu____7983 uu____7986  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7982  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____7981  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7980  in
            FStar_Pprint.op_Hat_Hat uu____7976 uu____7979  in
          FStar_Pprint.group uu____7975

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___28_7995  ->
    match uu___28_7995 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____8007 =
          let uu____8008 = str "[@"  in
          let uu____8010 =
            let uu____8011 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____8012 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____8011 uu____8012  in
          FStar_Pprint.op_Hat_Slash_Hat uu____8008 uu____8010  in
        FStar_Pprint.group uu____8007

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
                 let uu____8049 =
                   let uu____8050 =
                     let uu____8051 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8051 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8050 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8049 term_doc
             | pats ->
                 let uu____8059 =
                   let uu____8060 =
                     let uu____8061 =
                       let uu____8062 =
                         let uu____8063 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8063
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8062 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8066 = p_trigger trigger  in
                     prefix2 uu____8061 uu____8066  in
                   FStar_Pprint.group uu____8060  in
                 prefix2 uu____8059 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8087 =
                   let uu____8088 =
                     let uu____8089 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8089 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8088 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8087 term_doc
             | pats ->
                 let uu____8097 =
                   let uu____8098 =
                     let uu____8099 =
                       let uu____8100 =
                         let uu____8101 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8101
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8100 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8104 = p_trigger trigger  in
                     prefix2 uu____8099 uu____8104  in
                   FStar_Pprint.group uu____8098  in
                 prefix2 uu____8097 term_doc)
        | uu____8105 -> p_simpleTerm ps pb e

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
      let uu____8126 = all_binders_annot t  in
      if uu____8126
      then
        let uu____8129 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8129
      else
        (let uu____8140 =
           let uu____8141 =
             let uu____8142 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8142  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8141  in
         FStar_Pprint.group uu____8140)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8201 = x  in
      match uu____8201 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8266 = hd1  in
               (match uu____8266 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8338 = cb  in
      match uu____8338 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8357 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8363 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8363) hd1 tl1
                  in
               cat_with_colon uu____8357 typ)
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
                 FStar_Parser_AST.brange = uu____8442;
                 FStar_Parser_AST.blevel = uu____8443;
                 FStar_Parser_AST.aqual = uu____8444;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8453 =
                 let uu____8458 = p_ident lid  in
                 p_refinement' aqual uu____8458 t1 phi  in
               FStar_Pervasives_Native.Some uu____8453
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8465) ->
               let uu____8470 =
                 let uu____8475 =
                   let uu____8476 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8477 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8476 uu____8477  in
                 let uu____8478 = p_tmEqNoRefinement t  in
                 (uu____8475, uu____8478)  in
               FStar_Pervasives_Native.Some uu____8470
           | uu____8483 -> FStar_Pervasives_Native.None)
      | uu____8492 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8505 -> false
      | uu____8517 -> true  in
    let uu____8519 = map_if_all all_binders pats  in
    match uu____8519 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8551 = collapse_pats bs  in
        (uu____8551,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8568 = FStar_List.map p_atomicPattern pats  in
        (uu____8568,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8580 -> str "forall"
    | FStar_Parser_AST.QExists uu____8594 -> str "exists"
    | uu____8608 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___29_8610  ->
    match uu___29_8610 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8622 =
          let uu____8623 =
            let uu____8624 =
              let uu____8625 = str "pattern"  in
              let uu____8627 =
                let uu____8628 =
                  let uu____8629 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8629
                   in
                FStar_Pprint.op_Hat_Hat uu____8628 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8625 uu____8627  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8624  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8623  in
        FStar_Pprint.group uu____8622

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8637 = str "\\/"  in
    FStar_Pprint.separate_map uu____8637 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8644 =
      let uu____8645 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8645 p_appTerm pats  in
    FStar_Pprint.group uu____8644

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8657 = p_term_sep false pb e1  in
            (match uu____8657 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8666 = str "fun"  in
                   let uu____8668 =
                     let uu____8669 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8669
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8666 uu____8668  in
                 let uu____8670 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8672 =
                       let uu____8673 =
                         let uu____8674 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8674  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8673
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8672
                   else
                     (let uu____8677 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8677)
                    in
                 let uu____8678 = paren_if ps  in uu____8678 uu____8670)
        | uu____8683 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8691  ->
      match uu____8691 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8715 =
                    let uu____8716 =
                      let uu____8717 =
                        let uu____8718 = p_tuplePattern p  in
                        let uu____8719 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8718 uu____8719  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8717
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8716  in
                  FStar_Pprint.group uu____8715
              | FStar_Pervasives_Native.Some f ->
                  let uu____8721 =
                    let uu____8722 =
                      let uu____8723 =
                        let uu____8724 =
                          let uu____8725 =
                            let uu____8726 = p_tuplePattern p  in
                            let uu____8727 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8726
                              uu____8727
                             in
                          FStar_Pprint.group uu____8725  in
                        let uu____8729 =
                          let uu____8730 =
                            let uu____8733 = p_tmFormula f  in
                            [uu____8733; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8730  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8724 uu____8729
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8723
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8722  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8721
               in
            let uu____8735 = p_term_sep false pb e  in
            match uu____8735 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8745 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8745
                   else
                     (let uu____8748 =
                        let uu____8749 =
                          let uu____8750 =
                            let uu____8751 =
                              let uu____8752 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8752  in
                            op_Hat_Slash_Plus_Hat branch uu____8751  in
                          FStar_Pprint.group uu____8750  in
                        let uu____8753 =
                          let uu____8754 =
                            let uu____8755 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8755  in
                          FStar_Pprint.op_Hat_Hat branch uu____8754  in
                        FStar_Pprint.ifflat uu____8749 uu____8753  in
                      FStar_Pprint.group uu____8748))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8759 =
                       let uu____8760 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8760  in
                     op_Hat_Slash_Plus_Hat branch uu____8759)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8771 =
                      let uu____8772 =
                        let uu____8773 =
                          let uu____8774 =
                            let uu____8775 =
                              let uu____8776 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8776  in
                            FStar_Pprint.separate_map uu____8775
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8774
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8773
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8772  in
                    FStar_Pprint.group uu____8771
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8778 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8780;_},e1::e2::[])
        ->
        let uu____8786 = str "<==>"  in
        let uu____8788 = p_tmImplies e1  in
        let uu____8789 = p_tmIff e2  in
        infix0 uu____8786 uu____8788 uu____8789
    | uu____8790 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8792;_},e1::e2::[])
        ->
        let uu____8798 = str "==>"  in
        let uu____8800 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8806 = p_tmImplies e2  in
        infix0 uu____8798 uu____8800 uu____8806
    | uu____8807 ->
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
          let uu____8821 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8821 with
          | (terms',last1) ->
              let uu____8841 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8876 =
                      let uu____8877 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8877
                       in
                    let uu____8878 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8876, uu____8878)
                | Binders (n1,ln,parens1) ->
                    let uu____8892 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8900 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8892, break1, uu____8900)
                 in
              (match uu____8841 with
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
                    | uu____8933 ->
                        let uu____8934 =
                          let uu____8935 =
                            let uu____8936 =
                              let uu____8937 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8938 =
                                let uu____8939 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8939
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8937 uu____8938
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8936  in
                          let uu____8940 =
                            let uu____8941 =
                              let uu____8942 =
                                let uu____8943 =
                                  let uu____8944 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8944  in
                                let uu____8945 =
                                  let uu____8946 =
                                    let uu____8947 =
                                      let uu____8948 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8949 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8955 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8955)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8948
                                        uu____8949
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8947
                                     in
                                  jump2 uu____8946  in
                                FStar_Pprint.ifflat uu____8943 uu____8945  in
                              FStar_Pprint.group uu____8942  in
                            let uu____8957 =
                              let uu____8958 =
                                let uu____8959 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8959  in
                              FStar_Pprint.align uu____8958  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8941 uu____8957
                             in
                          FStar_Pprint.ifflat uu____8935 uu____8940  in
                        FStar_Pprint.group uu____8934))

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
            | Arrows uu____8973 -> p_tmArrow' p_Tm e
            | Binders uu____8980 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____9003 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____9009 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____9003 uu____9009
      | uu____9012 -> let uu____9013 = p_Tm e  in [uu____9013]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____9066 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9092 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____9066 uu____9092
        | uu____9115 ->
            let uu____9116 =
              let uu____9127 = p_Tm1 e1  in
              (uu____9127, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9116]
         in
      let fold_fun bs x =
        let uu____9225 = x  in
        match uu____9225 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9361 = hd1  in
                 (match uu____9361 with
                  | (b2s,t2,uu____9390) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9500 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9561 = cb  in
        match uu____9561 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9590 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9603 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9609 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9609) hd1 tl1
                         in
                      f uu____9603 typ))
         in
      let binders =
        let uu____9627 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9627  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9690 =
        let uu____9691 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9691 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9690  in
    let disj =
      let uu____9694 =
        let uu____9695 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9695 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9694  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9715;_},e1::e2::[])
        ->
        let uu____9721 = p_tmDisjunction e1  in
        let uu____9726 = let uu____9731 = p_tmConjunction e2  in [uu____9731]
           in
        FStar_List.append uu____9721 uu____9726
    | uu____9740 -> let uu____9741 = p_tmConjunction e  in [uu____9741]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9751;_},e1::e2::[])
        ->
        let uu____9757 = p_tmConjunction e1  in
        let uu____9760 = let uu____9763 = p_tmTuple e2  in [uu____9763]  in
        FStar_List.append uu____9757 uu____9760
    | uu____9764 -> let uu____9765 = p_tmTuple e  in [uu____9765]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9782 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9782
          (fun uu____9790  ->
             match uu____9790 with | (e1,uu____9796) -> p_tmEq e1) args
    | uu____9797 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9806 =
             let uu____9807 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9807  in
           FStar_Pprint.group uu____9806)

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
               (let uu____9826 = FStar_Ident.text_of_id op  in
                uu____9826 = "="))
              ||
              (let uu____9831 = FStar_Ident.text_of_id op  in
               uu____9831 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9837 = levels op1  in
            (match uu____9837 with
             | (left1,mine,right1) ->
                 let uu____9856 =
                   let uu____9857 = FStar_All.pipe_left str op1  in
                   let uu____9859 = p_tmEqWith' p_X left1 e1  in
                   let uu____9860 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9857 uu____9859 uu____9860  in
                 paren_if_gt curr mine uu____9856)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9861;_},e1::e2::[])
            ->
            let uu____9867 =
              let uu____9868 = p_tmEqWith p_X e1  in
              let uu____9869 =
                let uu____9870 =
                  let uu____9871 =
                    let uu____9872 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9872  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9871  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9870  in
              FStar_Pprint.op_Hat_Hat uu____9868 uu____9869  in
            FStar_Pprint.group uu____9867
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9873;_},e1::[])
            ->
            let uu____9878 = levels "-"  in
            (match uu____9878 with
             | (left1,mine,right1) ->
                 let uu____9898 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9898)
        | uu____9899 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9947)::(e2,uu____9949)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9969 = is_list e  in Prims.op_Negation uu____9969)
              ->
              let op = "::"  in
              let uu____9974 = levels op  in
              (match uu____9974 with
               | (left1,mine,right1) ->
                   let uu____9993 =
                     let uu____9994 = str op  in
                     let uu____9995 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9997 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9994 uu____9995 uu____9997  in
                   paren_if_gt curr mine uu____9993)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____10016 = levels op  in
              (match uu____10016 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____10050 = p_binder false b  in
                         let uu____10052 =
                           let uu____10053 =
                             let uu____10054 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10054 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10053
                            in
                         FStar_Pprint.op_Hat_Hat uu____10050 uu____10052
                     | FStar_Util.Inr t ->
                         let uu____10056 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____10058 =
                           let uu____10059 =
                             let uu____10060 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____10060 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____10059
                            in
                         FStar_Pprint.op_Hat_Hat uu____10056 uu____10058
                      in
                   let uu____10061 =
                     let uu____10062 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10067 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____10062 uu____10067  in
                   paren_if_gt curr mine uu____10061)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10069;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10099 = levels op  in
              (match uu____10099 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10119 = str op  in
                     let uu____10120 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10122 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10119 uu____10120 uu____10122
                   else
                     (let uu____10126 =
                        let uu____10127 = str op  in
                        let uu____10128 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10130 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10127 uu____10128 uu____10130  in
                      paren_if_gt curr mine uu____10126))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10139 = levels op1  in
              (match uu____10139 with
               | (left1,mine,right1) ->
                   let uu____10158 =
                     let uu____10159 = str op1  in
                     let uu____10160 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10162 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10159 uu____10160 uu____10162  in
                   paren_if_gt curr mine uu____10158)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10182 =
                let uu____10183 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10184 =
                  let uu____10185 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10185 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10183 uu____10184  in
              braces_with_nesting uu____10182
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10190;_},e1::[])
              ->
              let uu____10195 =
                let uu____10196 = str "~"  in
                let uu____10198 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10196 uu____10198  in
              FStar_Pprint.group uu____10195
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10200;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10209 = levels op  in
                   (match uu____10209 with
                    | (left1,mine,right1) ->
                        let uu____10228 =
                          let uu____10229 = str op  in
                          let uu____10230 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10232 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10229 uu____10230 uu____10232  in
                        paren_if_gt curr mine uu____10228)
               | uu____10234 -> p_X e)
          | uu____10235 -> p_X e

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
        let uu____10242 =
          let uu____10243 = p_lident lid  in
          let uu____10244 =
            let uu____10245 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10245  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10243 uu____10244  in
        FStar_Pprint.group uu____10242
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10248 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10250 = p_appTerm e  in
    let uu____10251 =
      let uu____10252 =
        let uu____10253 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10253 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10252  in
    FStar_Pprint.op_Hat_Hat uu____10250 uu____10251

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10259 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10259 t phi
      | FStar_Parser_AST.TAnnotated uu____10260 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10266 ->
          let uu____10267 =
            let uu____10269 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10269
             in
          failwith uu____10267
      | FStar_Parser_AST.TVariable uu____10272 ->
          let uu____10273 =
            let uu____10275 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10275
             in
          failwith uu____10273
      | FStar_Parser_AST.NoName uu____10278 ->
          let uu____10279 =
            let uu____10281 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10281
             in
          failwith uu____10279

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10285  ->
      match uu____10285 with
      | (lid,e) ->
          let uu____10293 =
            let uu____10294 = p_qlident lid  in
            let uu____10295 =
              let uu____10296 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10296
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10294 uu____10295  in
          FStar_Pprint.group uu____10293

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10299 when is_general_application e ->
        let uu____10306 = head_and_args e  in
        (match uu____10306 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10353 = p_argTerm e1  in
                  let uu____10354 =
                    let uu____10355 =
                      let uu____10356 =
                        let uu____10357 = str "`"  in
                        let uu____10359 =
                          let uu____10360 = p_indexingTerm head1  in
                          let uu____10361 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10360 uu____10361  in
                        FStar_Pprint.op_Hat_Hat uu____10357 uu____10359  in
                      FStar_Pprint.group uu____10356  in
                    let uu____10363 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10355 uu____10363  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10353 uu____10354
              | uu____10364 ->
                  let uu____10371 =
                    let uu____10382 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10382
                    then
                      let uu____10416 =
                        FStar_Util.take
                          (fun uu____10440  ->
                             match uu____10440 with
                             | (uu____10446,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10416 with
                      | (fs_typ_args,args1) ->
                          let uu____10484 =
                            let uu____10485 = p_indexingTerm head1  in
                            let uu____10486 =
                              let uu____10487 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10487
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10485 uu____10486
                             in
                          (uu____10484, args1)
                    else
                      (let uu____10502 = p_indexingTerm head1  in
                       (uu____10502, args))
                     in
                  (match uu____10371 with
                   | (head_doc,args1) ->
                       let uu____10523 =
                         let uu____10524 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10524 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10523)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10546 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10546)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10565 =
               let uu____10566 = p_quident lid  in
               let uu____10567 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10566 uu____10567  in
             FStar_Pprint.group uu____10565
         | hd1::tl1 ->
             let uu____10584 =
               let uu____10585 =
                 let uu____10586 =
                   let uu____10587 = p_quident lid  in
                   let uu____10588 = p_argTerm hd1  in
                   prefix2 uu____10587 uu____10588  in
                 FStar_Pprint.group uu____10586  in
               let uu____10589 =
                 let uu____10590 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10590  in
               FStar_Pprint.op_Hat_Hat uu____10585 uu____10589  in
             FStar_Pprint.group uu____10584)
    | uu____10595 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10606 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10606 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10610 = str "#"  in
        let uu____10612 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10610 uu____10612
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10615 = str "#["  in
        let uu____10617 =
          let uu____10618 = p_indexingTerm t  in
          let uu____10619 =
            let uu____10620 = str "]"  in
            let uu____10622 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10620 uu____10622  in
          FStar_Pprint.op_Hat_Hat uu____10618 uu____10619  in
        FStar_Pprint.op_Hat_Hat uu____10615 uu____10617
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10625  ->
    match uu____10625 with | (e,uu____10631) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10636;_},e1::e2::[])
          ->
          let uu____10642 =
            let uu____10643 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10644 =
              let uu____10645 =
                let uu____10646 = p_term false false e2  in
                soft_parens_with_nesting uu____10646  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10645  in
            FStar_Pprint.op_Hat_Hat uu____10643 uu____10644  in
          FStar_Pprint.group uu____10642
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10649;_},e1::e2::[])
          ->
          let uu____10655 =
            let uu____10656 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10657 =
              let uu____10658 =
                let uu____10659 = p_term false false e2  in
                soft_brackets_with_nesting uu____10659  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10658  in
            FStar_Pprint.op_Hat_Hat uu____10656 uu____10657  in
          FStar_Pprint.group uu____10655
      | uu____10662 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10667 = p_quident lid  in
        let uu____10668 =
          let uu____10669 =
            let uu____10670 = p_term false false e1  in
            soft_parens_with_nesting uu____10670  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10669  in
        FStar_Pprint.op_Hat_Hat uu____10667 uu____10668
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10678 =
          let uu____10679 = FStar_Ident.text_of_id op  in str uu____10679  in
        let uu____10681 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10678 uu____10681
    | uu____10682 -> p_atomicTermNotQUident e

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
         | uu____10695 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10704 =
          let uu____10705 = FStar_Ident.text_of_id op  in str uu____10705  in
        let uu____10707 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10704 uu____10707
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10711 =
          let uu____10712 =
            let uu____10713 =
              let uu____10714 = FStar_Ident.text_of_id op  in str uu____10714
               in
            let uu____10716 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10713 uu____10716  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10712  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10711
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10731 = all_explicit args  in
        if uu____10731
        then
          let uu____10734 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10735 =
            let uu____10736 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10737 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10736 p_tmEq uu____10737  in
          let uu____10744 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10734 uu____10735 uu____10744
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10766 =
                 let uu____10767 = p_quident lid  in
                 let uu____10768 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10767 uu____10768  in
               FStar_Pprint.group uu____10766
           | hd1::tl1 ->
               let uu____10785 =
                 let uu____10786 =
                   let uu____10787 =
                     let uu____10788 = p_quident lid  in
                     let uu____10789 = p_argTerm hd1  in
                     prefix2 uu____10788 uu____10789  in
                   FStar_Pprint.group uu____10787  in
                 let uu____10790 =
                   let uu____10791 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10791  in
                 FStar_Pprint.op_Hat_Hat uu____10786 uu____10790  in
               FStar_Pprint.group uu____10785)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10798 =
          let uu____10799 = p_atomicTermNotQUident e1  in
          let uu____10800 =
            let uu____10801 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10801  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10799 uu____10800
           in
        FStar_Pprint.group uu____10798
    | uu____10804 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10809 = p_quident constr_lid  in
        let uu____10810 =
          let uu____10811 =
            let uu____10812 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10812  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10811  in
        FStar_Pprint.op_Hat_Hat uu____10809 uu____10810
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10814 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10814 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10816 = p_term_sep false false e1  in
        (match uu____10816 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10829 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10829))
    | uu____10830 when is_array e ->
        let es = extract_from_list e  in
        let uu____10834 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10835 =
          let uu____10836 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10836
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10841 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10834 uu____10835 uu____10841
    | uu____10844 when is_list e ->
        let uu____10845 =
          let uu____10846 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10847 = extract_from_list e  in
          separate_map_or_flow_last uu____10846
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10847
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10845 FStar_Pprint.rbracket
    | uu____10856 when is_lex_list e ->
        let uu____10857 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10858 =
          let uu____10859 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10860 = extract_from_list e  in
          separate_map_or_flow_last uu____10859
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10860
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10857 uu____10858 FStar_Pprint.rbracket
    | uu____10869 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10873 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10874 =
          let uu____10875 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10875 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10873 uu____10874 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10885 =
          let uu____10886 =
            let uu____10888 = FStar_String.op_Hat s "*)"  in
            FStar_String.op_Hat "(*" uu____10888  in
          str uu____10886  in
        let uu____10892 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10885 uu____10892
    | FStar_Parser_AST.Op (op,args) when
        let uu____10901 = handleable_op op args  in
        Prims.op_Negation uu____10901 ->
        let uu____10903 =
          let uu____10905 =
            let uu____10907 = FStar_Ident.text_of_id op  in
            let uu____10909 =
              let uu____10911 =
                let uu____10913 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                FStar_String.op_Hat uu____10913
                  " arguments couldn't be handled by the pretty printer"
                 in
              FStar_String.op_Hat " with " uu____10911  in
            FStar_String.op_Hat uu____10907 uu____10909  in
          FStar_String.op_Hat "Operation " uu____10905  in
        failwith uu____10903
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____10920 = p_term false false e  in
        soft_parens_with_nesting uu____10920
    | FStar_Parser_AST.Const uu____10923 ->
        let uu____10924 = p_term false false e  in
        soft_parens_with_nesting uu____10924
    | FStar_Parser_AST.Op uu____10927 ->
        let uu____10934 = p_term false false e  in
        soft_parens_with_nesting uu____10934
    | FStar_Parser_AST.Tvar uu____10937 ->
        let uu____10938 = p_term false false e  in
        soft_parens_with_nesting uu____10938
    | FStar_Parser_AST.Var uu____10941 ->
        let uu____10942 = p_term false false e  in
        soft_parens_with_nesting uu____10942
    | FStar_Parser_AST.Name uu____10945 ->
        let uu____10946 = p_term false false e  in
        soft_parens_with_nesting uu____10946
    | FStar_Parser_AST.Construct uu____10949 ->
        let uu____10960 = p_term false false e  in
        soft_parens_with_nesting uu____10960
    | FStar_Parser_AST.Abs uu____10963 ->
        let uu____10970 = p_term false false e  in
        soft_parens_with_nesting uu____10970
    | FStar_Parser_AST.App uu____10973 ->
        let uu____10980 = p_term false false e  in
        soft_parens_with_nesting uu____10980
    | FStar_Parser_AST.Let uu____10983 ->
        let uu____11004 = p_term false false e  in
        soft_parens_with_nesting uu____11004
    | FStar_Parser_AST.LetOpen uu____11007 ->
        let uu____11012 = p_term false false e  in
        soft_parens_with_nesting uu____11012
    | FStar_Parser_AST.Seq uu____11015 ->
        let uu____11020 = p_term false false e  in
        soft_parens_with_nesting uu____11020
    | FStar_Parser_AST.Bind uu____11023 ->
        let uu____11030 = p_term false false e  in
        soft_parens_with_nesting uu____11030
    | FStar_Parser_AST.If uu____11033 ->
        let uu____11040 = p_term false false e  in
        soft_parens_with_nesting uu____11040
    | FStar_Parser_AST.Match uu____11043 ->
        let uu____11058 = p_term false false e  in
        soft_parens_with_nesting uu____11058
    | FStar_Parser_AST.TryWith uu____11061 ->
        let uu____11076 = p_term false false e  in
        soft_parens_with_nesting uu____11076
    | FStar_Parser_AST.Ascribed uu____11079 ->
        let uu____11088 = p_term false false e  in
        soft_parens_with_nesting uu____11088
    | FStar_Parser_AST.Record uu____11091 ->
        let uu____11104 = p_term false false e  in
        soft_parens_with_nesting uu____11104
    | FStar_Parser_AST.Project uu____11107 ->
        let uu____11112 = p_term false false e  in
        soft_parens_with_nesting uu____11112
    | FStar_Parser_AST.Product uu____11115 ->
        let uu____11122 = p_term false false e  in
        soft_parens_with_nesting uu____11122
    | FStar_Parser_AST.Sum uu____11125 ->
        let uu____11136 = p_term false false e  in
        soft_parens_with_nesting uu____11136
    | FStar_Parser_AST.QForall uu____11139 ->
        let uu____11152 = p_term false false e  in
        soft_parens_with_nesting uu____11152
    | FStar_Parser_AST.QExists uu____11155 ->
        let uu____11168 = p_term false false e  in
        soft_parens_with_nesting uu____11168
    | FStar_Parser_AST.Refine uu____11171 ->
        let uu____11176 = p_term false false e  in
        soft_parens_with_nesting uu____11176
    | FStar_Parser_AST.NamedTyp uu____11179 ->
        let uu____11184 = p_term false false e  in
        soft_parens_with_nesting uu____11184
    | FStar_Parser_AST.Requires uu____11187 ->
        let uu____11195 = p_term false false e  in
        soft_parens_with_nesting uu____11195
    | FStar_Parser_AST.Ensures uu____11198 ->
        let uu____11206 = p_term false false e  in
        soft_parens_with_nesting uu____11206
    | FStar_Parser_AST.Attributes uu____11209 ->
        let uu____11212 = p_term false false e  in
        soft_parens_with_nesting uu____11212
    | FStar_Parser_AST.Quote uu____11215 ->
        let uu____11220 = p_term false false e  in
        soft_parens_with_nesting uu____11220
    | FStar_Parser_AST.VQuote uu____11223 ->
        let uu____11224 = p_term false false e  in
        soft_parens_with_nesting uu____11224
    | FStar_Parser_AST.Antiquote uu____11227 ->
        let uu____11228 = p_term false false e  in
        soft_parens_with_nesting uu____11228
    | FStar_Parser_AST.CalcProof uu____11231 ->
        let uu____11240 = p_term false false e  in
        soft_parens_with_nesting uu____11240

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___32_11243  ->
    match uu___32_11243 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11252) ->
        let uu____11255 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11255
    | FStar_Const.Const_bytearray (bytes,uu____11257) ->
        let uu____11262 =
          let uu____11263 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11263  in
        let uu____11264 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11262 uu____11264
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___30_11287 =
          match uu___30_11287 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___31_11294 =
          match uu___31_11294 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11309  ->
               match uu____11309 with
               | (s,w) ->
                   let uu____11316 = signedness s  in
                   let uu____11317 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11316 uu____11317)
            sign_width_opt
           in
        let uu____11318 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11318 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11322 = FStar_Range.string_of_range r  in str uu____11322
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11326 = p_quident lid  in
        let uu____11327 =
          let uu____11328 =
            let uu____11329 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11329  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11328  in
        FStar_Pprint.op_Hat_Hat uu____11326 uu____11327

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11332 = str "u#"  in
    let uu____11334 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11332 uu____11334

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11336;_},u1::u2::[])
        ->
        let uu____11342 =
          let uu____11343 = p_universeFrom u1  in
          let uu____11344 =
            let uu____11345 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11345  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11343 uu____11344  in
        FStar_Pprint.group uu____11342
    | FStar_Parser_AST.App uu____11346 ->
        let uu____11353 = head_and_args u  in
        (match uu____11353 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11379 =
                    let uu____11380 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11381 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11389  ->
                           match uu____11389 with
                           | (u1,uu____11395) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11380 uu____11381  in
                  FStar_Pprint.group uu____11379
              | uu____11396 ->
                  let uu____11397 =
                    let uu____11399 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11399
                     in
                  failwith uu____11397))
    | uu____11402 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11428 = FStar_Ident.text_of_id id1  in str uu____11428
    | FStar_Parser_AST.Paren u1 ->
        let uu____11431 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11431
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11432;_},uu____11433::uu____11434::[])
        ->
        let uu____11438 = p_universeFrom u  in
        soft_parens_with_nesting uu____11438
    | FStar_Parser_AST.App uu____11439 ->
        let uu____11446 = p_universeFrom u  in
        soft_parens_with_nesting uu____11446
    | uu____11447 ->
        let uu____11448 =
          let uu____11450 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11450
           in
        failwith uu____11448

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
       | FStar_Parser_AST.Module (uu____11539,decls) ->
           let uu____11545 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11545
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11554,decls,uu____11556) ->
           let uu____11563 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11563
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11623  ->
         match uu____11623 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11645)) -> false
      | ([],uu____11649) -> false
      | uu____11653 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11663 -> true
         | uu____11665 -> false)
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
        | FStar_Parser_AST.Module (uu____11708,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11714,decls,uu____11716) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11768 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11781;
                 FStar_Parser_AST.doc = uu____11782;
                 FStar_Parser_AST.quals = uu____11783;
                 FStar_Parser_AST.attrs = uu____11784;_}::uu____11785 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11791 =
                   let uu____11794 =
                     let uu____11797 = FStar_List.tl ds  in d :: uu____11797
                      in
                   d0 :: uu____11794  in
                 (uu____11791, (d0.FStar_Parser_AST.drange))
             | uu____11802 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11768 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11859 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11859 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11968 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11968, comments1))))))
  