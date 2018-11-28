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
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
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
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2118 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2118 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2170) ->
          assoc_levels
      | uu____2208 -> failwith (Prims.strcat "Unrecognized operator " s)
  
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
         (id1,uu____5091)) ->
          let uu____5094 =
            let uu____5096 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5096 FStar_Util.is_upper  in
          if uu____5094
          then
            let uu____5102 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____5102 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____5105 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____5112 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____5115 =
      let uu____5116 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____5117 =
        let uu____5118 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____5118  in
      FStar_Pprint.op_Hat_Hat uu____5116 uu____5117  in
    FStar_Pprint.op_Hat_Hat uu____5112 uu____5115

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____5120 ->
        let uu____5121 =
          let uu____5122 = str "@ "  in
          let uu____5124 =
            let uu____5125 =
              let uu____5126 =
                let uu____5127 =
                  let uu____5128 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____5128  in
                FStar_Pprint.op_Hat_Hat uu____5127 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____5126  in
            FStar_Pprint.op_Hat_Hat uu____5125 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____5122 uu____5124  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____5121

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____5131  ->
    match uu____5131 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____5179 =
                match uu____5179 with
                | (kwd,arg) ->
                    let uu____5192 = str "@"  in
                    let uu____5194 =
                      let uu____5195 = str kwd  in
                      let uu____5196 =
                        let uu____5197 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5197
                         in
                      FStar_Pprint.op_Hat_Hat uu____5195 uu____5196  in
                    FStar_Pprint.op_Hat_Hat uu____5192 uu____5194
                 in
              let uu____5198 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____5198 FStar_Pprint.hardline
           in
        let uu____5205 =
          let uu____5206 =
            let uu____5207 =
              let uu____5208 = str doc1  in
              let uu____5209 =
                let uu____5210 =
                  let uu____5211 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5211  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____5210  in
              FStar_Pprint.op_Hat_Hat uu____5208 uu____5209  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5207  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____5206  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5205

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5215 =
          let uu____5216 = str "val"  in
          let uu____5218 =
            let uu____5219 =
              let uu____5220 = p_lident lid  in
              let uu____5221 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____5220 uu____5221  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5219  in
          FStar_Pprint.op_Hat_Hat uu____5216 uu____5218  in
        let uu____5222 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____5215 uu____5222
    | FStar_Parser_AST.TopLevelLet (uu____5225,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____5250 =
               let uu____5251 = str "let"  in p_letlhs uu____5251 lb false
                in
             FStar_Pprint.group uu____5250) lbs
    | uu____5254 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___114_5269 =
          match uu___114_5269 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____5277 = f x  in
              let uu____5278 =
                let uu____5279 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____5279  in
              FStar_Pprint.op_Hat_Hat uu____5277 uu____5278
           in
        let uu____5280 = str "["  in
        let uu____5282 =
          let uu____5283 = p_list' l  in
          let uu____5284 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____5283 uu____5284  in
        FStar_Pprint.op_Hat_Hat uu____5280 uu____5282

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____5288 =
          let uu____5289 = str "open"  in
          let uu____5291 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5289 uu____5291  in
        FStar_Pprint.group uu____5288
    | FStar_Parser_AST.Include uid ->
        let uu____5293 =
          let uu____5294 = str "include"  in
          let uu____5296 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5294 uu____5296  in
        FStar_Pprint.group uu____5293
    | FStar_Parser_AST.Friend uid ->
        let uu____5298 =
          let uu____5299 = str "friend"  in
          let uu____5301 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5299 uu____5301  in
        FStar_Pprint.group uu____5298
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____5304 =
          let uu____5305 = str "module"  in
          let uu____5307 =
            let uu____5308 =
              let uu____5309 = p_uident uid1  in
              let uu____5310 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5309 uu____5310  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5308  in
          FStar_Pprint.op_Hat_Hat uu____5305 uu____5307  in
        let uu____5311 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____5304 uu____5311
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____5313 =
          let uu____5314 = str "module"  in
          let uu____5316 =
            let uu____5317 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5317  in
          FStar_Pprint.op_Hat_Hat uu____5314 uu____5316  in
        FStar_Pprint.group uu____5313
    | FStar_Parser_AST.Tycon
        (true
         ,uu____5318,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____5355 = str "effect"  in
          let uu____5357 =
            let uu____5358 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5358  in
          FStar_Pprint.op_Hat_Hat uu____5355 uu____5357  in
        let uu____5359 =
          let uu____5360 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____5360 FStar_Pprint.equals
           in
        let uu____5363 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____5359 uu____5363
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____5394 =
          let uu____5395 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____5395  in
        let uu____5408 =
          let uu____5409 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____5447 =
                    let uu____5448 = str "and"  in
                    p_fsdocTypeDeclPairs uu____5448 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____5447)) uu____5409
           in
        FStar_Pprint.op_Hat_Hat uu____5394 uu____5408
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____5465 = str "let"  in
          let uu____5467 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____5465 uu____5467  in
        let uu____5468 = str "and"  in
        separate_map_with_comments_kw let_doc uu____5468 p_letbinding lbs
          (fun uu____5478  ->
             match uu____5478 with
             | (p,t) ->
                 let uu____5485 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____5485;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____5491 =
          let uu____5492 = str "val"  in
          let uu____5494 =
            let uu____5495 =
              let uu____5496 = p_lident lid  in
              let uu____5497 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____5496 uu____5497  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5495  in
          FStar_Pprint.op_Hat_Hat uu____5492 uu____5494  in
        FStar_All.pipe_left FStar_Pprint.group uu____5491
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____5502 =
            let uu____5504 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____5504 FStar_Util.is_upper  in
          if uu____5502
          then FStar_Pprint.empty
          else
            (let uu____5512 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____5512 FStar_Pprint.space)
           in
        let uu____5514 =
          let uu____5515 = p_ident id1  in
          let uu____5516 =
            let uu____5517 =
              let uu____5518 =
                let uu____5519 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5519  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5518  in
            FStar_Pprint.group uu____5517  in
          FStar_Pprint.op_Hat_Hat uu____5515 uu____5516  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____5514
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____5528 = str "exception"  in
        let uu____5530 =
          let uu____5531 =
            let uu____5532 = p_uident uid  in
            let uu____5533 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____5537 =
                     let uu____5538 = str "of"  in
                     let uu____5540 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____5538 uu____5540  in
                   FStar_Pprint.op_Hat_Hat break1 uu____5537) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____5532 uu____5533  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5531  in
        FStar_Pprint.op_Hat_Hat uu____5528 uu____5530
    | FStar_Parser_AST.NewEffect ne ->
        let uu____5544 = str "new_effect"  in
        let uu____5546 =
          let uu____5547 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5547  in
        FStar_Pprint.op_Hat_Hat uu____5544 uu____5546
    | FStar_Parser_AST.SubEffect se ->
        let uu____5549 = str "sub_effect"  in
        let uu____5551 =
          let uu____5552 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5552  in
        FStar_Pprint.op_Hat_Hat uu____5549 uu____5551
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____5555 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____5557,uu____5558) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____5586 = str "%splice"  in
        let uu____5588 =
          let uu____5589 =
            let uu____5590 = str ";"  in p_list p_uident uu____5590 ids  in
          let uu____5592 =
            let uu____5593 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5593  in
          FStar_Pprint.op_Hat_Hat uu____5589 uu____5592  in
        FStar_Pprint.op_Hat_Hat uu____5586 uu____5588

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___115_5596  ->
    match uu___115_5596 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____5599 = str "#set-options"  in
        let uu____5601 =
          let uu____5602 =
            let uu____5603 = str s  in FStar_Pprint.dquotes uu____5603  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5602  in
        FStar_Pprint.op_Hat_Hat uu____5599 uu____5601
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____5608 = str "#reset-options"  in
        let uu____5610 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5616 =
                 let uu____5617 = str s  in FStar_Pprint.dquotes uu____5617
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5616) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5608 uu____5610
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____5622 = str "#push-options"  in
        let uu____5624 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____5630 =
                 let uu____5631 = str s  in FStar_Pprint.dquotes uu____5631
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5630) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5622 uu____5624
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
    fun uu____5662  ->
      match uu____5662 with
      | (typedecl,fsdoc_opt) ->
          let uu____5675 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____5675 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____5700 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____5700
               else
                 (let uu____5703 =
                    let uu____5704 =
                      let uu____5705 =
                        let uu____5706 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5706 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____5705  in
                    let uu____5707 =
                      let uu____5708 =
                        let uu____5709 =
                          let uu____5710 =
                            let uu____5711 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____5711  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____5710
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____5709
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____5708  in
                    FStar_Pprint.ifflat uu____5704 uu____5707  in
                  FStar_All.pipe_left FStar_Pprint.group uu____5703))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___116_5714  ->
      match uu___116_5714 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____5743 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5743, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____5760 = p_typ_sep false false t  in
          (match uu____5760 with
           | (comm,doc1) ->
               let uu____5780 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____5780, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____5836 =
            match uu____5836 with
            | (lid1,t,doc_opt) ->
                let uu____5853 =
                  let uu____5858 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____5858
                   in
                (match uu____5853 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____5876 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____5876  in
          let uu____5885 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____5885, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____5952 =
            match uu____5952 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____5981 =
                    let uu____5982 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____5982  in
                  FStar_Range.extend_to_end_of_line uu____5981  in
                let uu____5987 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____5987 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____6026 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6026, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____6031  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____6031 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____6066 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____6066  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____6068 =
                        let uu____6071 =
                          let uu____6074 = p_fsdoc fsdoc  in
                          let uu____6075 =
                            let uu____6078 = cont lid_doc  in [uu____6078]
                             in
                          uu____6074 :: uu____6075  in
                        kw :: uu____6071  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____6068
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____6085 =
                        let uu____6086 =
                          let uu____6087 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6087 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6086
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6085
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____6107 =
                          let uu____6108 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____6108  in
                        prefix2 uu____6107 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6110  ->
      match uu____6110 with
      | (lid,t,doc_opt) ->
          let uu____6127 =
            let uu____6128 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____6129 =
              let uu____6130 = p_lident lid  in
              let uu____6131 =
                let uu____6132 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6132  in
              FStar_Pprint.op_Hat_Hat uu____6130 uu____6131  in
            FStar_Pprint.op_Hat_Hat uu____6128 uu____6129  in
          FStar_Pprint.group uu____6127

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____6134  ->
    match uu____6134 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____6168 =
            let uu____6169 =
              let uu____6170 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6170  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6169  in
          FStar_Pprint.group uu____6168  in
        let uu____6171 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____6172 =
          default_or_map uid_doc
            (fun t  ->
               let uu____6176 =
                 let uu____6177 =
                   let uu____6178 =
                     let uu____6179 =
                       let uu____6180 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6180
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____6179  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6178  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____6177  in
               FStar_Pprint.group uu____6176) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6171 uu____6172

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6184  ->
      fun inner_let  ->
        match uu____6184 with
        | (pat,uu____6192) ->
            let uu____6193 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____6245 =
                    let uu____6252 =
                      let uu____6257 =
                        let uu____6258 =
                          let uu____6259 =
                            let uu____6260 = str "by"  in
                            let uu____6262 =
                              let uu____6263 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____6263
                               in
                            FStar_Pprint.op_Hat_Hat uu____6260 uu____6262  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____6259
                           in
                        FStar_Pprint.group uu____6258  in
                      (t, uu____6257)  in
                    FStar_Pervasives_Native.Some uu____6252  in
                  (pat1, uu____6245)
              | uu____6274 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____6193 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____6300);
                         FStar_Parser_AST.prange = uu____6301;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6318 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____6318 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6324 =
                        if inner_let
                        then
                          let uu____6338 = pats_as_binders_if_possible pats
                             in
                          match uu____6338 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____6361 = pats_as_binders_if_possible pats
                              in
                           match uu____6361 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____6324 with
                       | (terms,style) ->
                           let uu____6388 =
                             let uu____6389 =
                               let uu____6390 =
                                 let uu____6391 = p_lident lid  in
                                 let uu____6392 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____6391
                                   uu____6392
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6390
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____6389  in
                           FStar_All.pipe_left FStar_Pprint.group uu____6388)
                  | uu____6395 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____6403 =
                              let uu____6404 =
                                let uu____6405 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____6405
                                 in
                              FStar_Pprint.group uu____6404  in
                            FStar_Pprint.op_Hat_Hat uu____6403 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____6416 =
                        let uu____6417 =
                          let uu____6418 =
                            let uu____6419 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____6419  in
                          FStar_Pprint.group uu____6418  in
                        FStar_Pprint.op_Hat_Hat uu____6417 ascr_doc  in
                      FStar_Pprint.group uu____6416))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____6421  ->
      match uu____6421 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____6430 = p_term_sep false false e  in
          (match uu____6430 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____6440 =
                 let uu____6441 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____6441  in
               let uu____6442 =
                 let uu____6443 =
                   let uu____6444 =
                     let uu____6445 =
                       let uu____6446 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____6446
                        in
                     FStar_Pprint.group uu____6445  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6444  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____6443  in
               FStar_Pprint.ifflat uu____6440 uu____6442)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___117_6447  ->
    match uu___117_6447 with
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
        let uu____6472 = p_uident uid  in
        let uu____6473 = p_binders true bs  in
        let uu____6475 =
          let uu____6476 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____6476  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6472 uu____6473 uu____6475

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
          let uu____6491 =
            let uu____6492 =
              let uu____6493 =
                let uu____6494 = p_uident uid  in
                let uu____6495 = p_binders true bs  in
                let uu____6497 =
                  let uu____6498 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____6498  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____6494 uu____6495 uu____6497
                 in
              FStar_Pprint.group uu____6493  in
            let uu____6503 =
              let uu____6504 = str "with"  in
              let uu____6506 =
                let uu____6507 =
                  let uu____6508 =
                    let uu____6509 =
                      let uu____6510 =
                        let uu____6511 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____6511
                         in
                      separate_map_last uu____6510 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6509  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6508  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6507  in
              FStar_Pprint.op_Hat_Hat uu____6504 uu____6506  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6492 uu____6503  in
          braces_with_nesting uu____6491

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____6515,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____6548 =
            let uu____6549 = p_lident lid  in
            let uu____6550 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____6549 uu____6550  in
          let uu____6551 = p_simpleTerm ps false e  in
          prefix2 uu____6548 uu____6551
      | uu____6553 ->
          let uu____6554 =
            let uu____6556 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____6556
             in
          failwith uu____6554

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____6639 =
        match uu____6639 with
        | (kwd,t) ->
            let uu____6650 =
              let uu____6651 = str kwd  in
              let uu____6652 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6651 uu____6652  in
            let uu____6653 = p_simpleTerm ps false t  in
            prefix2 uu____6650 uu____6653
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____6660 =
      let uu____6661 =
        let uu____6662 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____6663 =
          let uu____6664 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6664  in
        FStar_Pprint.op_Hat_Hat uu____6662 uu____6663  in
      let uu____6666 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____6661 uu____6666  in
    let uu____6667 =
      let uu____6668 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6668  in
    FStar_Pprint.op_Hat_Hat uu____6660 uu____6667

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___118_6669  ->
    match uu___118_6669 with
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
        let uu____6689 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____6689 FStar_Pprint.hardline
    | uu____6690 ->
        let uu____6691 =
          let uu____6692 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____6692  in
        FStar_Pprint.op_Hat_Hat uu____6691 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___119_6695  ->
    match uu___119_6695 with
    | FStar_Parser_AST.Rec  ->
        let uu____6696 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6696
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___120_6698  ->
    match uu___120_6698 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____6702,e) ->
             let uu____6708 = str "#["  in
             let uu____6710 =
               let uu____6711 = p_term false false e  in
               let uu____6714 =
                 let uu____6715 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____6715 break1  in
               FStar_Pprint.op_Hat_Hat uu____6711 uu____6714  in
             FStar_Pprint.op_Hat_Hat uu____6708 uu____6710
         | uu____6717 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____6723 =
          let uu____6724 =
            let uu____6725 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____6725  in
          FStar_Pprint.separate_map uu____6724 p_tuplePattern pats  in
        FStar_Pprint.group uu____6723
    | uu____6726 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____6735 =
          let uu____6736 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____6736 p_constructorPattern pats  in
        FStar_Pprint.group uu____6735
    | uu____6737 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____6740;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____6745 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____6746 = p_constructorPattern hd1  in
        let uu____6747 = p_constructorPattern tl1  in
        infix0 uu____6745 uu____6746 uu____6747
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____6749;_},pats)
        ->
        let uu____6755 = p_quident uid  in
        let uu____6756 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____6755 uu____6756
    | uu____6757 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____6773;
               FStar_Parser_AST.blevel = uu____6774;
               FStar_Parser_AST.aqual = uu____6775;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____6784 =
               let uu____6785 = p_ident lid  in
               p_refinement aqual uu____6785 t1 phi  in
             soft_parens_with_nesting uu____6784
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____6788;
               FStar_Parser_AST.blevel = uu____6789;
               FStar_Parser_AST.aqual = uu____6790;_},phi))
             ->
             let uu____6796 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____6796
         | uu____6797 ->
             let uu____6802 =
               let uu____6803 = p_tuplePattern pat  in
               let uu____6804 =
                 let uu____6805 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6805
                  in
               FStar_Pprint.op_Hat_Hat uu____6803 uu____6804  in
             soft_parens_with_nesting uu____6802)
    | FStar_Parser_AST.PatList pats ->
        let uu____6809 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6809 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____6828 =
          match uu____6828 with
          | (lid,pat) ->
              let uu____6835 = p_qlident lid  in
              let uu____6836 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____6835 uu____6836
           in
        let uu____6837 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____6837
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____6849 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6850 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____6851 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6849 uu____6850 uu____6851
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____6862 =
          let uu____6863 =
            let uu____6864 =
              let uu____6865 = FStar_Ident.text_of_id op  in str uu____6865
               in
            let uu____6867 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6864 uu____6867  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6863  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6862
    | FStar_Parser_AST.PatWild aqual ->
        let uu____6871 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____6871 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____6879 = FStar_Pprint.optional p_aqual aqual  in
        let uu____6880 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____6879 uu____6880
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____6882 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____6886;
           FStar_Parser_AST.prange = uu____6887;_},uu____6888)
        ->
        let uu____6893 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6893
    | FStar_Parser_AST.PatTuple (uu____6894,false ) ->
        let uu____6901 = p_tuplePattern p  in
        soft_parens_with_nesting uu____6901
    | uu____6902 ->
        let uu____6903 =
          let uu____6905 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____6905  in
        failwith uu____6903

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____6910;_},uu____6911)
        -> true
    | uu____6918 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____6924) -> true
    | uu____6926 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____6933 = p_binder' is_atomic b  in
      match uu____6933 with
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
          let uu____6972 =
            let uu____6973 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____6974 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____6973 uu____6974  in
          (uu____6972, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____6980 = p_lident lid  in
          (uu____6980, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6987 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____6998;
                   FStar_Parser_AST.blevel = uu____6999;
                   FStar_Parser_AST.aqual = uu____7000;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____7005 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____7005 t1 phi
            | uu____7006 ->
                let t' =
                  let uu____7008 = is_typ_tuple t  in
                  if uu____7008
                  then
                    let uu____7011 = p_tmFormula t  in
                    soft_parens_with_nesting uu____7011
                  else p_tmFormula t  in
                let uu____7014 =
                  let uu____7015 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____7016 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____7015 uu____7016  in
                (uu____7014, t')
             in
          (match uu____6987 with
           | (b',t') ->
               let catf =
                 let uu____7034 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____7034
                 then
                   fun x  ->
                     fun y  ->
                       let uu____7041 =
                         let uu____7042 =
                           let uu____7043 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____7043
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____7042
                          in
                       FStar_Pprint.group uu____7041
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____7048 = cat_with_colon x y  in
                        FStar_Pprint.group uu____7048)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____7057 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____7085;
                  FStar_Parser_AST.blevel = uu____7086;
                  FStar_Parser_AST.aqual = uu____7087;_},phi)
               ->
               let uu____7091 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____7091 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____7112 ->
               if is_atomic
               then
                 let uu____7124 = p_atomicTerm t  in
                 (uu____7124, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____7131 = p_appTerm t  in
                  (uu____7131, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____7142 = p_refinement' aqual_opt binder t phi  in
          match uu____7142 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____7158 -> false
            | FStar_Parser_AST.App uu____7170 -> false
            | FStar_Parser_AST.Op uu____7178 -> false
            | uu____7186 -> true  in
          let uu____7188 = p_noSeqTerm false false phi  in
          match uu____7188 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____7205 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____7205)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____7214 =
                let uu____7215 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____7215 binder  in
              let uu____7216 =
                let uu____7217 = p_appTerm t  in
                let uu____7218 =
                  let uu____7219 =
                    let uu____7220 =
                      let uu____7221 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____7222 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____7221 uu____7222  in
                    FStar_Pprint.group uu____7220  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____7219
                   in
                FStar_Pprint.op_Hat_Hat uu____7217 uu____7218  in
              (uu____7214, uu____7216)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____7236 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____7236

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____7240 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7243 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7243)
       in
    if uu____7240
    then FStar_Pprint.underscore
    else (let uu____7248 = FStar_Ident.text_of_id lid  in str uu____7248)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____7251 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____7254 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____7254)
       in
    if uu____7251
    then FStar_Pprint.underscore
    else (let uu____7259 = FStar_Ident.text_of_lid lid  in str uu____7259)

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
          let uu____7280 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____7280
        else
          (let uu____7283 =
             let uu____7284 =
               let uu____7285 =
                 let uu____7286 =
                   let uu____7287 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____7287  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____7286  in
               FStar_Pprint.group uu____7285  in
             let uu____7288 =
               let uu____7289 =
                 let uu____7290 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7290  in
               FStar_Pprint.op_Hat_Hat comm uu____7289  in
             FStar_Pprint.ifflat uu____7284 uu____7288  in
           FStar_All.pipe_left FStar_Pprint.group uu____7283)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____7298 = p_noSeqTerm true false e1  in
            (match uu____7298 with
             | (comm,t1) ->
                 let uu____7307 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____7308 =
                   let uu____7309 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7309
                    in
                 FStar_Pprint.op_Hat_Hat uu____7307 uu____7308)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7313 =
              let uu____7314 =
                let uu____7315 =
                  let uu____7316 = p_lident x  in
                  let uu____7317 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____7316 uu____7317  in
                let uu____7318 =
                  let uu____7319 = p_noSeqTermAndComment true false e1  in
                  let uu____7322 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____7319 uu____7322  in
                op_Hat_Slash_Plus_Hat uu____7315 uu____7318  in
              FStar_Pprint.group uu____7314  in
            let uu____7323 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7313 uu____7323
        | uu____7324 ->
            let uu____7325 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____7325

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
            let uu____7337 = p_noSeqTerm true false e1  in
            (match uu____7337 with
             | (comm,t1) ->
                 let uu____7350 =
                   let uu____7351 =
                     let uu____7352 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____7352  in
                   let uu____7353 =
                     let uu____7354 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7354
                      in
                   FStar_Pprint.op_Hat_Hat uu____7351 uu____7353  in
                 (comm, uu____7350))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____7358 =
              let uu____7359 =
                let uu____7360 =
                  let uu____7361 =
                    let uu____7362 = p_lident x  in
                    let uu____7363 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____7362 uu____7363  in
                  let uu____7364 =
                    let uu____7365 = p_noSeqTermAndComment true false e1  in
                    let uu____7368 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____7365 uu____7368  in
                  op_Hat_Slash_Plus_Hat uu____7361 uu____7364  in
                FStar_Pprint.group uu____7360  in
              let uu____7369 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7359 uu____7369  in
            (FStar_Pprint.empty, uu____7358)
        | uu____7370 -> p_noSeqTerm ps pb e

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
            let uu____7390 =
              let uu____7391 = p_tmIff e1  in
              let uu____7392 =
                let uu____7393 =
                  let uu____7394 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7394
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7393  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7391 uu____7392  in
            FStar_Pprint.group uu____7390
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____7400 =
              let uu____7401 = p_tmIff e1  in
              let uu____7402 =
                let uu____7403 =
                  let uu____7404 =
                    let uu____7405 = p_typ false false t  in
                    let uu____7408 =
                      let uu____7409 = str "by"  in
                      let uu____7411 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____7409 uu____7411  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____7405 uu____7408  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____7404
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____7403  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7401 uu____7402  in
            FStar_Pprint.group uu____7400
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____7412;_},e1::e2::e3::[])
            ->
            let uu____7419 =
              let uu____7420 =
                let uu____7421 =
                  let uu____7422 = p_atomicTermNotQUident e1  in
                  let uu____7423 =
                    let uu____7424 =
                      let uu____7425 =
                        let uu____7426 = p_term false false e2  in
                        soft_parens_with_nesting uu____7426  in
                      let uu____7429 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7425 uu____7429  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7424  in
                  FStar_Pprint.op_Hat_Hat uu____7422 uu____7423  in
                FStar_Pprint.group uu____7421  in
              let uu____7430 =
                let uu____7431 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7431  in
              FStar_Pprint.op_Hat_Hat uu____7420 uu____7430  in
            FStar_Pprint.group uu____7419
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____7432;_},e1::e2::e3::[])
            ->
            let uu____7439 =
              let uu____7440 =
                let uu____7441 =
                  let uu____7442 = p_atomicTermNotQUident e1  in
                  let uu____7443 =
                    let uu____7444 =
                      let uu____7445 =
                        let uu____7446 = p_term false false e2  in
                        soft_brackets_with_nesting uu____7446  in
                      let uu____7449 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____7445 uu____7449  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7444  in
                  FStar_Pprint.op_Hat_Hat uu____7442 uu____7443  in
                FStar_Pprint.group uu____7441  in
              let uu____7450 =
                let uu____7451 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____7451  in
              FStar_Pprint.op_Hat_Hat uu____7440 uu____7450  in
            FStar_Pprint.group uu____7439
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____7461 =
              let uu____7462 = str "requires"  in
              let uu____7464 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7462 uu____7464  in
            FStar_Pprint.group uu____7461
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____7474 =
              let uu____7475 = str "ensures"  in
              let uu____7477 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7475 uu____7477  in
            FStar_Pprint.group uu____7474
        | FStar_Parser_AST.Attributes es ->
            let uu____7481 =
              let uu____7482 = str "attributes"  in
              let uu____7484 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7482 uu____7484  in
            FStar_Pprint.group uu____7481
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____7489 =
                let uu____7490 =
                  let uu____7491 = str "if"  in
                  let uu____7493 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____7491 uu____7493  in
                let uu____7496 =
                  let uu____7497 = str "then"  in
                  let uu____7499 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____7497 uu____7499  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7490 uu____7496  in
              FStar_Pprint.group uu____7489
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____7503,uu____7504,e31) when
                     is_unit e31 ->
                     let uu____7506 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____7506
                 | uu____7509 -> p_noSeqTermAndComment false false e2  in
               let uu____7512 =
                 let uu____7513 =
                   let uu____7514 = str "if"  in
                   let uu____7516 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____7514 uu____7516  in
                 let uu____7519 =
                   let uu____7520 =
                     let uu____7521 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____7521 e2_doc  in
                   let uu____7523 =
                     let uu____7524 = str "else"  in
                     let uu____7526 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____7524 uu____7526  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____7520 uu____7523  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____7513 uu____7519  in
               FStar_Pprint.group uu____7512)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____7549 =
              let uu____7550 =
                let uu____7551 =
                  let uu____7552 = str "try"  in
                  let uu____7554 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____7552 uu____7554  in
                let uu____7557 =
                  let uu____7558 = str "with"  in
                  let uu____7560 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____7558 uu____7560  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7551 uu____7557  in
              FStar_Pprint.group uu____7550  in
            let uu____7569 = paren_if (ps || pb)  in uu____7569 uu____7549
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____7596 =
              let uu____7597 =
                let uu____7598 =
                  let uu____7599 = str "match"  in
                  let uu____7601 = p_noSeqTermAndComment false false e1  in
                  let uu____7604 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7599 uu____7601 uu____7604
                   in
                let uu____7608 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7598 uu____7608  in
              FStar_Pprint.group uu____7597  in
            let uu____7617 = paren_if (ps || pb)  in uu____7617 uu____7596
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____7624 =
              let uu____7625 =
                let uu____7626 =
                  let uu____7627 = str "let open"  in
                  let uu____7629 = p_quident uid  in
                  let uu____7630 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____7627 uu____7629 uu____7630
                   in
                let uu____7634 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____7626 uu____7634  in
              FStar_Pprint.group uu____7625  in
            let uu____7636 = paren_if ps  in uu____7636 uu____7624
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____7701 is_last =
              match uu____7701 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____7735 =
                          let uu____7736 = str "let"  in
                          let uu____7738 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7736 uu____7738
                           in
                        FStar_Pprint.group uu____7735
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____7741 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____7747 = p_term_sep false false e2  in
                  (match uu____7747 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____7757 =
                         if is_last
                         then
                           let uu____7759 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____7760 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____7759 doc_expr1
                             uu____7760
                         else
                           (let uu____7766 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____7766)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____7757)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____7817 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____7817
                     else
                       (let uu____7828 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____7828)) lbs
               in
            let lbs_doc =
              let uu____7838 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____7838  in
            let uu____7839 =
              let uu____7840 =
                let uu____7841 =
                  let uu____7842 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____7842
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____7841  in
              FStar_Pprint.group uu____7840  in
            let uu____7844 = paren_if ps  in uu____7844 uu____7839
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____7851;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____7854;
                                                             FStar_Parser_AST.level
                                                               = uu____7855;_})
            when matches_var maybe_x x ->
            let uu____7882 =
              let uu____7883 =
                let uu____7884 = str "function"  in
                let uu____7886 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____7884 uu____7886  in
              FStar_Pprint.group uu____7883  in
            let uu____7895 = paren_if (ps || pb)  in uu____7895 uu____7882
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____7901 =
              let uu____7902 = str "quote"  in
              let uu____7904 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____7902 uu____7904  in
            FStar_Pprint.group uu____7901
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____7906 =
              let uu____7907 = str "`"  in
              let uu____7909 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7907 uu____7909  in
            FStar_Pprint.group uu____7906
        | FStar_Parser_AST.VQuote e1 ->
            let uu____7911 =
              let uu____7912 = str "`%"  in
              let uu____7914 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7912 uu____7914  in
            FStar_Pprint.group uu____7911
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____7916;
              FStar_Parser_AST.level = uu____7917;_}
            ->
            let uu____7918 =
              let uu____7919 = str "`@"  in
              let uu____7921 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7919 uu____7921  in
            FStar_Pprint.group uu____7918
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____7923 =
              let uu____7924 = str "`#"  in
              let uu____7926 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____7924 uu____7926  in
            FStar_Pprint.group uu____7923
        | uu____7927 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___121_7928  ->
    match uu___121_7928 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____7940 =
          let uu____7941 = str "[@"  in
          let uu____7943 =
            let uu____7944 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____7945 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____7944 uu____7945  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7941 uu____7943  in
        FStar_Pprint.group uu____7940

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
                 let uu____7982 =
                   let uu____7983 =
                     let uu____7984 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____7984 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____7983 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____7982 term_doc
             | pats ->
                 let uu____7992 =
                   let uu____7993 =
                     let uu____7994 =
                       let uu____7995 =
                         let uu____7996 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____7996
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____7995 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____7999 = p_trigger trigger  in
                     prefix2 uu____7994 uu____7999  in
                   FStar_Pprint.group uu____7993  in
                 prefix2 uu____7992 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____8020 =
                   let uu____8021 =
                     let uu____8022 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____8022 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____8021 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____8020 term_doc
             | pats ->
                 let uu____8030 =
                   let uu____8031 =
                     let uu____8032 =
                       let uu____8033 =
                         let uu____8034 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____8034
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____8033 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____8037 = p_trigger trigger  in
                     prefix2 uu____8032 uu____8037  in
                   FStar_Pprint.group uu____8031  in
                 prefix2 uu____8030 term_doc)
        | uu____8038 -> p_simpleTerm ps pb e

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
      let uu____8059 = all_binders_annot t  in
      if uu____8059
      then
        let uu____8062 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____8062
      else
        (let uu____8073 =
           let uu____8074 =
             let uu____8075 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____8075  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8074  in
         FStar_Pprint.group uu____8073)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____8134 = x  in
      match uu____8134 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____8199 = hd1  in
               (match uu____8199 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____8271 = cb  in
      match uu____8271 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____8290 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____8296 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____8296) hd1 tl1
                  in
               cat_with_colon uu____8290 typ)
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
                 FStar_Parser_AST.brange = uu____8375;
                 FStar_Parser_AST.blevel = uu____8376;
                 FStar_Parser_AST.aqual = uu____8377;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____8386 =
                 let uu____8391 = p_ident lid  in
                 p_refinement' aqual uu____8391 t1 phi  in
               FStar_Pervasives_Native.Some uu____8386
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____8398) ->
               let uu____8403 =
                 let uu____8408 =
                   let uu____8409 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____8410 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____8409 uu____8410  in
                 let uu____8411 = p_tmEqNoRefinement t  in
                 (uu____8408, uu____8411)  in
               FStar_Pervasives_Native.Some uu____8403
           | uu____8416 -> FStar_Pervasives_Native.None)
      | uu____8425 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____8438 -> false
      | uu____8450 -> true  in
    let uu____8452 = map_if_all all_binders pats  in
    match uu____8452 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____8484 = collapse_pats bs  in
        (uu____8484,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____8501 = FStar_List.map p_atomicPattern pats  in
        (uu____8501,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____8513 -> str "forall"
    | FStar_Parser_AST.QExists uu____8527 -> str "exists"
    | uu____8541 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___122_8543  ->
    match uu___122_8543 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____8555 =
          let uu____8556 =
            let uu____8557 =
              let uu____8558 = str "pattern"  in
              let uu____8560 =
                let uu____8561 =
                  let uu____8562 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____8562
                   in
                FStar_Pprint.op_Hat_Hat uu____8561 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____8558 uu____8560  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____8557  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____8556  in
        FStar_Pprint.group uu____8555

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8570 = str "\\/"  in
    FStar_Pprint.separate_map uu____8570 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____8577 =
      let uu____8578 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____8578 p_appTerm pats  in
    FStar_Pprint.group uu____8577

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____8590 = p_term_sep false pb e1  in
            (match uu____8590 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____8599 = str "fun"  in
                   let uu____8601 =
                     let uu____8602 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____8602
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____8599 uu____8601  in
                 let uu____8603 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____8605 =
                       let uu____8606 =
                         let uu____8607 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____8607  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____8606
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____8605
                   else
                     (let uu____8610 = op_Hat_Slash_Plus_Hat prefix1 doc1  in
                      FStar_Pprint.group uu____8610)
                    in
                 let uu____8611 = paren_if ps  in uu____8611 uu____8603)
        | uu____8616 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____8624  ->
      match uu____8624 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____8648 =
                    let uu____8649 =
                      let uu____8650 =
                        let uu____8651 = p_tuplePattern p  in
                        let uu____8652 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____8651 uu____8652  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8650
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8649  in
                  FStar_Pprint.group uu____8648
              | FStar_Pervasives_Native.Some f ->
                  let uu____8654 =
                    let uu____8655 =
                      let uu____8656 =
                        let uu____8657 =
                          let uu____8658 =
                            let uu____8659 = p_tuplePattern p  in
                            let uu____8660 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____8659
                              uu____8660
                             in
                          FStar_Pprint.group uu____8658  in
                        let uu____8662 =
                          let uu____8663 =
                            let uu____8666 = p_tmFormula f  in
                            [uu____8666; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____8663  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____8657 uu____8662
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8656
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8655  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____8654
               in
            let uu____8668 = p_term_sep false pb e  in
            match uu____8668 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____8678 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____8678
                   else
                     (let uu____8681 =
                        let uu____8682 =
                          let uu____8683 =
                            let uu____8684 =
                              let uu____8685 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____8685  in
                            op_Hat_Slash_Plus_Hat branch uu____8684  in
                          FStar_Pprint.group uu____8683  in
                        let uu____8686 =
                          let uu____8687 =
                            let uu____8688 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____8688  in
                          FStar_Pprint.op_Hat_Hat branch uu____8687  in
                        FStar_Pprint.ifflat uu____8682 uu____8686  in
                      FStar_Pprint.group uu____8681))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____8692 =
                       let uu____8693 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____8693  in
                     op_Hat_Slash_Plus_Hat branch uu____8692)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____8704 =
                      let uu____8705 =
                        let uu____8706 =
                          let uu____8707 =
                            let uu____8708 =
                              let uu____8709 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____8709  in
                            FStar_Pprint.separate_map uu____8708
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____8707
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8706
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____8705  in
                    FStar_Pprint.group uu____8704
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____8711 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____8713;_},e1::e2::[])
        ->
        let uu____8719 = str "<==>"  in
        let uu____8721 = p_tmImplies e1  in
        let uu____8722 = p_tmIff e2  in
        infix0 uu____8719 uu____8721 uu____8722
    | uu____8723 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____8725;_},e1::e2::[])
        ->
        let uu____8731 = str "==>"  in
        let uu____8733 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____8739 = p_tmImplies e2  in
        infix0 uu____8731 uu____8733 uu____8739
    | uu____8740 ->
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
          let uu____8754 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____8754 with
          | (terms',last1) ->
              let uu____8774 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____8809 =
                      let uu____8810 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8810
                       in
                    let uu____8811 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____8809, uu____8811)
                | Binders (n1,ln,parens1) ->
                    let uu____8825 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____8833 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____8825, break1, uu____8833)
                 in
              (match uu____8774 with
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
                    | uu____8866 ->
                        let uu____8867 =
                          let uu____8868 =
                            let uu____8869 =
                              let uu____8870 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____8871 =
                                let uu____8872 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____8872
                                 in
                              FStar_Pprint.op_Hat_Hat uu____8870 uu____8871
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____8869  in
                          let uu____8873 =
                            let uu____8874 =
                              let uu____8875 =
                                let uu____8876 =
                                  let uu____8877 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____8877  in
                                let uu____8878 =
                                  let uu____8879 =
                                    let uu____8880 =
                                      let uu____8881 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____8882 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____8888 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____8888)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____8881
                                        uu____8882
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____8880
                                     in
                                  jump2 uu____8879  in
                                FStar_Pprint.ifflat uu____8876 uu____8878  in
                              FStar_Pprint.group uu____8875  in
                            let uu____8890 =
                              let uu____8891 =
                                let uu____8892 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____8892  in
                              FStar_Pprint.align uu____8891  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____8874 uu____8890
                             in
                          FStar_Pprint.ifflat uu____8868 uu____8873  in
                        FStar_Pprint.group uu____8867))

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
            | Arrows uu____8906 -> p_tmArrow' p_Tm e
            | Binders uu____8913 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____8936 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____8942 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____8936 uu____8942
      | uu____8945 -> let uu____8946 = p_Tm e  in [uu____8946]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____8999 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____9025 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____8999 uu____9025
        | uu____9048 ->
            let uu____9049 =
              let uu____9060 = p_Tm1 e1  in
              (uu____9060, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____9049]
         in
      let fold_fun bs x =
        let uu____9158 = x  in
        match uu____9158 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____9294 = hd1  in
                 (match uu____9294 with
                  | (b2s,t2,uu____9323) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____9433 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____9494 = cb  in
        match uu____9494 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____9523 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____9536 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____9542 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____9542) hd1 tl1
                         in
                      f uu____9536 typ))
         in
      let binders =
        let uu____9560 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____9560  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____9623 =
        let uu____9624 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____9624 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9623  in
    let disj =
      let uu____9627 =
        let uu____9628 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____9628 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9627  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____9648;_},e1::e2::[])
        ->
        let uu____9654 = p_tmDisjunction e1  in
        let uu____9659 = let uu____9664 = p_tmConjunction e2  in [uu____9664]
           in
        FStar_List.append uu____9654 uu____9659
    | uu____9673 -> let uu____9674 = p_tmConjunction e  in [uu____9674]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____9684;_},e1::e2::[])
        ->
        let uu____9690 = p_tmConjunction e1  in
        let uu____9693 = let uu____9696 = p_tmTuple e2  in [uu____9696]  in
        FStar_List.append uu____9690 uu____9693
    | uu____9697 -> let uu____9698 = p_tmTuple e  in [uu____9698]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____9715 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____9715
          (fun uu____9723  ->
             match uu____9723 with | (e1,uu____9729) -> p_tmEq e1) args
    | uu____9730 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____9739 =
             let uu____9740 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____9740  in
           FStar_Pprint.group uu____9739)

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
               (let uu____9759 = FStar_Ident.text_of_id op  in
                uu____9759 = "="))
              ||
              (let uu____9764 = FStar_Ident.text_of_id op  in
               uu____9764 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____9770 = levels op1  in
            (match uu____9770 with
             | (left1,mine,right1) ->
                 let uu____9789 =
                   let uu____9790 = FStar_All.pipe_left str op1  in
                   let uu____9792 = p_tmEqWith' p_X left1 e1  in
                   let uu____9793 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____9790 uu____9792 uu____9793  in
                 paren_if_gt curr mine uu____9789)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____9794;_},e1::e2::[])
            ->
            let uu____9800 =
              let uu____9801 = p_tmEqWith p_X e1  in
              let uu____9802 =
                let uu____9803 =
                  let uu____9804 =
                    let uu____9805 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____9805  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____9804  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____9803  in
              FStar_Pprint.op_Hat_Hat uu____9801 uu____9802  in
            FStar_Pprint.group uu____9800
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____9806;_},e1::[])
            ->
            let uu____9811 = levels "-"  in
            (match uu____9811 with
             | (left1,mine,right1) ->
                 let uu____9831 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____9831)
        | uu____9832 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____9880)::(e2,uu____9882)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____9902 = is_list e  in Prims.op_Negation uu____9902)
              ->
              let op = "::"  in
              let uu____9907 = levels op  in
              (match uu____9907 with
               | (left1,mine,right1) ->
                   let uu____9926 =
                     let uu____9927 = str op  in
                     let uu____9928 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____9930 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____9927 uu____9928 uu____9930  in
                   paren_if_gt curr mine uu____9926)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____9949 = levels op  in
              (match uu____9949 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____9983 = p_binder false b  in
                         let uu____9985 =
                           let uu____9986 =
                             let uu____9987 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9987 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9986
                            in
                         FStar_Pprint.op_Hat_Hat uu____9983 uu____9985
                     | FStar_Util.Inr t ->
                         let uu____9989 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____9991 =
                           let uu____9992 =
                             let uu____9993 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____9993 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____9992
                            in
                         FStar_Pprint.op_Hat_Hat uu____9989 uu____9991
                      in
                   let uu____9994 =
                     let uu____9995 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____10000 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____9995 uu____10000  in
                   paren_if_gt curr mine uu____9994)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____10002;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____10032 = levels op  in
              (match uu____10032 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____10052 = str op  in
                     let uu____10053 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____10055 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____10052 uu____10053 uu____10055
                   else
                     (let uu____10059 =
                        let uu____10060 = str op  in
                        let uu____10061 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____10063 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____10060 uu____10061 uu____10063  in
                      paren_if_gt curr mine uu____10059))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____10072 = levels op1  in
              (match uu____10072 with
               | (left1,mine,right1) ->
                   let uu____10091 =
                     let uu____10092 = str op1  in
                     let uu____10093 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____10095 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____10092 uu____10093 uu____10095  in
                   paren_if_gt curr mine uu____10091)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____10115 =
                let uu____10116 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____10117 =
                  let uu____10118 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____10118 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____10116 uu____10117  in
              braces_with_nesting uu____10115
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____10123;_},e1::[])
              ->
              let uu____10128 =
                let uu____10129 = str "~"  in
                let uu____10131 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____10129 uu____10131  in
              FStar_Pprint.group uu____10128
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____10133;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____10142 = levels op  in
                   (match uu____10142 with
                    | (left1,mine,right1) ->
                        let uu____10161 =
                          let uu____10162 = str op  in
                          let uu____10163 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____10165 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____10162 uu____10163 uu____10165  in
                        paren_if_gt curr mine uu____10161)
               | uu____10167 -> p_X e)
          | uu____10168 -> p_X e

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
        let uu____10175 =
          let uu____10176 = p_lident lid  in
          let uu____10177 =
            let uu____10178 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____10178  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10176 uu____10177  in
        FStar_Pprint.group uu____10175
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____10181 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____10183 = p_appTerm e  in
    let uu____10184 =
      let uu____10185 =
        let uu____10186 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____10186 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10185  in
    FStar_Pprint.op_Hat_Hat uu____10183 uu____10184

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____10192 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____10192 t phi
      | FStar_Parser_AST.TAnnotated uu____10193 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____10199 ->
          let uu____10200 =
            let uu____10202 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10202
             in
          failwith uu____10200
      | FStar_Parser_AST.TVariable uu____10205 ->
          let uu____10206 =
            let uu____10208 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10208
             in
          failwith uu____10206
      | FStar_Parser_AST.NoName uu____10211 ->
          let uu____10212 =
            let uu____10214 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____10214
             in
          failwith uu____10212

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____10218  ->
      match uu____10218 with
      | (lid,e) ->
          let uu____10226 =
            let uu____10227 = p_qlident lid  in
            let uu____10228 =
              let uu____10229 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____10229
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____10227 uu____10228  in
          FStar_Pprint.group uu____10226

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____10232 when is_general_application e ->
        let uu____10239 = head_and_args e  in
        (match uu____10239 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____10286 = p_argTerm e1  in
                  let uu____10287 =
                    let uu____10288 =
                      let uu____10289 =
                        let uu____10290 = str "`"  in
                        let uu____10292 =
                          let uu____10293 = p_indexingTerm head1  in
                          let uu____10294 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____10293 uu____10294  in
                        FStar_Pprint.op_Hat_Hat uu____10290 uu____10292  in
                      FStar_Pprint.group uu____10289  in
                    let uu____10296 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____10288 uu____10296  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____10286 uu____10287
              | uu____10297 ->
                  let uu____10304 =
                    let uu____10315 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____10315
                    then
                      let uu____10349 =
                        FStar_Util.take
                          (fun uu____10373  ->
                             match uu____10373 with
                             | (uu____10379,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____10349 with
                      | (fs_typ_args,args1) ->
                          let uu____10417 =
                            let uu____10418 = p_indexingTerm head1  in
                            let uu____10419 =
                              let uu____10420 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____10420
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____10418 uu____10419
                             in
                          (uu____10417, args1)
                    else
                      (let uu____10435 = p_indexingTerm head1  in
                       (uu____10435, args))
                     in
                  (match uu____10304 with
                   | (head_doc,args1) ->
                       let uu____10456 =
                         let uu____10457 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____10457 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____10456)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____10479 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____10479)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____10498 =
               let uu____10499 = p_quident lid  in
               let uu____10500 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____10499 uu____10500  in
             FStar_Pprint.group uu____10498
         | hd1::tl1 ->
             let uu____10517 =
               let uu____10518 =
                 let uu____10519 =
                   let uu____10520 = p_quident lid  in
                   let uu____10521 = p_argTerm hd1  in
                   prefix2 uu____10520 uu____10521  in
                 FStar_Pprint.group uu____10519  in
               let uu____10522 =
                 let uu____10523 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____10523  in
               FStar_Pprint.op_Hat_Hat uu____10518 uu____10522  in
             FStar_Pprint.group uu____10517)
    | uu____10528 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____10539 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____10539 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____10543 = str "#"  in
        let uu____10545 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____10543 uu____10545
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____10548 = str "#["  in
        let uu____10550 =
          let uu____10551 = p_indexingTerm t  in
          let uu____10552 =
            let uu____10553 = str "]"  in
            let uu____10555 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____10553 uu____10555  in
          FStar_Pprint.op_Hat_Hat uu____10551 uu____10552  in
        FStar_Pprint.op_Hat_Hat uu____10548 uu____10550
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____10558  ->
    match uu____10558 with | (e,uu____10564) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____10569;_},e1::e2::[])
          ->
          let uu____10575 =
            let uu____10576 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10577 =
              let uu____10578 =
                let uu____10579 = p_term false false e2  in
                soft_parens_with_nesting uu____10579  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10578  in
            FStar_Pprint.op_Hat_Hat uu____10576 uu____10577  in
          FStar_Pprint.group uu____10575
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____10582;_},e1::e2::[])
          ->
          let uu____10588 =
            let uu____10589 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____10590 =
              let uu____10591 =
                let uu____10592 = p_term false false e2  in
                soft_brackets_with_nesting uu____10592  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10591  in
            FStar_Pprint.op_Hat_Hat uu____10589 uu____10590  in
          FStar_Pprint.group uu____10588
      | uu____10595 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____10600 = p_quident lid  in
        let uu____10601 =
          let uu____10602 =
            let uu____10603 = p_term false false e1  in
            soft_parens_with_nesting uu____10603  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10602  in
        FStar_Pprint.op_Hat_Hat uu____10600 uu____10601
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10611 =
          let uu____10612 = FStar_Ident.text_of_id op  in str uu____10612  in
        let uu____10614 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____10611 uu____10614
    | uu____10615 -> p_atomicTermNotQUident e

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
         | uu____10628 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____10637 =
          let uu____10638 = FStar_Ident.text_of_id op  in str uu____10638  in
        let uu____10640 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____10637 uu____10640
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____10644 =
          let uu____10645 =
            let uu____10646 =
              let uu____10647 = FStar_Ident.text_of_id op  in str uu____10647
               in
            let uu____10649 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____10646 uu____10649  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10645  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____10644
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____10664 = all_explicit args  in
        if uu____10664
        then
          let uu____10667 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____10668 =
            let uu____10669 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____10670 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____10669 p_tmEq uu____10670  in
          let uu____10677 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____10667 uu____10668 uu____10677
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____10699 =
                 let uu____10700 = p_quident lid  in
                 let uu____10701 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____10700 uu____10701  in
               FStar_Pprint.group uu____10699
           | hd1::tl1 ->
               let uu____10718 =
                 let uu____10719 =
                   let uu____10720 =
                     let uu____10721 = p_quident lid  in
                     let uu____10722 = p_argTerm hd1  in
                     prefix2 uu____10721 uu____10722  in
                   FStar_Pprint.group uu____10720  in
                 let uu____10723 =
                   let uu____10724 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____10724  in
                 FStar_Pprint.op_Hat_Hat uu____10719 uu____10723  in
               FStar_Pprint.group uu____10718)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____10731 =
          let uu____10732 = p_atomicTermNotQUident e1  in
          let uu____10733 =
            let uu____10734 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10734  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____10732 uu____10733
           in
        FStar_Pprint.group uu____10731
    | uu____10737 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____10742 = p_quident constr_lid  in
        let uu____10743 =
          let uu____10744 =
            let uu____10745 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____10745  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____10744  in
        FStar_Pprint.op_Hat_Hat uu____10742 uu____10743
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____10747 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____10747 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____10749 = p_term_sep false false e1  in
        (match uu____10749 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____10762 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____10762))
    | uu____10763 when is_array e ->
        let es = extract_from_list e  in
        let uu____10767 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____10768 =
          let uu____10769 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____10769
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____10774 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10767 uu____10768 uu____10774
    | uu____10777 when is_list e ->
        let uu____10778 =
          let uu____10779 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10780 = extract_from_list e  in
          separate_map_or_flow_last uu____10779
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10780
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____10778 FStar_Pprint.rbracket
    | uu____10789 when is_lex_list e ->
        let uu____10790 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____10791 =
          let uu____10792 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____10793 = extract_from_list e  in
          separate_map_or_flow_last uu____10792
            (fun ps  -> p_noSeqTermAndComment ps false) uu____10793
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____10790 uu____10791 FStar_Pprint.rbracket
    | uu____10802 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____10806 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____10807 =
          let uu____10808 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____10808 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____10806 uu____10807 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____10818 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____10821 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____10818 uu____10821
    | FStar_Parser_AST.Op (op,args) when
        let uu____10830 = handleable_op op args  in
        Prims.op_Negation uu____10830 ->
        let uu____10832 =
          let uu____10834 =
            let uu____10836 = FStar_Ident.text_of_id op  in
            let uu____10838 =
              let uu____10840 =
                let uu____10842 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____10842
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____10840  in
            Prims.strcat uu____10836 uu____10838  in
          Prims.strcat "Operation " uu____10834  in
        failwith uu____10832
    | FStar_Parser_AST.Uvar id1 ->
        let uu____10848 = str "u#"  in
        let uu____10850 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____10848 uu____10850
    | FStar_Parser_AST.Wild  ->
        let uu____10851 = p_term false false e  in
        soft_parens_with_nesting uu____10851
    | FStar_Parser_AST.Const uu____10854 ->
        let uu____10855 = p_term false false e  in
        soft_parens_with_nesting uu____10855
    | FStar_Parser_AST.Op uu____10858 ->
        let uu____10865 = p_term false false e  in
        soft_parens_with_nesting uu____10865
    | FStar_Parser_AST.Tvar uu____10868 ->
        let uu____10869 = p_term false false e  in
        soft_parens_with_nesting uu____10869
    | FStar_Parser_AST.Var uu____10872 ->
        let uu____10873 = p_term false false e  in
        soft_parens_with_nesting uu____10873
    | FStar_Parser_AST.Name uu____10876 ->
        let uu____10877 = p_term false false e  in
        soft_parens_with_nesting uu____10877
    | FStar_Parser_AST.Construct uu____10880 ->
        let uu____10891 = p_term false false e  in
        soft_parens_with_nesting uu____10891
    | FStar_Parser_AST.Abs uu____10894 ->
        let uu____10901 = p_term false false e  in
        soft_parens_with_nesting uu____10901
    | FStar_Parser_AST.App uu____10904 ->
        let uu____10911 = p_term false false e  in
        soft_parens_with_nesting uu____10911
    | FStar_Parser_AST.Let uu____10914 ->
        let uu____10935 = p_term false false e  in
        soft_parens_with_nesting uu____10935
    | FStar_Parser_AST.LetOpen uu____10938 ->
        let uu____10943 = p_term false false e  in
        soft_parens_with_nesting uu____10943
    | FStar_Parser_AST.Seq uu____10946 ->
        let uu____10951 = p_term false false e  in
        soft_parens_with_nesting uu____10951
    | FStar_Parser_AST.Bind uu____10954 ->
        let uu____10961 = p_term false false e  in
        soft_parens_with_nesting uu____10961
    | FStar_Parser_AST.If uu____10964 ->
        let uu____10971 = p_term false false e  in
        soft_parens_with_nesting uu____10971
    | FStar_Parser_AST.Match uu____10974 ->
        let uu____10989 = p_term false false e  in
        soft_parens_with_nesting uu____10989
    | FStar_Parser_AST.TryWith uu____10992 ->
        let uu____11007 = p_term false false e  in
        soft_parens_with_nesting uu____11007
    | FStar_Parser_AST.Ascribed uu____11010 ->
        let uu____11019 = p_term false false e  in
        soft_parens_with_nesting uu____11019
    | FStar_Parser_AST.Record uu____11022 ->
        let uu____11035 = p_term false false e  in
        soft_parens_with_nesting uu____11035
    | FStar_Parser_AST.Project uu____11038 ->
        let uu____11043 = p_term false false e  in
        soft_parens_with_nesting uu____11043
    | FStar_Parser_AST.Product uu____11046 ->
        let uu____11053 = p_term false false e  in
        soft_parens_with_nesting uu____11053
    | FStar_Parser_AST.Sum uu____11056 ->
        let uu____11067 = p_term false false e  in
        soft_parens_with_nesting uu____11067
    | FStar_Parser_AST.QForall uu____11070 ->
        let uu____11083 = p_term false false e  in
        soft_parens_with_nesting uu____11083
    | FStar_Parser_AST.QExists uu____11086 ->
        let uu____11099 = p_term false false e  in
        soft_parens_with_nesting uu____11099
    | FStar_Parser_AST.Refine uu____11102 ->
        let uu____11107 = p_term false false e  in
        soft_parens_with_nesting uu____11107
    | FStar_Parser_AST.NamedTyp uu____11110 ->
        let uu____11115 = p_term false false e  in
        soft_parens_with_nesting uu____11115
    | FStar_Parser_AST.Requires uu____11118 ->
        let uu____11126 = p_term false false e  in
        soft_parens_with_nesting uu____11126
    | FStar_Parser_AST.Ensures uu____11129 ->
        let uu____11137 = p_term false false e  in
        soft_parens_with_nesting uu____11137
    | FStar_Parser_AST.Attributes uu____11140 ->
        let uu____11143 = p_term false false e  in
        soft_parens_with_nesting uu____11143
    | FStar_Parser_AST.Quote uu____11146 ->
        let uu____11151 = p_term false false e  in
        soft_parens_with_nesting uu____11151
    | FStar_Parser_AST.VQuote uu____11154 ->
        let uu____11155 = p_term false false e  in
        soft_parens_with_nesting uu____11155
    | FStar_Parser_AST.Antiquote uu____11158 ->
        let uu____11159 = p_term false false e  in
        soft_parens_with_nesting uu____11159

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___125_11162  ->
    match uu___125_11162 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____11171) ->
        let uu____11174 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____11174
    | FStar_Const.Const_bytearray (bytes,uu____11176) ->
        let uu____11181 =
          let uu____11182 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____11182  in
        let uu____11183 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____11181 uu____11183
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___123_11206 =
          match uu___123_11206 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___124_11213 =
          match uu___124_11213 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____11228  ->
               match uu____11228 with
               | (s,w) ->
                   let uu____11235 = signedness s  in
                   let uu____11236 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____11235 uu____11236)
            sign_width_opt
           in
        let uu____11237 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____11237 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____11241 = FStar_Range.string_of_range r  in str uu____11241
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____11245 = p_quident lid  in
        let uu____11246 =
          let uu____11247 =
            let uu____11248 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____11248  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____11247  in
        FStar_Pprint.op_Hat_Hat uu____11245 uu____11246

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____11251 = str "u#"  in
    let uu____11253 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____11251 uu____11253

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11255;_},u1::u2::[])
        ->
        let uu____11261 =
          let uu____11262 = p_universeFrom u1  in
          let uu____11263 =
            let uu____11264 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____11264  in
          FStar_Pprint.op_Hat_Slash_Hat uu____11262 uu____11263  in
        FStar_Pprint.group uu____11261
    | FStar_Parser_AST.App uu____11265 ->
        let uu____11272 = head_and_args u  in
        (match uu____11272 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____11298 =
                    let uu____11299 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____11300 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____11308  ->
                           match uu____11308 with
                           | (u1,uu____11314) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____11299 uu____11300  in
                  FStar_Pprint.group uu____11298
              | uu____11315 ->
                  let uu____11316 =
                    let uu____11318 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____11318
                     in
                  failwith uu____11316))
    | uu____11321 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____11347 = FStar_Ident.text_of_id id1  in str uu____11347
    | FStar_Parser_AST.Paren u1 ->
        let uu____11350 = p_universeFrom u1  in
        soft_parens_with_nesting uu____11350
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____11351;_},uu____11352::uu____11353::[])
        ->
        let uu____11357 = p_universeFrom u  in
        soft_parens_with_nesting uu____11357
    | FStar_Parser_AST.App uu____11358 ->
        let uu____11365 = p_universeFrom u  in
        soft_parens_with_nesting uu____11365
    | uu____11366 ->
        let uu____11367 =
          let uu____11369 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____11369
           in
        failwith uu____11367

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
       | FStar_Parser_AST.Module (uu____11458,decls) ->
           let uu____11464 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11464
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____11473,decls,uu____11475) ->
           let uu____11482 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____11482
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____11542  ->
         match uu____11542 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____11564)) -> false
      | ([],uu____11568) -> false
      | uu____11572 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____11582 -> true
         | uu____11584 -> false)
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
        | FStar_Parser_AST.Module (uu____11627,decls) -> decls
        | FStar_Parser_AST.Interface (uu____11633,decls,uu____11635) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____11687 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____11700;
                 FStar_Parser_AST.doc = uu____11701;
                 FStar_Parser_AST.quals = uu____11702;
                 FStar_Parser_AST.attrs = uu____11703;_}::uu____11704 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____11710 =
                   let uu____11713 =
                     let uu____11716 = FStar_List.tl ds  in d :: uu____11716
                      in
                   d0 :: uu____11713  in
                 (uu____11710, (d0.FStar_Parser_AST.drange))
             | uu____11721 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____11687 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____11778 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____11778 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____11887 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____11887, comments1))))))
  