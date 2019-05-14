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
            let uu____103 = let uu____106 = f x  in uu____106 :: acc  in
            aux xs uu____103
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
            let uu____173 = f x  in
            (match uu____173 with
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
          let uu____229 = f x  in if uu____229 then all f xs else false
  
let (all_explicit :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list -> Prims.bool) =
  fun args  ->
    FStar_Util.for_all
      (fun uu___0_271  ->
         match uu___0_271 with
         | (uu____280,FStar_Parser_AST.Nothing ) -> true
         | uu____288 -> false) args
  
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____320 'Auu____321 .
    Prims.bool -> ('Auu____320 -> 'Auu____321) -> 'Auu____320 -> 'Auu____321
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
  'Auu____431 'Auu____432 .
    'Auu____431 ->
      ('Auu____432 -> 'Auu____431) ->
        'Auu____432 FStar_Pervasives_Native.option -> 'Auu____431
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
  'Auu____545 .
    FStar_Pprint.document ->
      ('Auu____545 -> FStar_Pprint.document) ->
        'Auu____545 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____570 =
          let uu____571 =
            let uu____572 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____572  in
          FStar_Pprint.separate_map uu____571 f l  in
        FStar_Pprint.group uu____570
  
let precede_break_separate_map :
  'Auu____584 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____584 -> FStar_Pprint.document) ->
          'Auu____584 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____614 =
            let uu____615 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____616 =
              let uu____617 = FStar_List.hd l  in
              FStar_All.pipe_right uu____617 f  in
            FStar_Pprint.precede uu____615 uu____616  in
          let uu____618 =
            let uu____619 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____625 =
                   let uu____626 =
                     let uu____627 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____627  in
                   FStar_Pprint.op_Hat_Hat sep uu____626  in
                 FStar_Pprint.op_Hat_Hat break1 uu____625) uu____619
             in
          FStar_Pprint.op_Hat_Hat uu____614 uu____618
  
let concat_break_map :
  'Auu____635 .
    ('Auu____635 -> FStar_Pprint.document) ->
      'Auu____635 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____655 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____659 = f x  in FStar_Pprint.op_Hat_Hat uu____659 break1)
          l
         in
      FStar_Pprint.group uu____655
  
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
    let uu____722 = str "begin"  in
    let uu____724 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____722 contents uu____724
  
let separate_map_last :
  'Auu____737 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____737 -> FStar_Pprint.document) ->
        'Auu____737 Prims.list -> FStar_Pprint.document
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
  'Auu____789 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____789 -> FStar_Pprint.document) ->
        'Auu____789 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____821 =
          let uu____822 =
            let uu____823 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____823  in
          separate_map_last uu____822 f l  in
        FStar_Pprint.group uu____821
  
let separate_map_or_flow :
  'Auu____833 .
    FStar_Pprint.document ->
      ('Auu____833 -> FStar_Pprint.document) ->
        'Auu____833 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____871 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____871 -> FStar_Pprint.document) ->
        'Auu____871 Prims.list -> FStar_Pprint.document
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
  'Auu____923 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____923 -> FStar_Pprint.document) ->
        'Auu____923 Prims.list -> FStar_Pprint.document
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
              let uu____1005 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____1005
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____1027 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1027 -> FStar_Pprint.document) ->
                  'Auu____1027 Prims.list -> FStar_Pprint.document
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
                    (let uu____1086 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1086
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____1106 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____1106 -> FStar_Pprint.document) ->
                  'Auu____1106 Prims.list -> FStar_Pprint.document
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
                    (let uu____1165 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____1165
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string * (Prims.string * Prims.string) Prims.list) ->
    FStar_Pprint.document)
  =
  fun uu____1184  ->
    match uu____1184 with
    | (comment,keywords) ->
        let uu____1218 =
          let uu____1219 =
            let uu____1222 = str comment  in
            let uu____1223 =
              let uu____1226 =
                let uu____1229 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____1240  ->
                       match uu____1240 with
                       | (k,v1) ->
                           let uu____1253 =
                             let uu____1256 = str k  in
                             let uu____1257 =
                               let uu____1260 =
                                 let uu____1263 = str v1  in [uu____1263]  in
                               FStar_Pprint.rarrow :: uu____1260  in
                             uu____1256 :: uu____1257  in
                           FStar_Pprint.concat uu____1253) keywords
                   in
                [uu____1229]  in
              FStar_Pprint.space :: uu____1226  in
            uu____1222 :: uu____1223  in
          FStar_Pprint.concat uu____1219  in
        FStar_Pprint.group uu____1218
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____1279 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____1309 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____1309
      | uu____1312 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____1410::(e2,uu____1412)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____1464 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1506,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1534,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1587 = extract_from_list e2  in e1 :: uu____1587
    | uu____1596 ->
        let uu____1597 =
          let uu____1599 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1599  in
        failwith uu____1597
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1622;
           FStar_Parser_AST.level = uu____1623;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1638 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1660;
           FStar_Parser_AST.level = uu____1661;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1663;
                                                         FStar_Parser_AST.level
                                                           = uu____1664;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1666;
                                                    FStar_Parser_AST.level =
                                                      uu____1667;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1692;
                FStar_Parser_AST.level = uu____1693;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1695;
           FStar_Parser_AST.level = uu____1696;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1720 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1744 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1752;
           FStar_Parser_AST.range = uu____1753;
           FStar_Parser_AST.level = uu____1754;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1755;
                                                         FStar_Parser_AST.range
                                                           = uu____1756;
                                                         FStar_Parser_AST.level
                                                           = uu____1757;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1759;
                                                    FStar_Parser_AST.level =
                                                      uu____1760;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1790;
                FStar_Parser_AST.range = uu____1791;
                FStar_Parser_AST.level = uu____1792;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1794;
           FStar_Parser_AST.level = uu____1795;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1819 = extract_from_ref_set e1  in
        let uu____1825 = extract_from_ref_set e2  in
        FStar_List.append uu____1819 uu____1825
    | uu____1834 ->
        let uu____1835 =
          let uu____1837 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1837  in
        failwith uu____1835
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1858 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1858
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1873 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1873
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1888 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1888 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1898 = FStar_Ident.text_of_id op  in uu____1898 <> "~"))
  
let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____2022 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____2051 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____2062 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____2073 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level = (associativity * token Prims.list)
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___1_2099  ->
    match uu___1_2099 with
    | FStar_Util.Inl c -> Prims.op_Hat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___2_2134  ->
      match uu___2_2134 with
      | FStar_Util.Inl c ->
          let uu____2147 = FStar_String.get s (Prims.parse_int "0")  in
          uu____2147 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____2163 .
    Prims.string ->
      ('Auu____2163 * (FStar_Char.char,Prims.string) FStar_Util.either
        Prims.list) -> Prims.bool
  =
  fun s  ->
    fun uu____2187  ->
      match uu____2187 with
      | (assoc_levels,tokens) ->
          let uu____2219 = FStar_List.tryFind (matches_token s) tokens  in
          uu____2219 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___3_2391 =
    match uu___3_2391 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2441  ->
         match uu____2441 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string -> (Prims.int * Prims.int * Prims.int))
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2516 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2516 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2568) ->
          assoc_levels
      | uu____2606 -> failwith (Prims.op_Hat "Unrecognized operator " s)
  
let max_level :
  'Auu____2639 . ('Auu____2639 * token Prims.list) Prims.list -> Prims.int =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2688 =
        FStar_List.tryFind
          (fun uu____2724  ->
             match uu____2724 with
             | (uu____2741,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2688 with
      | FStar_Pervasives_Native.Some ((uu____2770,l1,uu____2772),uu____2773)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2823 =
            let uu____2825 =
              let uu____2827 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2827  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2825
             in
          failwith uu____2823
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels : Prims.string -> (Prims.int * Prims.int * Prims.int)) =
  fun op  ->
    let uu____2862 = assign_levels level_associativity_spec op  in
    match uu____2862 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2925 =
      let uu____2928 =
        let uu____2934 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2934  in
      FStar_List.tryFind uu____2928 operatorInfix0ad12  in
    uu____2925 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____3005 =
      let uu____3020 =
        let uu____3038 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____3038  in
      FStar_List.tryFind uu____3020 opinfix34  in
    uu____3005 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____3108 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____3108
    then (Prims.parse_int "1")
    else
      (let uu____3121 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____3121
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____3167 . FStar_Ident.ident -> 'Auu____3167 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _3187 when _3187 = (Prims.parse_int "0") -> true
      | _3189 when _3189 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____3191 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____3191 ["-"; "~"])
      | _3199 when _3199 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____3201 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____3201
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _3223 when _3223 = (Prims.parse_int "3") ->
          let uu____3224 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____3224 [".()<-"; ".[]<-"]
      | uu____3232 -> false
  
type annotation_style =
  | Binders of (Prims.int * Prims.int * Prims.bool) 
  | Arrows of (Prims.int * Prims.int) 
let (uu___is_Binders : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binders _0 -> true | uu____3278 -> false
  
let (__proj__Binders__item___0 :
  annotation_style -> (Prims.int * Prims.int * Prims.bool)) =
  fun projectee  -> match projectee with | Binders _0 -> _0 
let (uu___is_Arrows : annotation_style -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrows _0 -> true | uu____3330 -> false
  
let (__proj__Arrows__item___0 : annotation_style -> (Prims.int * Prims.int))
  = fun projectee  -> match projectee with | Arrows _0 -> _0 
let (all_binders_annot : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let is_binder_annot b =
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated uu____3386 -> true
      | uu____3397 -> false  in
    let rec all_binders e1 l =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____3450 = FStar_List.for_all is_binder_annot bs  in
          if uu____3450
          then all_binders tgt (l + (FStar_List.length bs))
          else (false, (Prims.parse_int "0"))
      | uu____3473 -> (true, (l + (Prims.parse_int "1")))  in
    let uu____3478 = all_binders e (Prims.parse_int "0")  in
    match uu____3478 with
    | (b,l) -> if b && (l > (Prims.parse_int "1")) then true else false
  
type catf =
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
let (cat_with_colon :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun x  ->
    fun y  ->
      let uu____3517 = FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon y  in
      FStar_Pprint.op_Hat_Hat x uu____3517
  
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
  'Auu____3741 .
    ('Auu____3741 -> FStar_Pprint.document) ->
      'Auu____3741 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3783 = FStar_ST.op_Bang comment_stack  in
          match uu____3783 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment =
                let uu____3854 = str c  in
                FStar_Pprint.op_Hat_Hat uu____3854 FStar_Pprint.hardline  in
              let uu____3855 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3855
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3897 = FStar_Pprint.op_Hat_Hat acc comment  in
                  comments_before_pos uu____3897 print_pos lookahead_pos))
              else
                (let uu____3900 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3900))
           in
        let uu____3903 =
          let uu____3909 =
            let uu____3910 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3910  in
          let uu____3911 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3909 uu____3911  in
        match uu____3903 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3920 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3920
              else comments  in
            if comments1 = FStar_Pprint.empty
            then printed_e
            else
              (let uu____3932 = FStar_Pprint.op_Hat_Hat comments1 printed_e
                  in
               FStar_Pprint.group uu____3932)
  
let with_comment_sep :
  'Auu____3944 'Auu____3945 .
    ('Auu____3944 -> 'Auu____3945) ->
      'Auu____3944 ->
        FStar_Range.range -> (FStar_Pprint.document * 'Auu____3945)
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____3991 = FStar_ST.op_Bang comment_stack  in
          match uu____3991 with
          | [] -> (acc, false)
          | (c,crange)::cs ->
              let comment = str c  in
              let uu____4062 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____4062
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____4104 =
                    if acc = FStar_Pprint.empty
                    then comment
                    else
                      (let uu____4108 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                           comment
                          in
                       FStar_Pprint.op_Hat_Hat acc uu____4108)
                     in
                  comments_before_pos uu____4104 print_pos lookahead_pos))
              else
                (let uu____4111 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____4111))
           in
        let uu____4114 =
          let uu____4120 =
            let uu____4121 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____4121  in
          let uu____4122 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____4120 uu____4122  in
        match uu____4114 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____4135 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____4135
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
                let uu____4198 = FStar_ST.op_Bang comment_stack  in
                match uu____4198 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____4292 =
                          let uu____4294 =
                            let uu____4296 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____4296  in
                          uu____4294 - lbegin  in
                        max k uu____4292  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____4301 =
                          let uu____4302 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____4303 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____4302 uu____4303  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____4301  in
                      let uu____4304 =
                        let uu____4306 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____4306  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____4304 pos meta_decl doc2 true init1))
                | uu____4309 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____4322 = FStar_Range.line_of_pos pos  in
                         uu____4322 - lbegin  in
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
                       let uu____4364 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____4364)
  
let separate_map_with_comments :
  'Auu____4378 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____4378 -> FStar_Pprint.document) ->
          'Auu____4378 Prims.list ->
            ('Auu____4378 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4447 x =
              match uu____4447 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4476 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4476 meta_decl doc1 false false
                     in
                  let uu____4480 =
                    let uu____4482 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4482  in
                  let uu____4483 =
                    let uu____4484 =
                      let uu____4485 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____4485  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4484  in
                  (uu____4480, uu____4483)
               in
            let uu____4487 =
              let uu____4494 = FStar_List.hd xs  in
              let uu____4495 = FStar_List.tl xs  in (uu____4494, uu____4495)
               in
            match uu____4487 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4523 =
                    let uu____4525 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4525  in
                  let uu____4526 =
                    let uu____4527 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____4527  in
                  (uu____4523, uu____4526)  in
                let uu____4529 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4529
  
let separate_map_with_comments_kw :
  'Auu____4556 'Auu____4557 .
    'Auu____4556 ->
      'Auu____4556 ->
        ('Auu____4556 -> 'Auu____4557 -> FStar_Pprint.document) ->
          'Auu____4557 Prims.list ->
            ('Auu____4557 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____4631 x =
              match uu____4631 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____4660 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____4660 meta_decl doc1 false false
                     in
                  let uu____4664 =
                    let uu____4666 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____4666  in
                  let uu____4667 =
                    let uu____4668 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____4668  in
                  (uu____4664, uu____4667)
               in
            let uu____4670 =
              let uu____4677 = FStar_List.hd xs  in
              let uu____4678 = FStar_List.tl xs  in (uu____4677, uu____4678)
               in
            match uu____4670 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____4706 =
                    let uu____4708 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____4708  in
                  let uu____4709 = f prefix1 x  in (uu____4706, uu____4709)
                   in
                let uu____4711 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____4711
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____6040)) ->
          let uu____6053 =
            let uu____6055 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____6055 FStar_Util.is_upper  in
          if uu____6053
          then
            let uu____6061 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____6061 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____6064 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____6071 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____6074 =
      let uu____6075 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____6076 =
        let uu____6077 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____6077  in
      FStar_Pprint.op_Hat_Hat uu____6075 uu____6076  in
    FStar_Pprint.op_Hat_Hat uu____6071 uu____6074

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____6082 ->
        let uu____6083 =
          let uu____6084 = str "@ "  in
          let uu____6086 =
            let uu____6087 =
              let uu____6088 =
                let uu____6089 =
                  let uu____6090 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____6090  in
                FStar_Pprint.op_Hat_Hat uu____6089 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____6088  in
            FStar_Pprint.op_Hat_Hat uu____6087 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____6084 uu____6086  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____6083

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____6096  ->
    match uu____6096 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____6144 =
                match uu____6144 with
                | (kwd,arg) ->
                    let uu____6157 = str "@"  in
                    let uu____6159 =
                      let uu____6160 = str kwd  in
                      let uu____6161 =
                        let uu____6162 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6162
                         in
                      FStar_Pprint.op_Hat_Hat uu____6160 uu____6161  in
                    FStar_Pprint.op_Hat_Hat uu____6157 uu____6159
                 in
              let uu____6163 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____6163 FStar_Pprint.hardline
           in
        let uu____6170 =
          let uu____6171 =
            let uu____6172 =
              let uu____6173 = str doc1  in
              let uu____6174 =
                let uu____6175 =
                  let uu____6176 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____6176  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____6175  in
              FStar_Pprint.op_Hat_Hat uu____6173 uu____6174  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____6172  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____6171  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6170

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____6195 =
          let uu____6196 = str "val"  in
          let uu____6198 =
            let uu____6199 =
              let uu____6200 = p_lident lid  in
              let uu____6201 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____6200 uu____6201  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6199  in
          FStar_Pprint.op_Hat_Hat uu____6196 uu____6198  in
        let uu____6202 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____6195 uu____6202
    | FStar_Parser_AST.TopLevelLet (uu____6205,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____6250 =
               let uu____6251 = str "let"  in p_letlhs uu____6251 lb false
                in
             FStar_Pprint.group uu____6250) lbs
    | uu____6254 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___4_6275 =
          match uu___4_6275 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____6299 = f x  in
              let uu____6300 =
                let uu____6301 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____6301  in
              FStar_Pprint.op_Hat_Hat uu____6299 uu____6300
           in
        let uu____6302 = str "["  in
        let uu____6304 =
          let uu____6305 = p_list' l  in
          let uu____6306 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____6305 uu____6306  in
        FStar_Pprint.op_Hat_Hat uu____6302 uu____6304

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____6319 =
          let uu____6320 = str "open"  in
          let uu____6322 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6320 uu____6322  in
        FStar_Pprint.group uu____6319
    | FStar_Parser_AST.Include uid ->
        let uu____6328 =
          let uu____6329 = str "include"  in
          let uu____6331 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6329 uu____6331  in
        FStar_Pprint.group uu____6328
    | FStar_Parser_AST.Friend uid ->
        let uu____6337 =
          let uu____6338 = str "friend"  in
          let uu____6340 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6338 uu____6340  in
        FStar_Pprint.group uu____6337
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____6355 =
          let uu____6356 = str "module"  in
          let uu____6358 =
            let uu____6359 =
              let uu____6360 = p_uident uid1  in
              let uu____6361 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____6360 uu____6361  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6359  in
          FStar_Pprint.op_Hat_Hat uu____6356 uu____6358  in
        let uu____6362 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____6355 uu____6362
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____6368 =
          let uu____6369 = str "module"  in
          let uu____6371 =
            let uu____6372 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6372  in
          FStar_Pprint.op_Hat_Hat uu____6369 uu____6371  in
        FStar_Pprint.group uu____6368
    | FStar_Parser_AST.Tycon
        (true
         ,uu____6373,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____6434 = str "effect"  in
          let uu____6436 =
            let uu____6437 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6437  in
          FStar_Pprint.op_Hat_Hat uu____6434 uu____6436  in
        let uu____6438 =
          let uu____6439 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____6439 FStar_Pprint.equals
           in
        let uu____6442 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____6438 uu____6442
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____6473 =
          let uu____6474 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____6474  in
        let uu____6487 =
          let uu____6488 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____6526 =
                    let uu____6527 = str "and"  in
                    p_fsdocTypeDeclPairs uu____6527 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____6526)) uu____6488
           in
        FStar_Pprint.op_Hat_Hat uu____6473 uu____6487
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____6554 = str "let"  in
          let uu____6556 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____6554 uu____6556  in
        let uu____6557 = str "and"  in
        separate_map_with_comments_kw let_doc uu____6557 p_letbinding lbs
          (fun uu____6572  ->
             match uu____6572 with
             | (p,t) ->
                 let uu____6599 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____6599;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____6615 =
          let uu____6616 = str "val"  in
          let uu____6618 =
            let uu____6619 =
              let uu____6620 = p_lident lid  in
              let uu____6621 = sig_as_binders_if_possible t false  in
              FStar_Pprint.op_Hat_Hat uu____6620 uu____6621  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6619  in
          FStar_Pprint.op_Hat_Hat uu____6616 uu____6618  in
        FStar_All.pipe_left FStar_Pprint.group uu____6615
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____6636 =
            let uu____6638 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____6638 FStar_Util.is_upper  in
          if uu____6636
          then FStar_Pprint.empty
          else
            (let uu____6646 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____6646 FStar_Pprint.space)
           in
        let uu____6648 =
          let uu____6649 = p_ident id1  in
          let uu____6650 =
            let uu____6651 =
              let uu____6652 =
                let uu____6653 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6653  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6652  in
            FStar_Pprint.group uu____6651  in
          FStar_Pprint.op_Hat_Hat uu____6649 uu____6650  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____6648
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____6672 = str "exception"  in
        let uu____6674 =
          let uu____6675 =
            let uu____6676 = p_uident uid  in
            let uu____6677 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____6687 =
                     let uu____6688 = str "of"  in
                     let uu____6690 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____6688 uu____6690  in
                   FStar_Pprint.op_Hat_Hat break1 uu____6687) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____6676 uu____6677  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6675  in
        FStar_Pprint.op_Hat_Hat uu____6672 uu____6674
    | FStar_Parser_AST.NewEffect ne ->
        let uu____6694 = str "new_effect"  in
        let uu____6696 =
          let uu____6697 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6697  in
        FStar_Pprint.op_Hat_Hat uu____6694 uu____6696
    | FStar_Parser_AST.SubEffect se ->
        let uu____6706 = str "sub_effect"  in
        let uu____6708 =
          let uu____6709 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6709  in
        FStar_Pprint.op_Hat_Hat uu____6706 uu____6708
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____6712 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____6717,uu____6718) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____6756 = str "%splice"  in
        let uu____6758 =
          let uu____6759 =
            let uu____6760 = str ";"  in p_list p_uident uu____6760 ids  in
          let uu____6762 =
            let uu____6763 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6763  in
          FStar_Pprint.op_Hat_Hat uu____6759 uu____6762  in
        FStar_Pprint.op_Hat_Hat uu____6756 uu____6758

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___5_6766  ->
    match uu___5_6766 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____6769 = str "#set-options"  in
        let uu____6771 =
          let uu____6772 =
            let uu____6773 = str s  in FStar_Pprint.dquotes uu____6773  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6772  in
        FStar_Pprint.op_Hat_Hat uu____6769 uu____6771
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____6778 = str "#reset-options"  in
        let uu____6780 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____6786 =
                 let uu____6787 = str s  in FStar_Pprint.dquotes uu____6787
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6786) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6778 uu____6780
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____6792 = str "#push-options"  in
        let uu____6794 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____6800 =
                 let uu____6801 = str s  in FStar_Pprint.dquotes uu____6801
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6800) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____6792 uu____6794
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
    fun uu____6836  ->
      match uu____6836 with
      | (typedecl,fsdoc_opt) ->
          let uu____6849 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____6849 with
           | (comm,decl,body,pre) ->
               if comm = FStar_Pprint.empty
               then
                 let uu____6874 = pre body  in
                 FStar_Pprint.op_Hat_Hat decl uu____6874
               else
                 (let uu____6877 =
                    let uu____6878 =
                      let uu____6879 =
                        let uu____6880 = pre body  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6880 comm  in
                      FStar_Pprint.op_Hat_Hat decl uu____6879  in
                    let uu____6881 =
                      let uu____6882 =
                        let uu____6883 =
                          let uu____6884 =
                            let uu____6885 =
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                                body
                               in
                            FStar_Pprint.op_Hat_Hat comm uu____6885  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____6884
                           in
                        FStar_Pprint.nest (Prims.parse_int "2") uu____6883
                         in
                      FStar_Pprint.op_Hat_Hat decl uu____6882  in
                    FStar_Pprint.ifflat uu____6878 uu____6881  in
                  FStar_All.pipe_left FStar_Pprint.group uu____6877))

and (p_typeDecl :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document * FStar_Pprint.document * FStar_Pprint.document
        * (FStar_Pprint.document -> FStar_Pprint.document)))
  =
  fun pre  ->
    fun uu___6_6888  ->
      match uu___6_6888 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let uu____6935 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (FStar_Pprint.empty, uu____6935, FStar_Pprint.empty,
            FStar_Pervasives.id)
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let uu____6976 = p_typ_sep false false t  in
          (match uu____6976 with
           | (comm,doc1) ->
               let uu____6996 = p_typeDeclPrefix pre true lid bs typ_opt  in
               (comm, uu____6996, doc1, jump2))
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____7085 =
            match uu____7085 with
            | (lid1,t,doc_opt) ->
                let uu____7117 =
                  let uu____7122 =
                    FStar_Range.extend_to_end_of_line
                      t.FStar_Parser_AST.range
                     in
                  with_comment_sep (p_recordFieldDecl ps) (lid1, t, doc_opt)
                    uu____7122
                   in
                (match uu____7117 with
                 | (comm,field) ->
                     let sep =
                       if ps then FStar_Pprint.semi else FStar_Pprint.empty
                        in
                     inline_comment_or_above comm field sep)
             in
          let p_fields =
            let uu____7150 =
              separate_map_last FStar_Pprint.hardline
                p_recordFieldAndComments record_field_decls
               in
            braces_with_nesting uu____7150  in
          let uu____7164 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____7164, p_fields,
            ((fun d  -> FStar_Pprint.op_Hat_Hat FStar_Pprint.space d)))
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____7264 =
            match uu____7264 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____7308 =
                    let uu____7309 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____7309  in
                  FStar_Range.extend_to_end_of_line uu____7308  in
                let uu____7320 =
                  with_comment_sep p_constructorBranch
                    (uid, t_opt, doc_opt, use_of) range
                   in
                (match uu____7320 with
                 | (comm,ctor) ->
                     inline_comment_or_above comm ctor FStar_Pprint.empty)
             in
          let datacon_doc =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____7374 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (FStar_Pprint.empty, uu____7374, datacon_doc, jump2)

and (p_typeDeclPrefix :
  (FStar_Pprint.document * FStar_Parser_AST.fsdoc
    FStar_Pervasives_Native.option) ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____7379  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____7379 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____7423 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____7423  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____7425 =
                        let uu____7428 =
                          let uu____7431 = p_fsdoc fsdoc  in
                          let uu____7432 =
                            let uu____7435 = cont lid_doc  in [uu____7435]
                             in
                          uu____7431 :: uu____7432  in
                        kw :: uu____7428  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____7425
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____7451 =
                        let uu____7452 =
                          let uu____7453 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____7453 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7452
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7451
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____7481 =
                          let uu____7482 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____7482  in
                        prefix2 uu____7481 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident * FStar_Parser_AST.term * FStar_Parser_AST.fsdoc
      FStar_Pervasives_Native.option) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____7484  ->
      match uu____7484 with
      | (lid,t,doc_opt) ->
          let uu____7516 =
            let uu____7517 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____7518 =
              let uu____7519 = p_lident lid  in
              let uu____7520 =
                let uu____7521 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____7521  in
              FStar_Pprint.op_Hat_Hat uu____7519 uu____7520  in
            FStar_Pprint.op_Hat_Hat uu____7517 uu____7518  in
          FStar_Pprint.group uu____7516

and (p_constructorBranch :
  (FStar_Ident.ident * FStar_Parser_AST.term FStar_Pervasives_Native.option *
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option * Prims.bool) ->
    FStar_Pprint.document)
  =
  fun uu____7523  ->
    match uu____7523 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____7572 =
            let uu____7573 =
              let uu____7574 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7574  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____7573  in
          FStar_Pprint.group uu____7572  in
        let uu____7575 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____7576 =
          default_or_map uid_doc
            (fun t  ->
               let uu____7586 =
                 let uu____7587 =
                   let uu____7588 =
                     let uu____7589 =
                       let uu____7590 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7590
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____7589  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7588  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____7587  in
               FStar_Pprint.group uu____7586) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____7575 uu____7576

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      Prims.bool -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____7594  ->
      fun inner_let  ->
        match uu____7594 with
        | (pat,uu____7607) ->
            let uu____7618 =
              match pat.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.None )) ->
                  (pat1,
                    (FStar_Pervasives_Native.Some (t, FStar_Pprint.empty)))
              | FStar_Parser_AST.PatAscribed
                  (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                  let uu____7738 =
                    let uu____7748 =
                      let uu____7756 =
                        let uu____7757 =
                          let uu____7758 =
                            let uu____7759 = str "by"  in
                            let uu____7761 =
                              let uu____7762 = p_atomicTerm tac  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____7762
                               in
                            FStar_Pprint.op_Hat_Hat uu____7759 uu____7761  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____7758
                           in
                        FStar_Pprint.group uu____7757  in
                      (t, uu____7756)  in
                    FStar_Pervasives_Native.Some uu____7748  in
                  (pat1, uu____7738)
              | uu____7784 -> (pat, FStar_Pervasives_Native.None)  in
            (match uu____7618 with
             | (pat1,ascr) ->
                 (match pat1.FStar_Parser_AST.pat with
                  | FStar_Parser_AST.PatApp
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           (lid,uu____7828);
                         FStar_Parser_AST.prange = uu____7829;_},pats)
                      ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____7865 =
                              sig_as_binders_if_possible t true  in
                            FStar_Pprint.op_Hat_Hat uu____7865 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____7874 =
                        if inner_let
                        then
                          let uu____7888 = pats_as_binders_if_possible pats
                             in
                          match uu____7888 with
                          | (bs,style) ->
                              ((FStar_List.append bs [ascr_doc]), style)
                        else
                          (let uu____7911 = pats_as_binders_if_possible pats
                              in
                           match uu____7911 with
                           | (bs,style) ->
                               ((FStar_List.append bs [ascr_doc]), style))
                         in
                      (match uu____7874 with
                       | (terms,style) ->
                           let uu____7938 =
                             let uu____7939 =
                               let uu____7940 =
                                 let uu____7941 = p_lident lid  in
                                 let uu____7942 =
                                   format_sig style terms true true  in
                                 FStar_Pprint.op_Hat_Hat uu____7941
                                   uu____7942
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____7940
                                in
                             FStar_Pprint.op_Hat_Hat kw uu____7939  in
                           FStar_All.pipe_left FStar_Pprint.group uu____7938)
                  | uu____7945 ->
                      let ascr_doc =
                        match ascr with
                        | FStar_Pervasives_Native.Some (t,tac) ->
                            let uu____7962 =
                              let uu____7963 =
                                let uu____7964 =
                                  p_typ_top
                                    (Arrows
                                       ((Prims.parse_int "2"),
                                         (Prims.parse_int "2"))) false false
                                    t
                                   in
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                                  uu____7964
                                 in
                              FStar_Pprint.group uu____7963  in
                            FStar_Pprint.op_Hat_Hat uu____7962 tac
                        | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
                         in
                      let uu____7978 =
                        let uu____7979 =
                          let uu____7980 =
                            let uu____7981 = p_tuplePattern pat1  in
                            FStar_Pprint.op_Hat_Slash_Hat kw uu____7981  in
                          FStar_Pprint.group uu____7980  in
                        FStar_Pprint.op_Hat_Hat uu____7979 ascr_doc  in
                      FStar_Pprint.group uu____7978))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____7983  ->
      match uu____7983 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e) false  in
          let uu____8012 = p_term_sep false false e  in
          (match uu____8012 with
           | (comm,doc_expr) ->
               let doc_expr1 =
                 inline_comment_or_above comm doc_expr FStar_Pprint.empty  in
               let uu____8022 =
                 let uu____8023 =
                   FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals
                     doc_expr1
                    in
                 FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____8023  in
               let uu____8024 =
                 let uu____8025 =
                   let uu____8026 =
                     let uu____8027 =
                       let uu____8028 = jump2 doc_expr1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____8028
                        in
                     FStar_Pprint.group uu____8027  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8026  in
                 FStar_Pprint.op_Hat_Hat doc_pat uu____8025  in
               FStar_Pprint.ifflat uu____8022 uu____8024)

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___7_8029  ->
    match uu___7_8029 with
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
        let uu____8109 = p_uident uid  in
        let uu____8110 = p_binders true bs  in
        let uu____8112 =
          let uu____8113 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____8113  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____8109 uu____8110 uu____8112

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
          let uu____8142 =
            let uu____8143 =
              let uu____8144 =
                let uu____8145 = p_uident uid  in
                let uu____8146 = p_binders true bs  in
                let uu____8148 =
                  let uu____8149 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____8149  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____8145 uu____8146 uu____8148
                 in
              FStar_Pprint.group uu____8144  in
            let uu____8154 =
              let uu____8155 = str "with"  in
              let uu____8157 =
                let uu____8158 =
                  let uu____8159 =
                    let uu____8160 =
                      let uu____8161 =
                        let uu____8162 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____8162
                         in
                      separate_map_last uu____8161 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8160  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8159  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____8158  in
              FStar_Pprint.op_Hat_Hat uu____8155 uu____8157  in
            FStar_Pprint.op_Hat_Slash_Hat uu____8143 uu____8154  in
          braces_with_nesting uu____8142

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____8176,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____8233 =
            let uu____8234 = p_lident lid  in
            let uu____8235 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____8234 uu____8235  in
          let uu____8236 = p_simpleTerm ps false e  in
          prefix2 uu____8233 uu____8236
      | uu____8238 ->
          let uu____8239 =
            let uu____8241 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____8241
             in
          failwith uu____8239

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____8391 =
        match uu____8391 with
        | (kwd,t) ->
            let uu____8411 =
              let uu____8412 = str kwd  in
              let uu____8413 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____8412 uu____8413  in
            let uu____8414 = p_simpleTerm ps false t  in
            prefix2 uu____8411 uu____8414
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____8424 =
      let uu____8425 =
        let uu____8426 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____8427 =
          let uu____8428 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8428  in
        FStar_Pprint.op_Hat_Hat uu____8426 uu____8427  in
      let uu____8430 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____8425 uu____8430  in
    let uu____8431 =
      let uu____8432 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8432  in
    FStar_Pprint.op_Hat_Hat uu____8424 uu____8431

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___8_8433  ->
    match uu___8_8433 with
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
        let uu____8453 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____8453 FStar_Pprint.hardline
    | uu____8454 ->
        let uu____8455 =
          let uu____8456 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____8456  in
        FStar_Pprint.op_Hat_Hat uu____8455 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___9_8459  ->
    match uu___9_8459 with
    | FStar_Parser_AST.Rec  ->
        let uu____8460 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8460
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___10_8462  ->
    match uu___10_8462 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let t1 =
          match t.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Abs (uu____8479,e) -> e
          | uu____8495 ->
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (t,
                     (FStar_Parser_AST.unit_const t.FStar_Parser_AST.range),
                     FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                FStar_Parser_AST.Expr
           in
        let uu____8502 = str "#["  in
        let uu____8504 =
          let uu____8505 = p_term false false t1  in
          let uu____8508 =
            let uu____8509 = str "]"  in
            FStar_Pprint.op_Hat_Hat uu____8509 break1  in
          FStar_Pprint.op_Hat_Hat uu____8505 uu____8508  in
        FStar_Pprint.op_Hat_Hat uu____8502 uu____8504

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____8519 =
          let uu____8520 =
            let uu____8521 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____8521  in
          FStar_Pprint.separate_map uu____8520 p_tuplePattern pats  in
        FStar_Pprint.group uu____8519
    | uu____8524 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____8539 =
          let uu____8540 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____8540 p_constructorPattern pats  in
        FStar_Pprint.group uu____8539
    | uu____8543 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____8548;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____8571 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____8572 = p_constructorPattern hd1  in
        let uu____8573 = p_constructorPattern tl1  in
        infix0 uu____8571 uu____8572 uu____8573
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____8575;_},pats)
        ->
        let uu____8591 = p_quident uid  in
        let uu____8592 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____8591 uu____8592
    | uu____8595 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____8635;
               FStar_Parser_AST.blevel = uu____8636;
               FStar_Parser_AST.aqual = uu____8637;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____8670 =
               let uu____8671 = p_ident lid  in
               p_refinement aqual uu____8671 t1 phi  in
             soft_parens_with_nesting uu____8670
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____8674;
               FStar_Parser_AST.blevel = uu____8675;
               FStar_Parser_AST.aqual = uu____8676;_},phi))
             ->
             let uu____8695 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____8695
         | uu____8696 ->
             let uu____8701 =
               let uu____8702 = p_tuplePattern pat  in
               let uu____8703 =
                 let uu____8704 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____8704
                  in
               FStar_Pprint.op_Hat_Hat uu____8702 uu____8703  in
             soft_parens_with_nesting uu____8701)
    | FStar_Parser_AST.PatList pats ->
        let uu____8710 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____8710 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____8743 =
          match uu____8743 with
          | (lid,pat) ->
              let uu____8768 = p_qlident lid  in
              let uu____8769 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____8768 uu____8769
           in
        let uu____8770 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____8770
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____8792 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____8793 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____8796 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____8792 uu____8793 uu____8796
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____8813 =
          let uu____8814 =
            let uu____8815 =
              let uu____8816 = FStar_Ident.text_of_id op  in str uu____8816
               in
            let uu____8818 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____8815 uu____8818  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____8814  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____8813
    | FStar_Parser_AST.PatWild aqual ->
        let uu____8822 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____8822 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____8834 = FStar_Pprint.optional p_aqual aqual  in
        let uu____8835 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____8834 uu____8835
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____8841 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____8847;
           FStar_Parser_AST.prange = uu____8848;_},uu____8849)
        ->
        let uu____8864 = p_tuplePattern p  in
        soft_parens_with_nesting uu____8864
    | FStar_Parser_AST.PatTuple (uu____8865,false ) ->
        let uu____8876 = p_tuplePattern p  in
        soft_parens_with_nesting uu____8876
    | uu____8877 ->
        let uu____8878 =
          let uu____8880 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____8880  in
        failwith uu____8878

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____8888;_},uu____8889)
        -> true
    | uu____8904 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____8910) -> true
    | uu____8915 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      let uu____8926 = p_binder' is_atomic b  in
      match uu____8926 with
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
          let uu____8969 =
            let uu____8970 =
              FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
            let uu____8971 = p_lident lid  in
            FStar_Pprint.op_Hat_Hat uu____8970 uu____8971  in
          (uu____8969, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.TVariable lid ->
          let uu____8979 = p_lident lid  in
          (uu____8979, FStar_Pervasives_Native.None, cat_with_colon)
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____8996 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____9007;
                   FStar_Parser_AST.blevel = uu____9008;
                   FStar_Parser_AST.aqual = uu____9009;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____9034 = p_lident lid  in
                p_refinement' b.FStar_Parser_AST.aqual uu____9034 t1 phi
            | uu____9035 ->
                let t' =
                  let uu____9037 = is_typ_tuple t  in
                  if uu____9037
                  then
                    let uu____9040 = p_tmFormula t  in
                    soft_parens_with_nesting uu____9040
                  else p_tmFormula t  in
                let uu____9043 =
                  let uu____9044 =
                    FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual
                     in
                  let uu____9045 = p_lident lid  in
                  FStar_Pprint.op_Hat_Hat uu____9044 uu____9045  in
                (uu____9043, t')
             in
          (match uu____8996 with
           | (b',t') ->
               let catf =
                 let uu____9063 =
                   is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)
                    in
                 if uu____9063
                 then
                   fun x  ->
                     fun y  ->
                       let uu____9070 =
                         let uu____9071 =
                           let uu____9072 = cat_with_colon x y  in
                           FStar_Pprint.op_Hat_Hat uu____9072
                             FStar_Pprint.rparen
                            in
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen
                           uu____9071
                          in
                       FStar_Pprint.group uu____9070
                 else
                   (fun x  ->
                      fun y  ->
                        let uu____9077 = cat_with_colon x y  in
                        FStar_Pprint.group uu____9077)
                  in
               (b', (FStar_Pervasives_Native.Some t'), catf))
      | FStar_Parser_AST.TAnnotated uu____9082 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____9118;
                  FStar_Parser_AST.blevel = uu____9119;
                  FStar_Parser_AST.aqual = uu____9120;_},phi)
               ->
               let uu____9137 =
                 p_refinement' b.FStar_Parser_AST.aqual
                   FStar_Pprint.underscore t1 phi
                  in
               (match uu____9137 with
                | (b',t') ->
                    (b', (FStar_Pervasives_Native.Some t'), cat_with_colon))
           | uu____9158 ->
               if is_atomic
               then
                 let uu____9170 = p_atomicTerm t  in
                 (uu____9170, FStar_Pervasives_Native.None, cat_with_colon)
               else
                 (let uu____9177 = p_appTerm t  in
                  (uu____9177, FStar_Pervasives_Native.None, cat_with_colon)))

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____9194 = p_refinement' aqual_opt binder t phi  in
          match uu____9194 with | (b,typ) -> cat_with_colon b typ

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
            | FStar_Parser_AST.Construct uu____9216 -> false
            | FStar_Parser_AST.App uu____9235 -> false
            | FStar_Parser_AST.Op uu____9249 -> false
            | uu____9262 -> true  in
          let uu____9264 = p_noSeqTerm false false phi  in
          match uu____9264 with
          | (comm,phi1) ->
              let phi2 =
                if comm = FStar_Pprint.empty
                then phi1
                else
                  (let uu____9281 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline phi1  in
                   FStar_Pprint.op_Hat_Hat comm uu____9281)
                 in
              let jump_break =
                if is_t_atomic
                then (Prims.parse_int "0")
                else (Prims.parse_int "1")  in
              let uu____9290 =
                let uu____9291 = FStar_Pprint.optional p_aqual aqual_opt  in
                FStar_Pprint.op_Hat_Hat uu____9291 binder  in
              let uu____9292 =
                let uu____9293 = p_appTerm t  in
                let uu____9294 =
                  let uu____9295 =
                    let uu____9296 =
                      let uu____9297 = soft_braces_with_nesting_tight phi2
                         in
                      let uu____9298 = soft_braces_with_nesting phi2  in
                      FStar_Pprint.ifflat uu____9297 uu____9298  in
                    FStar_Pprint.group uu____9296  in
                  FStar_Pprint.jump (Prims.parse_int "2") jump_break
                    uu____9295
                   in
                FStar_Pprint.op_Hat_Hat uu____9293 uu____9294  in
              (uu____9290, uu____9292)

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____9324 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____9324

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    let uu____9330 =
      (FStar_Util.starts_with lid.FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____9333 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____9333)
       in
    if uu____9330
    then FStar_Pprint.underscore
    else (let uu____9338 = FStar_Ident.text_of_id lid  in str uu____9338)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    let uu____9345 =
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        &&
        (let uu____9348 = FStar_Options.print_real_names ()  in
         Prims.op_Negation uu____9348)
       in
    if uu____9345
    then FStar_Pprint.underscore
    else (let uu____9353 = FStar_Ident.text_of_lid lid  in str uu____9353)

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
          let uu____9390 = FStar_Pprint.op_Hat_Hat doc1 sep  in
          FStar_Pprint.group uu____9390
        else
          (let uu____9393 =
             let uu____9394 =
               let uu____9395 =
                 let uu____9396 =
                   let uu____9397 = FStar_Pprint.op_Hat_Hat break1 comm  in
                   FStar_Pprint.op_Hat_Hat sep uu____9397  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____9396  in
               FStar_Pprint.group uu____9395  in
             let uu____9398 =
               let uu____9399 =
                 let uu____9400 = FStar_Pprint.op_Hat_Hat doc1 sep  in
                 FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____9400  in
               FStar_Pprint.op_Hat_Hat comm uu____9399  in
             FStar_Pprint.ifflat uu____9394 uu____9398  in
           FStar_All.pipe_left FStar_Pprint.group uu____9393)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____9423 = p_noSeqTerm true false e1  in
            (match uu____9423 with
             | (comm,t1) ->
                 let uu____9432 =
                   inline_comment_or_above comm t1 FStar_Pprint.semi  in
                 let uu____9433 =
                   let uu____9434 = p_term ps pb e2  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____9434
                    in
                 FStar_Pprint.op_Hat_Hat uu____9432 uu____9433)
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____9454 =
              let uu____9455 =
                let uu____9456 =
                  let uu____9457 = p_lident x  in
                  let uu____9458 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____9457 uu____9458  in
                let uu____9459 =
                  let uu____9460 = p_noSeqTermAndComment true false e1  in
                  let uu____9463 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____9460 uu____9463  in
                op_Hat_Slash_Plus_Hat uu____9456 uu____9459  in
              FStar_Pprint.group uu____9455  in
            let uu____9464 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____9454 uu____9464
        | uu____9465 ->
            let uu____9466 = p_noSeqTermAndComment ps pb e  in
            FStar_Pprint.group uu____9466

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
            let uu____9493 = p_noSeqTerm true false e1  in
            (match uu____9493 with
             | (comm,t1) ->
                 let uu____9506 =
                   let uu____9507 =
                     let uu____9508 =
                       FStar_Pprint.op_Hat_Hat t1 FStar_Pprint.semi  in
                     FStar_Pprint.group uu____9508  in
                   let uu____9509 =
                     let uu____9510 = p_term ps pb e2  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____9510
                      in
                   FStar_Pprint.op_Hat_Hat uu____9507 uu____9509  in
                 (comm, uu____9506))
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____9530 =
              let uu____9531 =
                let uu____9532 =
                  let uu____9533 =
                    let uu____9534 = p_lident x  in
                    let uu____9535 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.long_left_arrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____9534 uu____9535  in
                  let uu____9536 =
                    let uu____9537 = p_noSeqTermAndComment true false e1  in
                    let uu____9540 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.semi
                       in
                    FStar_Pprint.op_Hat_Hat uu____9537 uu____9540  in
                  op_Hat_Slash_Plus_Hat uu____9533 uu____9536  in
                FStar_Pprint.group uu____9532  in
              let uu____9541 = p_term ps pb e2  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9531 uu____9541  in
            (FStar_Pprint.empty, uu____9530)
        | uu____9542 -> p_noSeqTerm ps pb e

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
            let uu____9595 =
              let uu____9596 = p_tmIff e1  in
              let uu____9597 =
                let uu____9598 =
                  let uu____9599 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9599
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____9598  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9596 uu____9597  in
            FStar_Pprint.group uu____9595
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____9626 =
              let uu____9627 = p_tmIff e1  in
              let uu____9628 =
                let uu____9629 =
                  let uu____9630 =
                    let uu____9631 = p_typ false false t  in
                    let uu____9634 =
                      let uu____9635 = str "by"  in
                      let uu____9637 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____9635 uu____9637  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____9631 uu____9634  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____9630
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____9629  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9627 uu____9628  in
            FStar_Pprint.group uu____9626
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____9638;_},e1::e2::e3::[])
            ->
            let uu____9671 =
              let uu____9672 =
                let uu____9673 =
                  let uu____9674 = p_atomicTermNotQUident e1  in
                  let uu____9675 =
                    let uu____9676 =
                      let uu____9677 =
                        let uu____9678 = p_term false false e2  in
                        soft_parens_with_nesting uu____9678  in
                      let uu____9681 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____9677 uu____9681  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9676  in
                  FStar_Pprint.op_Hat_Hat uu____9674 uu____9675  in
                FStar_Pprint.group uu____9673  in
              let uu____9682 =
                let uu____9683 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____9683  in
              FStar_Pprint.op_Hat_Hat uu____9672 uu____9682  in
            FStar_Pprint.group uu____9671
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____9684;_},e1::e2::e3::[])
            ->
            let uu____9717 =
              let uu____9718 =
                let uu____9719 =
                  let uu____9720 = p_atomicTermNotQUident e1  in
                  let uu____9721 =
                    let uu____9722 =
                      let uu____9723 =
                        let uu____9724 = p_term false false e2  in
                        soft_brackets_with_nesting uu____9724  in
                      let uu____9727 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____9723 uu____9727  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____9722  in
                  FStar_Pprint.op_Hat_Hat uu____9720 uu____9721  in
                FStar_Pprint.group uu____9719  in
              let uu____9728 =
                let uu____9729 = p_noSeqTermAndComment ps pb e3  in
                jump2 uu____9729  in
              FStar_Pprint.op_Hat_Hat uu____9718 uu____9728  in
            FStar_Pprint.group uu____9717
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____9745 =
              let uu____9746 = str "requires"  in
              let uu____9748 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9746 uu____9748  in
            FStar_Pprint.group uu____9745
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____9764 =
              let uu____9765 = str "ensures"  in
              let uu____9767 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9765 uu____9767  in
            FStar_Pprint.group uu____9764
        | FStar_Parser_AST.Attributes es ->
            let uu____9774 =
              let uu____9775 = str "attributes"  in
              let uu____9777 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____9775 uu____9777  in
            FStar_Pprint.group uu____9774
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____9803 =
                let uu____9804 =
                  let uu____9805 = str "if"  in
                  let uu____9807 = p_noSeqTermAndComment false false e1  in
                  op_Hat_Slash_Plus_Hat uu____9805 uu____9807  in
                let uu____9810 =
                  let uu____9811 = str "then"  in
                  let uu____9813 = p_noSeqTermAndComment ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____9811 uu____9813  in
                FStar_Pprint.op_Hat_Slash_Hat uu____9804 uu____9810  in
              FStar_Pprint.group uu____9803
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____9817,uu____9818,e31) when
                     is_unit e31 ->
                     let uu____9838 = p_noSeqTermAndComment false false e2
                        in
                     soft_parens_with_nesting uu____9838
                 | uu____9841 -> p_noSeqTermAndComment false false e2  in
               let uu____9844 =
                 let uu____9845 =
                   let uu____9846 = str "if"  in
                   let uu____9848 = p_noSeqTermAndComment false false e1  in
                   op_Hat_Slash_Plus_Hat uu____9846 uu____9848  in
                 let uu____9851 =
                   let uu____9852 =
                     let uu____9853 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____9853 e2_doc  in
                   let uu____9855 =
                     let uu____9856 = str "else"  in
                     let uu____9858 = p_noSeqTermAndComment ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____9856 uu____9858  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____9852 uu____9855  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____9845 uu____9851  in
               FStar_Pprint.group uu____9844)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____9903 =
              let uu____9904 =
                let uu____9905 =
                  let uu____9906 = str "try"  in
                  let uu____9908 = p_noSeqTermAndComment false false e1  in
                  prefix2 uu____9906 uu____9908  in
                let uu____9911 =
                  let uu____9912 = str "with"  in
                  let uu____9914 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____9912 uu____9914  in
                FStar_Pprint.op_Hat_Slash_Hat uu____9905 uu____9911  in
              FStar_Pprint.group uu____9904  in
            let uu____9931 = paren_if (ps || pb)  in uu____9931 uu____9903
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____9980 =
              let uu____9981 =
                let uu____9982 =
                  let uu____9983 = str "match"  in
                  let uu____9985 = p_noSeqTermAndComment false false e1  in
                  let uu____9988 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____9983 uu____9985 uu____9988
                   in
                let uu____9992 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____9982 uu____9992  in
              FStar_Pprint.group uu____9981  in
            let uu____10009 = paren_if (ps || pb)  in uu____10009 uu____9980
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____10030 =
              let uu____10031 =
                let uu____10032 =
                  let uu____10033 = str "let open"  in
                  let uu____10035 = p_quident uid  in
                  let uu____10036 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____10033 uu____10035 uu____10036
                   in
                let uu____10040 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____10032 uu____10040  in
              FStar_Pprint.group uu____10031  in
            let uu____10042 = paren_if ps  in uu____10042 uu____10030
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____10137 is_last =
              match uu____10137 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____10200 =
                          let uu____10201 = str "let"  in
                          let uu____10203 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____10201
                            uu____10203
                           in
                        FStar_Pprint.group uu____10200
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____10206 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2) true  in
                  let uu____10217 = p_term_sep false false e2  in
                  (match uu____10217 with
                   | (comm,doc_expr) ->
                       let doc_expr1 =
                         inline_comment_or_above comm doc_expr
                           FStar_Pprint.empty
                          in
                       let uu____10227 =
                         if is_last
                         then
                           let uu____10229 =
                             FStar_Pprint.flow break1
                               [doc_pat; FStar_Pprint.equals]
                              in
                           let uu____10230 = str "in"  in
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") uu____10229 doc_expr1
                             uu____10230
                         else
                           (let uu____10236 =
                              FStar_Pprint.flow break1
                                [doc_pat; FStar_Pprint.equals; doc_expr1]
                               in
                            FStar_Pprint.hang (Prims.parse_int "2")
                              uu____10236)
                          in
                       FStar_Pprint.op_Hat_Hat attrs uu____10227)
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____10311 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____10311
                     else
                       (let uu____10316 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____10316)) lbs
               in
            let lbs_doc =
              let uu____10320 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____10320  in
            let uu____10321 =
              let uu____10322 =
                let uu____10323 =
                  let uu____10324 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____10324
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____10323  in
              FStar_Pprint.group uu____10322  in
            let uu____10326 = paren_if ps  in uu____10326 uu____10321
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____10333;_}::[],{
                                                              FStar_Parser_AST.tm
                                                                =
                                                                FStar_Parser_AST.Match
                                                                (maybe_x,branches);
                                                              FStar_Parser_AST.range
                                                                = uu____10336;
                                                              FStar_Parser_AST.level
                                                                = uu____10337;_})
            when matches_var maybe_x x ->
            let uu____10399 =
              let uu____10400 =
                let uu____10401 = str "function"  in
                let uu____10403 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____10401 uu____10403  in
              FStar_Pprint.group uu____10400  in
            let uu____10420 = paren_if (ps || pb)  in uu____10420 uu____10399
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____10432 =
              let uu____10433 = str "quote"  in
              let uu____10435 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____10433 uu____10435  in
            FStar_Pprint.group uu____10432
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____10443 =
              let uu____10444 = str "`"  in
              let uu____10446 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____10444 uu____10446  in
            FStar_Pprint.group uu____10443
        | FStar_Parser_AST.VQuote e1 ->
            let uu____10451 =
              let uu____10452 = str "`%"  in
              let uu____10454 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____10452 uu____10454  in
            FStar_Pprint.group uu____10451
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____10456;
              FStar_Parser_AST.level = uu____10457;_}
            ->
            let uu____10464 =
              let uu____10465 = str "`@"  in
              let uu____10467 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____10465 uu____10467  in
            FStar_Pprint.group uu____10464
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____10472 =
              let uu____10473 = str "`#"  in
              let uu____10475 = p_noSeqTermAndComment ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____10473 uu____10475  in
            FStar_Pprint.group uu____10472
        | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
            let head1 =
              let uu____10498 = str "calc"  in
              let uu____10500 =
                let uu____10501 =
                  let uu____10502 = p_noSeqTermAndComment false false rel  in
                  let uu____10505 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.lbrace
                     in
                  FStar_Pprint.op_Hat_Hat uu____10502 uu____10505  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10501  in
              FStar_Pprint.op_Hat_Hat uu____10498 uu____10500  in
            let bot = FStar_Pprint.rbrace  in
            let uu____10507 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline bot  in
            let uu____10508 =
              let uu____10509 =
                let uu____10510 =
                  let uu____10511 = p_noSeqTermAndComment false false init1
                     in
                  let uu____10514 =
                    let uu____10515 = str ";"  in
                    let uu____10517 =
                      let uu____10518 =
                        separate_map_last FStar_Pprint.hardline p_calcStep
                          steps
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                        uu____10518
                       in
                    FStar_Pprint.op_Hat_Hat uu____10515 uu____10517  in
                  FStar_Pprint.op_Hat_Hat uu____10511 uu____10514  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____10510  in
              FStar_All.pipe_left (FStar_Pprint.nest (Prims.parse_int "2"))
                uu____10509
               in
            FStar_Pprint.enclose head1 uu____10507 uu____10508
        | uu____10521 -> p_typ ps pb e

and (p_calcStep :
  Prims.bool -> FStar_Parser_AST.calc_step -> FStar_Pprint.document) =
  fun uu____10522  ->
    fun uu____10523  ->
      match uu____10523 with
      | FStar_Parser_AST.CalcStep (rel,just,next) ->
          let uu____10547 =
            let uu____10548 = p_noSeqTermAndComment false false rel  in
            let uu____10551 =
              let uu____10552 =
                let uu____10553 =
                  let uu____10554 =
                    let uu____10555 = p_noSeqTermAndComment false false just
                       in
                    let uu____10558 =
                      let uu____10559 =
                        let uu____10560 =
                          let uu____10561 =
                            let uu____10562 =
                              p_noSeqTermAndComment false false next  in
                            let uu____10565 = str ";"  in
                            FStar_Pprint.op_Hat_Hat uu____10562 uu____10565
                             in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                            uu____10561
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace
                          uu____10560
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10559
                       in
                    FStar_Pprint.op_Hat_Hat uu____10555 uu____10558  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10554  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____10553  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____10552  in
            FStar_Pprint.op_Hat_Hat uu____10548 uu____10551  in
          FStar_Pprint.group uu____10547

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___11_10567  ->
    match uu___11_10567 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____10591 =
          let uu____10592 = str "[@"  in
          let uu____10594 =
            let uu____10595 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____10599 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____10595 uu____10599  in
          FStar_Pprint.op_Hat_Slash_Hat uu____10592 uu____10594  in
        FStar_Pprint.group uu____10591

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
        | FStar_Parser_AST.QForall (bs,(uu____10632,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____10698 =
                   let uu____10699 =
                     let uu____10700 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____10700 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____10699 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____10698 term_doc
             | pats ->
                 let uu____10711 =
                   let uu____10712 =
                     let uu____10713 =
                       let uu____10714 =
                         let uu____10715 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____10715
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____10714 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____10718 = p_trigger trigger  in
                     prefix2 uu____10713 uu____10718  in
                   FStar_Pprint.group uu____10712  in
                 prefix2 uu____10711 term_doc)
        | FStar_Parser_AST.QExists (bs,(uu____10720,trigger),e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTermAndComment ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____10786 =
                   let uu____10787 =
                     let uu____10788 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____10788 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____10787 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____10786 term_doc
             | pats ->
                 let uu____10799 =
                   let uu____10800 =
                     let uu____10801 =
                       let uu____10802 =
                         let uu____10803 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____10803
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____10802 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____10806 = p_trigger trigger  in
                     prefix2 uu____10801 uu____10806  in
                   FStar_Pprint.group uu____10800  in
                 prefix2 uu____10799 term_doc)
        | uu____10807 -> p_simpleTerm ps pb e

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
      let uu____10840 = all_binders_annot t  in
      if uu____10840
      then
        let uu____10843 =
          p_typ_top
            (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true))
            false false t
           in
        FStar_Pprint.op_Hat_Hat s uu____10843
      else
        (let uu____10854 =
           let uu____10855 =
             let uu____10856 =
               p_typ_top
                 (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
                 false false t
                in
             FStar_Pprint.op_Hat_Hat s uu____10856  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____10855  in
         FStar_Pprint.group uu____10854)

and (collapse_pats :
  (FStar_Pprint.document * FStar_Pprint.document) Prims.list ->
    FStar_Pprint.document Prims.list)
  =
  fun pats  ->
    let fold_fun bs x =
      let uu____10915 = x  in
      match uu____10915 with
      | (b1,t1) ->
          (match bs with
           | [] -> [([b1], t1)]
           | hd1::tl1 ->
               let uu____10980 = hd1  in
               (match uu____10980 with
                | (b2s,t2) ->
                    if t1 = t2
                    then ((FStar_List.append b2s [b1]), t1) :: tl1
                    else ([b1], t1) :: hd1 :: tl1))
       in
    let p_collapsed_binder cb =
      let uu____11052 = cb  in
      match uu____11052 with
      | (bs,typ) ->
          (match bs with
           | [] -> failwith "Impossible"
           | b::[] -> cat_with_colon b typ
           | hd1::tl1 ->
               let uu____11071 =
                 FStar_List.fold_left
                   (fun x  ->
                      fun y  ->
                        let uu____11077 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space y  in
                        FStar_Pprint.op_Hat_Hat x uu____11077) hd1 tl1
                  in
               cat_with_colon uu____11071 typ)
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
                 FStar_Parser_AST.brange = uu____11184;
                 FStar_Parser_AST.blevel = uu____11185;
                 FStar_Parser_AST.aqual = uu____11186;_},phi))
               when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
               let uu____11219 =
                 let uu____11224 = p_ident lid  in
                 p_refinement' aqual uu____11224 t1 phi  in
               FStar_Pervasives_Native.Some uu____11219
           | (FStar_Parser_AST.PatVar (lid,aqual),uu____11231) ->
               let uu____11240 =
                 let uu____11245 =
                   let uu____11246 = FStar_Pprint.optional p_aqual aqual  in
                   let uu____11247 = p_ident lid  in
                   FStar_Pprint.op_Hat_Hat uu____11246 uu____11247  in
                 let uu____11248 = p_tmEqNoRefinement t  in
                 (uu____11245, uu____11248)  in
               FStar_Pervasives_Native.Some uu____11240
           | uu____11253 -> FStar_Pervasives_Native.None)
      | uu____11262 -> FStar_Pervasives_Native.None  in
    let all_unbound p =
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatAscribed uu____11279 -> false
      | uu____11299 -> true  in
    let uu____11301 = map_if_all all_binders pats  in
    match uu____11301 with
    | FStar_Pervasives_Native.Some bs ->
        let uu____11335 = collapse_pats bs  in
        (uu____11335,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), true)))
    | FStar_Pervasives_Native.None  ->
        let uu____11352 = FStar_List.map p_atomicPattern pats  in
        (uu____11352,
          (Binders ((Prims.parse_int "4"), (Prims.parse_int "0"), false)))

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____11369 -> str "forall"
    | FStar_Parser_AST.QExists uu____11401 -> str "exists"
    | uu____11433 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___12_11435  ->
    match uu___12_11435 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____11456 =
          let uu____11457 =
            let uu____11458 =
              let uu____11459 = str "pattern"  in
              let uu____11461 =
                let uu____11462 =
                  let uu____11463 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____11463
                   in
                FStar_Pprint.op_Hat_Hat uu____11462 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____11459 uu____11461  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____11458  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____11457  in
        FStar_Pprint.group uu____11456

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____11474 = str "\\/"  in
    FStar_Pprint.separate_map uu____11474 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____11487 =
      let uu____11488 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____11488 p_appTerm pats  in
    FStar_Pprint.group uu____11487

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____11516 = p_term_sep false pb e1  in
            (match uu____11516 with
             | (comm,doc1) ->
                 let prefix1 =
                   let uu____11525 = str "fun"  in
                   let uu____11527 =
                     let uu____11528 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Slash_Hat uu____11528
                       FStar_Pprint.rarrow
                      in
                   op_Hat_Slash_Plus_Hat uu____11525 uu____11527  in
                 let uu____11531 =
                   if comm <> FStar_Pprint.empty
                   then
                     let uu____11533 =
                       let uu____11534 =
                         let uu____11535 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                            in
                         FStar_Pprint.op_Hat_Hat comm uu____11535  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                         uu____11534
                        in
                     FStar_Pprint.op_Hat_Hat prefix1 uu____11533
                   else
                     (let uu____11538 = op_Hat_Slash_Plus_Hat prefix1 doc1
                         in
                      FStar_Pprint.group uu____11538)
                    in
                 let uu____11539 = paren_if ps  in uu____11539 uu____11531)
        | uu____11544 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern * FStar_Parser_AST.term
      FStar_Pervasives_Native.option * FStar_Parser_AST.term) ->
      FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____11552  ->
      match uu____11552 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____11607 =
                    let uu____11608 =
                      let uu____11609 =
                        let uu____11610 = p_tuplePattern p  in
                        let uu____11611 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____11610 uu____11611  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____11609
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____11608  in
                  FStar_Pprint.group uu____11607
              | FStar_Pervasives_Native.Some f ->
                  let uu____11619 =
                    let uu____11620 =
                      let uu____11621 =
                        let uu____11622 =
                          let uu____11623 =
                            let uu____11624 = p_tuplePattern p  in
                            let uu____11625 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____11624
                              uu____11625
                             in
                          FStar_Pprint.group uu____11623  in
                        let uu____11627 =
                          let uu____11628 =
                            let uu____11631 = p_tmFormula f  in
                            [uu____11631; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____11628  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____11622 uu____11627
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____11621
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____11620  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____11619
               in
            let uu____11633 = p_term_sep false pb e  in
            match uu____11633 with
            | (comm,doc1) ->
                if pb
                then
                  (if comm = FStar_Pprint.empty
                   then
                     let uu____11643 = op_Hat_Slash_Plus_Hat branch doc1  in
                     FStar_Pprint.group uu____11643
                   else
                     (let uu____11646 =
                        let uu____11647 =
                          let uu____11648 =
                            let uu____11649 =
                              let uu____11650 =
                                FStar_Pprint.op_Hat_Hat break1 comm  in
                              FStar_Pprint.op_Hat_Hat doc1 uu____11650  in
                            op_Hat_Slash_Plus_Hat branch uu____11649  in
                          FStar_Pprint.group uu____11648  in
                        let uu____11651 =
                          let uu____11652 =
                            let uu____11653 =
                              inline_comment_or_above comm doc1
                                FStar_Pprint.empty
                               in
                            jump2 uu____11653  in
                          FStar_Pprint.op_Hat_Hat branch uu____11652  in
                        FStar_Pprint.ifflat uu____11647 uu____11651  in
                      FStar_Pprint.group uu____11646))
                else
                  if comm <> FStar_Pprint.empty
                  then
                    (let uu____11657 =
                       let uu____11658 =
                         FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1
                          in
                       FStar_Pprint.op_Hat_Hat comm uu____11658  in
                     op_Hat_Slash_Plus_Hat branch uu____11657)
                  else op_Hat_Slash_Plus_Hat branch doc1
             in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____11679 =
                      let uu____11680 =
                        let uu____11681 =
                          let uu____11682 =
                            let uu____11683 =
                              let uu____11684 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____11684  in
                            FStar_Pprint.separate_map uu____11683
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____11682
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          uu____11681
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____11680
                       in
                    FStar_Pprint.group uu____11679
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____11692 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____11697;_},e1::e2::[])
        ->
        let uu____11723 = str "<==>"  in
        let uu____11725 = p_tmImplies e1  in
        let uu____11726 = p_tmIff e2  in
        infix0 uu____11723 uu____11725 uu____11726
    | uu____11727 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____11732;_},e1::e2::[])
        ->
        let uu____11758 = str "==>"  in
        let uu____11760 =
          p_tmArrow (Arrows ((Prims.parse_int "2"), (Prims.parse_int "2")))
            false p_tmFormula e1
           in
        let uu____11766 = p_tmImplies e2  in
        infix0 uu____11758 uu____11760 uu____11766
    | uu____11767 ->
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
          let uu____11781 =
            FStar_List.splitAt
              ((FStar_List.length terms) - (Prims.parse_int "1")) terms
             in
          match uu____11781 with
          | (terms',last1) ->
              let uu____11801 =
                match style with
                | Arrows (n1,ln) ->
                    let uu____11836 =
                      let uu____11837 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____11837
                       in
                    let uu____11838 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                        FStar_Pprint.space
                       in
                    (n1, ln, terms', uu____11836, uu____11838)
                | Binders (n1,ln,parens1) ->
                    let uu____11852 =
                      if parens1
                      then FStar_List.map soft_parens_with_nesting terms'
                      else terms'  in
                    let uu____11860 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                        FStar_Pprint.space
                       in
                    (n1, ln, uu____11852, break1, uu____11860)
                 in
              (match uu____11801 with
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
                    | _11893 when _11893 = (Prims.parse_int "1") ->
                        FStar_List.hd terms
                    | uu____11894 ->
                        let uu____11895 =
                          let uu____11896 =
                            let uu____11897 =
                              let uu____11898 =
                                FStar_Pprint.separate sep terms'1  in
                              let uu____11899 =
                                let uu____11900 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.op_Hat_Hat one_line_space
                                  uu____11900
                                 in
                              FStar_Pprint.op_Hat_Hat uu____11898 uu____11899
                               in
                            FStar_Pprint.op_Hat_Hat fs uu____11897  in
                          let uu____11901 =
                            let uu____11902 =
                              let uu____11903 =
                                let uu____11904 =
                                  let uu____11905 =
                                    FStar_Pprint.separate sep terms'1  in
                                  FStar_Pprint.op_Hat_Hat fs uu____11905  in
                                let uu____11906 =
                                  let uu____11907 =
                                    let uu____11908 =
                                      let uu____11909 =
                                        FStar_Pprint.op_Hat_Hat sep
                                          single_line_arg_indent
                                         in
                                      let uu____11910 =
                                        FStar_List.map
                                          (fun x  ->
                                             let uu____11916 =
                                               FStar_Pprint.hang
                                                 (Prims.parse_int "2") x
                                                in
                                             FStar_Pprint.align uu____11916)
                                          terms'1
                                         in
                                      FStar_Pprint.separate uu____11909
                                        uu____11910
                                       in
                                    FStar_Pprint.op_Hat_Hat
                                      single_line_arg_indent uu____11908
                                     in
                                  jump2 uu____11907  in
                                FStar_Pprint.ifflat uu____11904 uu____11906
                                 in
                              FStar_Pprint.group uu____11903  in
                            let uu____11918 =
                              let uu____11919 =
                                let uu____11920 =
                                  FStar_Pprint.op_Hat_Hat last_op1 last2  in
                                FStar_Pprint.hang last_n uu____11920  in
                              FStar_Pprint.align uu____11919  in
                            FStar_Pprint.prefix n1 (Prims.parse_int "1")
                              uu____11902 uu____11918
                             in
                          FStar_Pprint.ifflat uu____11896 uu____11901  in
                        FStar_Pprint.group uu____11895))

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
            | Arrows uu____11940 -> p_tmArrow' p_Tm e
            | Binders uu____11947 -> collapse_binders p_Tm e  in
          format_sig style terms false flat_space

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____11990 = FStar_List.map (fun b  -> p_binder false b) bs
             in
          let uu____12004 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____11990 uu____12004
      | uu____12007 -> let uu____12008 = p_Tm e  in [uu____12008]

and (collapse_binders :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      let rec accumulate_binders p_Tm1 e1 =
        match e1.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Product (bs,tgt) ->
            let uu____12093 = FStar_List.map (fun b  -> p_binder' false b) bs
               in
            let uu____12127 = accumulate_binders p_Tm1 tgt  in
            FStar_List.append uu____12093 uu____12127
        | uu____12150 ->
            let uu____12151 =
              let uu____12162 = p_Tm1 e1  in
              (uu____12162, FStar_Pervasives_Native.None, cat_with_colon)  in
            [uu____12151]
         in
      let fold_fun bs x =
        let uu____12260 = x  in
        match uu____12260 with
        | (b1,t1,f1) ->
            (match bs with
             | [] -> [([b1], t1, f1)]
             | hd1::tl1 ->
                 let uu____12392 = hd1  in
                 (match uu____12392 with
                  | (b2s,t2,uu____12421) ->
                      (match (t1, t2) with
                       | (FStar_Pervasives_Native.Some
                          typ1,FStar_Pervasives_Native.Some typ2) ->
                           if typ1 = typ2
                           then ((FStar_List.append b2s [b1]), t1, f1) :: tl1
                           else ([b1], t1, f1) :: hd1 :: tl1
                       | uu____12523 -> ([b1], t1, f1) :: bs)))
         in
      let p_collapsed_binder cb =
        let uu____12580 = cb  in
        match uu____12580 with
        | (bs,t,f) ->
            (match t with
             | FStar_Pervasives_Native.None  ->
                 (match bs with
                  | b::[] -> b
                  | uu____12609 -> failwith "Impossible")
             | FStar_Pervasives_Native.Some typ ->
                 (match bs with
                  | [] -> failwith "Impossible"
                  | b::[] -> f b typ
                  | hd1::tl1 ->
                      let uu____12620 =
                        FStar_List.fold_left
                          (fun x  ->
                             fun y  ->
                               let uu____12626 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.space y
                                  in
                               FStar_Pprint.op_Hat_Hat x uu____12626) hd1 tl1
                         in
                      f uu____12620 typ))
         in
      let binders =
        let uu____12642 = accumulate_binders p_Tm e  in
        FStar_List.fold_left fold_fun [] uu____12642  in
      map_rev p_collapsed_binder binders

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____12708 =
        let uu____12709 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____12709 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____12708  in
    let disj =
      let uu____12712 =
        let uu____12713 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____12713 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____12712  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____12736;_},e1::e2::[])
        ->
        let uu____12762 = p_tmDisjunction e1  in
        let uu____12767 =
          let uu____12772 = p_tmConjunction e2  in [uu____12772]  in
        FStar_List.append uu____12762 uu____12767
    | uu____12781 -> let uu____12782 = p_tmConjunction e  in [uu____12782]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____12795;_},e1::e2::[])
        ->
        let uu____12821 = p_tmConjunction e1  in
        let uu____12824 = let uu____12827 = p_tmTuple e2  in [uu____12827]
           in
        FStar_List.append uu____12821 uu____12824
    | uu____12828 -> let uu____12829 = p_tmTuple e  in [uu____12829]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____12869 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____12869
          (fun uu____12880  ->
             match uu____12880 with | (e1,uu____12889) -> p_tmEq e1) args
    | uu____12896 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____12905 =
             let uu____12906 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____12906  in
           FStar_Pprint.group uu____12905)

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
               (let uu____12959 = FStar_Ident.text_of_id op  in
                uu____12959 = "="))
              ||
              (let uu____12964 = FStar_Ident.text_of_id op  in
               uu____12964 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____12970 = levels op1  in
            (match uu____12970 with
             | (left1,mine,right1) ->
                 let uu____12989 =
                   let uu____12990 = FStar_All.pipe_left str op1  in
                   let uu____12992 = p_tmEqWith' p_X left1 e1  in
                   let uu____12993 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____12990 uu____12992 uu____12993  in
                 paren_if_gt curr mine uu____12989)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":=";
               FStar_Ident.idRange = uu____12994;_},e1::e2::[])
            ->
            let uu____13020 =
              let uu____13021 = p_tmEqWith p_X e1  in
              let uu____13022 =
                let uu____13023 =
                  let uu____13024 =
                    let uu____13025 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____13025  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____13024  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____13023  in
              FStar_Pprint.op_Hat_Hat uu____13021 uu____13022  in
            FStar_Pprint.group uu____13020
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____13026;_},e1::[])
            ->
            let uu____13045 = levels "-"  in
            (match uu____13045 with
             | (left1,mine,right1) ->
                 let uu____13065 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____13065)
        | uu____13066 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____13126)::(e2,uu____13128)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____13180 = is_list e  in
                 Prims.op_Negation uu____13180)
              ->
              let op = "::"  in
              let uu____13185 = levels op  in
              (match uu____13185 with
               | (left1,mine,right1) ->
                   let uu____13204 =
                     let uu____13205 = str op  in
                     let uu____13206 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____13208 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____13205 uu____13206 uu____13208  in
                   paren_if_gt curr mine uu____13204)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____13247 = levels op  in
              (match uu____13247 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____13306 = p_binder false b  in
                         let uu____13308 =
                           let uu____13309 =
                             let uu____13310 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____13310 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____13309
                            in
                         FStar_Pprint.op_Hat_Hat uu____13306 uu____13308
                     | FStar_Util.Inr t ->
                         let uu____13322 = p_tmNoEqWith' false p_X left1 t
                            in
                         let uu____13324 =
                           let uu____13325 =
                             let uu____13326 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____13326 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____13325
                            in
                         FStar_Pprint.op_Hat_Hat uu____13322 uu____13324
                      in
                   let uu____13327 =
                     let uu____13328 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____13340 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____13328 uu____13340  in
                   paren_if_gt curr mine uu____13327)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____13342;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____13392 = levels op  in
              (match uu____13392 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____13412 = str op  in
                     let uu____13413 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____13415 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____13412 uu____13413 uu____13415
                   else
                     (let uu____13419 =
                        let uu____13420 = str op  in
                        let uu____13421 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____13423 = p_tmNoEqWith' true p_X right1 e2
                           in
                        infix0 uu____13420 uu____13421 uu____13423  in
                      paren_if_gt curr mine uu____13419))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____13454 = levels op1  in
              (match uu____13454 with
               | (left1,mine,right1) ->
                   let uu____13473 =
                     let uu____13474 = str op1  in
                     let uu____13475 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____13477 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____13474 uu____13475 uu____13477  in
                   paren_if_gt curr mine uu____13473)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____13517 =
                let uu____13518 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____13522 =
                  let uu____13523 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____13523 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____13518 uu____13522  in
              braces_with_nesting uu____13517
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____13535;_},e1::[])
              ->
              let uu____13554 =
                let uu____13555 = str "~"  in
                let uu____13557 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____13555 uu____13557  in
              FStar_Pprint.group uu____13554
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____13562;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____13591 = levels op  in
                   (match uu____13591 with
                    | (left1,mine,right1) ->
                        let uu____13610 =
                          let uu____13611 = str op  in
                          let uu____13612 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____13614 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____13611 uu____13612 uu____13614  in
                        paren_if_gt curr mine uu____13610)
               | uu____13616 -> p_X e)
          | uu____13617 -> p_X e

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
        let uu____13646 =
          let uu____13647 = p_lident lid  in
          let uu____13648 =
            let uu____13649 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____13649  in
          FStar_Pprint.op_Hat_Slash_Hat uu____13647 uu____13648  in
        FStar_Pprint.group uu____13646
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____13666 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____13671 = p_appTerm e  in
    let uu____13672 =
      let uu____13673 =
        let uu____13674 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____13674 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____13673  in
    FStar_Pprint.op_Hat_Hat uu____13671 uu____13672

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____13697 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____13697 t phi
      | FStar_Parser_AST.TAnnotated uu____13698 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____13709 ->
          let uu____13712 =
            let uu____13714 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____13714
             in
          failwith uu____13712
      | FStar_Parser_AST.TVariable uu____13717 ->
          let uu____13720 =
            let uu____13722 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____13722
             in
          failwith uu____13720
      | FStar_Parser_AST.NoName uu____13725 ->
          let uu____13729 =
            let uu____13731 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____13731
             in
          failwith uu____13729

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid * FStar_Parser_AST.term) -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____13735  ->
      match uu____13735 with
      | (lid,e) ->
          let uu____13764 =
            let uu____13765 = p_qlident lid  in
            let uu____13766 =
              let uu____13767 = p_noSeqTermAndComment ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____13767
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____13765 uu____13766  in
          FStar_Pprint.group uu____13764

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____13773 when is_general_application e ->
        let uu____13786 = head_and_args e  in
        (match uu____13786 with
         | (head1,args) ->
             (match args with
              | e1::e2::[] when
                  (FStar_Pervasives_Native.snd e1) = FStar_Parser_AST.Infix
                  ->
                  let uu____13869 = p_argTerm e1  in
                  let uu____13870 =
                    let uu____13871 =
                      let uu____13872 =
                        let uu____13873 = str "`"  in
                        let uu____13875 =
                          let uu____13876 = p_indexingTerm head1  in
                          let uu____13877 = str "`"  in
                          FStar_Pprint.op_Hat_Hat uu____13876 uu____13877  in
                        FStar_Pprint.op_Hat_Hat uu____13873 uu____13875  in
                      FStar_Pprint.group uu____13872  in
                    let uu____13879 = p_argTerm e2  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____13871 uu____13879  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____13869 uu____13870
              | uu____13880 ->
                  let uu____13890 =
                    let uu____13904 =
                      FStar_ST.op_Bang should_print_fs_typ_app  in
                    if uu____13904
                    then
                      let uu____13941 =
                        FStar_Util.take
                          (fun uu____13974  ->
                             match uu____13974 with
                             | (uu____13983,aq) ->
                                 aq = FStar_Parser_AST.FsTypApp) args
                         in
                      match uu____13941 with
                      | (fs_typ_args,args1) ->
                          let uu____14042 =
                            let uu____14043 = p_indexingTerm head1  in
                            let uu____14044 =
                              let uu____14045 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                                  break1
                                 in
                              soft_surround_map_or_flow (Prims.parse_int "2")
                                (Prims.parse_int "0") FStar_Pprint.empty
                                FStar_Pprint.langle uu____14045
                                FStar_Pprint.rangle p_fsTypArg fs_typ_args
                               in
                            FStar_Pprint.op_Hat_Hat uu____14043 uu____14044
                             in
                          (uu____14042, args1)
                    else
                      (let uu____14066 = p_indexingTerm head1  in
                       (uu____14066, args))
                     in
                  (match uu____13890 with
                   | (head_doc,args1) ->
                       let uu____14096 =
                         let uu____14097 =
                           FStar_Pprint.op_Hat_Hat head_doc
                             FStar_Pprint.space
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") head_doc uu____14097 break1
                           FStar_Pprint.empty p_argTerm args1
                          in
                       FStar_Pprint.group uu____14096)))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____14136 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____14136)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____14167 =
               let uu____14168 = p_quident lid  in
               let uu____14169 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____14168 uu____14169  in
             FStar_Pprint.group uu____14167
         | hd1::tl1 ->
             let uu____14195 =
               let uu____14196 =
                 let uu____14197 =
                   let uu____14198 = p_quident lid  in
                   let uu____14199 = p_argTerm hd1  in
                   prefix2 uu____14198 uu____14199  in
                 FStar_Pprint.group uu____14197  in
               let uu____14200 =
                 let uu____14201 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____14201  in
               FStar_Pprint.op_Hat_Hat uu____14196 uu____14200  in
             FStar_Pprint.group uu____14195)
    | uu____14209 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____14235 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____14235 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____14245 = str "#"  in
        let uu____14247 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____14245 uu____14247
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____14259 = str "#["  in
        let uu____14261 =
          let uu____14262 = p_indexingTerm t  in
          let uu____14263 =
            let uu____14264 = str "]"  in
            let uu____14266 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____14264 uu____14266  in
          FStar_Pprint.op_Hat_Hat uu____14262 uu____14263  in
        FStar_Pprint.op_Hat_Hat uu____14259 uu____14261
    | (e,FStar_Parser_AST.Infix ) -> p_indexingTerm e
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term * FStar_Parser_AST.imp) -> FStar_Pprint.document) =
  fun uu____14281  ->
    match uu____14281 with | (e,uu____14290) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____14307;_},e1::e2::[])
          ->
          let uu____14333 =
            let uu____14334 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____14335 =
              let uu____14336 =
                let uu____14337 = p_term false false e2  in
                soft_parens_with_nesting uu____14337  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____14336  in
            FStar_Pprint.op_Hat_Hat uu____14334 uu____14335  in
          FStar_Pprint.group uu____14333
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____14340;_},e1::e2::[])
          ->
          let uu____14366 =
            let uu____14367 = p_indexingTerm_aux p_atomicTermNotQUident e1
               in
            let uu____14368 =
              let uu____14369 =
                let uu____14370 = p_term false false e2  in
                soft_brackets_with_nesting uu____14370  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____14369  in
            FStar_Pprint.op_Hat_Hat uu____14367 uu____14368  in
          FStar_Pprint.group uu____14366
      | uu____14373 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____14398 = p_quident lid  in
        let uu____14399 =
          let uu____14400 =
            let uu____14401 = p_term false false e1  in
            soft_parens_with_nesting uu____14401  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____14400  in
        FStar_Pprint.op_Hat_Hat uu____14398 uu____14399
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____14429 =
          let uu____14430 = FStar_Ident.text_of_id op  in str uu____14430  in
        let uu____14432 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____14429 uu____14432
    | uu____14433 -> p_atomicTermNotQUident e

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
         | uu____14459 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____14492 =
          let uu____14493 = FStar_Ident.text_of_id op  in str uu____14493  in
        let uu____14495 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____14492 uu____14495
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____14509 =
          let uu____14510 =
            let uu____14511 =
              let uu____14512 = FStar_Ident.text_of_id op  in str uu____14512
               in
            let uu____14514 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____14511 uu____14514  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____14510  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____14509
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____14543 = all_explicit args  in
        if uu____14543
        then
          let uu____14546 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____14547 =
            let uu____14548 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____14549 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____14548 p_tmEq uu____14549  in
          let uu____14571 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____14546 uu____14547 uu____14571
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____14605 =
                 let uu____14606 = p_quident lid  in
                 let uu____14607 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____14606 uu____14607  in
               FStar_Pprint.group uu____14605
           | hd1::tl1 ->
               let uu____14633 =
                 let uu____14634 =
                   let uu____14635 =
                     let uu____14636 = p_quident lid  in
                     let uu____14637 = p_argTerm hd1  in
                     prefix2 uu____14636 uu____14637  in
                   FStar_Pprint.group uu____14635  in
                 let uu____14638 =
                   let uu____14639 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____14639  in
                 FStar_Pprint.op_Hat_Hat uu____14634 uu____14638  in
               FStar_Pprint.group uu____14633)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____14663 =
          let uu____14664 = p_atomicTermNotQUident e1  in
          let uu____14665 =
            let uu____14666 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____14666  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____14664 uu____14665
           in
        FStar_Pprint.group uu____14663
    | uu____14669 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____14693 = p_quident constr_lid  in
        let uu____14694 =
          let uu____14695 =
            let uu____14696 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____14696  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____14695  in
        FStar_Pprint.op_Hat_Hat uu____14693 uu____14694
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____14702 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____14702 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____14707 = p_term_sep false false e1  in
        (match uu____14707 with
         | (comm,t) ->
             let doc1 = soft_parens_with_nesting t  in
             if comm = FStar_Pprint.empty
             then doc1
             else
               (let uu____14720 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline doc1  in
                FStar_Pprint.op_Hat_Hat comm uu____14720))
    | uu____14721 when is_array e ->
        let es = extract_from_list e  in
        let uu____14728 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____14729 =
          let uu____14730 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____14730
            (fun ps  -> p_noSeqTermAndComment ps false) es
           in
        let uu____14738 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____14728 uu____14729 uu____14738
    | uu____14741 when is_list e ->
        let uu____14742 =
          let uu____14743 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____14744 = extract_from_list e  in
          separate_map_or_flow_last uu____14743
            (fun ps  -> p_noSeqTermAndComment ps false) uu____14744
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____14742 FStar_Pprint.rbracket
    | uu____14759 when is_lex_list e ->
        let uu____14760 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____14761 =
          let uu____14762 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____14763 = extract_from_list e  in
          separate_map_or_flow_last uu____14762
            (fun ps  -> p_noSeqTermAndComment ps false) uu____14763
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____14760 uu____14761 FStar_Pprint.rbracket
    | uu____14778 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____14785 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____14786 =
          let uu____14787 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____14787 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____14785 uu____14786 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____14806 = str (Prims.op_Hat "(*" (Prims.op_Hat s "*)"))  in
        let uu____14809 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____14806 uu____14809
    | FStar_Parser_AST.Op (op,args) when
        let uu____14828 = handleable_op op args  in
        Prims.op_Negation uu____14828 ->
        let uu____14833 =
          let uu____14835 =
            let uu____14837 = FStar_Ident.text_of_id op  in
            let uu____14839 =
              let uu____14841 =
                let uu____14843 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.op_Hat uu____14843
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.op_Hat " with " uu____14841  in
            Prims.op_Hat uu____14837 uu____14839  in
          Prims.op_Hat "Operation " uu____14835  in
        failwith uu____14833
    | FStar_Parser_AST.Uvar id1 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____14855 = p_term false false e  in
        soft_parens_with_nesting uu____14855
    | FStar_Parser_AST.Const uu____14858 ->
        let uu____14859 = p_term false false e  in
        soft_parens_with_nesting uu____14859
    | FStar_Parser_AST.Op uu____14862 ->
        let uu____14874 = p_term false false e  in
        soft_parens_with_nesting uu____14874
    | FStar_Parser_AST.Tvar uu____14877 ->
        let uu____14880 = p_term false false e  in
        soft_parens_with_nesting uu____14880
    | FStar_Parser_AST.Var uu____14883 ->
        let uu____14888 = p_term false false e  in
        soft_parens_with_nesting uu____14888
    | FStar_Parser_AST.Name uu____14891 ->
        let uu____14896 = p_term false false e  in
        soft_parens_with_nesting uu____14896
    | FStar_Parser_AST.Construct uu____14899 ->
        let uu____14917 = p_term false false e  in
        soft_parens_with_nesting uu____14917
    | FStar_Parser_AST.Abs uu____14920 ->
        let uu____14932 = p_term false false e  in
        soft_parens_with_nesting uu____14932
    | FStar_Parser_AST.App uu____14935 ->
        let uu____14948 = p_term false false e  in
        soft_parens_with_nesting uu____14948
    | FStar_Parser_AST.Let uu____14951 ->
        let uu____14983 = p_term false false e  in
        soft_parens_with_nesting uu____14983
    | FStar_Parser_AST.LetOpen uu____14986 ->
        let uu____14998 = p_term false false e  in
        soft_parens_with_nesting uu____14998
    | FStar_Parser_AST.Seq uu____15001 ->
        let uu____15012 = p_term false false e  in
        soft_parens_with_nesting uu____15012
    | FStar_Parser_AST.Bind uu____15015 ->
        let uu____15030 = p_term false false e  in
        soft_parens_with_nesting uu____15030
    | FStar_Parser_AST.If uu____15033 ->
        let uu____15049 = p_term false false e  in
        soft_parens_with_nesting uu____15049
    | FStar_Parser_AST.Match uu____15052 ->
        let uu____15078 = p_term false false e  in
        soft_parens_with_nesting uu____15078
    | FStar_Parser_AST.TryWith uu____15081 ->
        let uu____15107 = p_term false false e  in
        soft_parens_with_nesting uu____15107
    | FStar_Parser_AST.Ascribed uu____15110 ->
        let uu____15128 = p_term false false e  in
        soft_parens_with_nesting uu____15128
    | FStar_Parser_AST.Record uu____15131 ->
        let uu____15154 = p_term false false e  in
        soft_parens_with_nesting uu____15154
    | FStar_Parser_AST.Project uu____15157 ->
        let uu____15169 = p_term false false e  in
        soft_parens_with_nesting uu____15169
    | FStar_Parser_AST.Product uu____15172 ->
        let uu____15186 = p_term false false e  in
        soft_parens_with_nesting uu____15186
    | FStar_Parser_AST.Sum uu____15189 ->
        let uu____15210 = p_term false false e  in
        soft_parens_with_nesting uu____15210
    | FStar_Parser_AST.QForall uu____15213 ->
        let uu____15244 = p_term false false e  in
        soft_parens_with_nesting uu____15244
    | FStar_Parser_AST.QExists uu____15247 ->
        let uu____15278 = p_term false false e  in
        soft_parens_with_nesting uu____15278
    | FStar_Parser_AST.Refine uu____15281 ->
        let uu____15293 = p_term false false e  in
        soft_parens_with_nesting uu____15293
    | FStar_Parser_AST.NamedTyp uu____15296 ->
        let uu____15306 = p_term false false e  in
        soft_parens_with_nesting uu____15306
    | FStar_Parser_AST.Requires uu____15309 ->
        let uu____15320 = p_term false false e  in
        soft_parens_with_nesting uu____15320
    | FStar_Parser_AST.Ensures uu____15323 ->
        let uu____15334 = p_term false false e  in
        soft_parens_with_nesting uu____15334
    | FStar_Parser_AST.Attributes uu____15337 ->
        let uu____15343 = p_term false false e  in
        soft_parens_with_nesting uu____15343
    | FStar_Parser_AST.Quote uu____15346 ->
        let uu____15354 = p_term false false e  in
        soft_parens_with_nesting uu____15354
    | FStar_Parser_AST.VQuote uu____15357 ->
        let uu____15361 = p_term false false e  in
        soft_parens_with_nesting uu____15361
    | FStar_Parser_AST.Antiquote uu____15364 ->
        let uu____15368 = p_term false false e  in
        soft_parens_with_nesting uu____15368
    | FStar_Parser_AST.CalcProof uu____15371 ->
        let uu____15387 = p_term false false e  in
        soft_parens_with_nesting uu____15387

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___15_15390  ->
    match uu___15_15390 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_real r -> str (Prims.op_Hat r "R")
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____15402) ->
        let uu____15405 = str (FStar_String.escaped s)  in
        FStar_Pprint.dquotes uu____15405
    | FStar_Const.Const_bytearray (bytes,uu____15407) ->
        let uu____15412 =
          let uu____15413 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____15413  in
        let uu____15414 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____15412 uu____15414
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___13_15437 =
          match uu___13_15437 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___14_15444 =
          match uu___14_15444 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____15459  ->
               match uu____15459 with
               | (s,w) ->
                   let uu____15466 = signedness s  in
                   let uu____15467 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____15466 uu____15467)
            sign_width_opt
           in
        let uu____15468 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____15468 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____15472 = FStar_Range.string_of_range r  in str uu____15472
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____15480 = p_quident lid  in
        let uu____15481 =
          let uu____15482 =
            let uu____15483 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____15483  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____15482  in
        FStar_Pprint.op_Hat_Hat uu____15480 uu____15481

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____15489 = str "u#"  in
    let uu____15491 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____15489 uu____15491

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____15496;_},u1::u2::[])
        ->
        let uu____15522 =
          let uu____15523 = p_universeFrom u1  in
          let uu____15524 =
            let uu____15525 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____15525  in
          FStar_Pprint.op_Hat_Slash_Hat uu____15523 uu____15524  in
        FStar_Pprint.group uu____15522
    | FStar_Parser_AST.App uu____15526 ->
        let uu____15539 = head_and_args u  in
        (match uu____15539 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____15587 =
                    let uu____15588 = p_qlident FStar_Parser_Const.max_lid
                       in
                    let uu____15589 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____15600  ->
                           match uu____15600 with
                           | (u1,uu____15609) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____15588 uu____15589  in
                  FStar_Pprint.group uu____15587
              | uu____15616 ->
                  let uu____15617 =
                    let uu____15619 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____15619
                     in
                  failwith uu____15617))
    | uu____15622 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____15653 = FStar_Ident.text_of_id id1  in str uu____15653
    | FStar_Parser_AST.Paren u1 ->
        let uu____15659 = p_universeFrom u1  in
        soft_parens_with_nesting uu____15659
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____15660;_},uu____15661::uu____15662::[])
        ->
        let uu____15686 = p_universeFrom u  in
        soft_parens_with_nesting uu____15686
    | FStar_Parser_AST.App uu____15687 ->
        let uu____15700 = p_universeFrom u  in
        soft_parens_with_nesting uu____15700
    | uu____15701 ->
        let uu____15702 =
          let uu____15704 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s"
            uu____15704
           in
        failwith uu____15702

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
       | FStar_Parser_AST.Module (uu____15831,decls) ->
           let uu____15855 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____15855
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____15874,decls,uu____15876) ->
           let uu____15901 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____15901
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string * FStar_Range.range) Prims.list -> FStar_Pprint.document) =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____15971  ->
         match uu____15971 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____16013)) -> false
      | ([],uu____16027) -> false
      | uu____16031 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____16044 -> true
         | uu____16046 -> false)
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
        | FStar_Parser_AST.Module (uu____16099,decls) -> decls
        | FStar_Parser_AST.Interface (uu____16123,decls,uu____16125) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____16215 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____16238;
                 FStar_Parser_AST.doc = uu____16239;
                 FStar_Parser_AST.quals = uu____16240;
                 FStar_Parser_AST.attrs = uu____16241;_}::uu____16242 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____16273 =
                   let uu____16281 =
                     let uu____16289 = FStar_List.tl ds  in d :: uu____16289
                      in
                   d0 :: uu____16281  in
                 (uu____16273, (d0.FStar_Parser_AST.drange))
             | uu____16319 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____16215 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____16401 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____16401 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____16515 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____16515, comments1))))))
  