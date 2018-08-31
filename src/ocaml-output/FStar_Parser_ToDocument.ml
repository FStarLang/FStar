open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____37 'Auu____38 .
    Prims.bool -> ('Auu____37 -> 'Auu____38) -> 'Auu____37 -> 'Auu____38
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
  'Auu____135 'Auu____136 .
    'Auu____135 ->
      ('Auu____136 -> 'Auu____135) ->
        'Auu____136 FStar_Pervasives_Native.option -> 'Auu____135
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
  'Auu____230 .
    FStar_Pprint.document ->
      ('Auu____230 -> FStar_Pprint.document) ->
        'Auu____230 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____255 =
          let uu____256 =
            let uu____257 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____257  in
          FStar_Pprint.separate_map uu____256 f l  in
        FStar_Pprint.group uu____255
  
let precede_break_separate_map :
  'Auu____268 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____268 -> FStar_Pprint.document) ->
          'Auu____268 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____298 =
            let uu____299 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____300 =
              let uu____301 = FStar_List.hd l  in
              FStar_All.pipe_right uu____301 f  in
            FStar_Pprint.precede uu____299 uu____300  in
          let uu____302 =
            let uu____303 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____309 =
                   let uu____310 =
                     let uu____311 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____311  in
                   FStar_Pprint.op_Hat_Hat sep uu____310  in
                 FStar_Pprint.op_Hat_Hat break1 uu____309) uu____303
             in
          FStar_Pprint.op_Hat_Hat uu____298 uu____302
  
let concat_break_map :
  'Auu____318 .
    ('Auu____318 -> FStar_Pprint.document) ->
      'Auu____318 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____338 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____342 = f x  in FStar_Pprint.op_Hat_Hat uu____342 break1)
          l
         in
      FStar_Pprint.group uu____338
  
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
    let uu____383 = str "begin"  in
    let uu____384 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____383 contents uu____384
  
let separate_map_last :
  'Auu____393 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____393 -> FStar_Pprint.document) ->
        'Auu____393 Prims.list -> FStar_Pprint.document
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
  'Auu____445 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____445 -> FStar_Pprint.document) ->
        'Auu____445 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____475 =
          let uu____476 =
            let uu____477 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____477  in
          separate_map_last uu____476 f l  in
        FStar_Pprint.group uu____475
  
let separate_map_or_flow :
  'Auu____486 .
    FStar_Pprint.document ->
      ('Auu____486 -> FStar_Pprint.document) ->
        'Auu____486 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____520 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____520 -> FStar_Pprint.document) ->
        'Auu____520 Prims.list -> FStar_Pprint.document
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
  'Auu____572 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____572 -> FStar_Pprint.document) ->
        'Auu____572 Prims.list -> FStar_Pprint.document
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
              let uu____642 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____642
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____662 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____662 -> FStar_Pprint.document) ->
                  'Auu____662 Prims.list -> FStar_Pprint.document
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
                    (let uu____715 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____715
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____734 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____734 -> FStar_Pprint.document) ->
                  'Auu____734 Prims.list -> FStar_Pprint.document
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
                    (let uu____787 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____787
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____802  ->
    match uu____802 with
    | (comment,keywords) ->
        let uu____827 =
          let uu____828 =
            let uu____831 = str comment  in
            let uu____832 =
              let uu____835 =
                let uu____838 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____847  ->
                       match uu____847 with
                       | (k,v1) ->
                           let uu____854 =
                             let uu____857 = str k  in
                             let uu____858 =
                               let uu____861 =
                                 let uu____864 = str v1  in [uu____864]  in
                               FStar_Pprint.rarrow :: uu____861  in
                             uu____857 :: uu____858  in
                           FStar_Pprint.concat uu____854) keywords
                   in
                [uu____838]  in
              FStar_Pprint.space :: uu____835  in
            uu____831 :: uu____832  in
          FStar_Pprint.concat uu____828  in
        FStar_Pprint.group uu____827
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____870 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____882 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____882
      | uu____883 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____925::(e2,uu____927)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____950 -> false  in
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
    | FStar_Parser_AST.Construct (uu____968,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____979,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____1000 = extract_from_list e2  in e1 :: uu____1000
    | uu____1003 ->
        let uu____1004 =
          let uu____1005 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1005  in
        failwith uu____1004
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1014;
           FStar_Parser_AST.level = uu____1015;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1017 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1025;
           FStar_Parser_AST.level = uu____1026;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1028;
                                                         FStar_Parser_AST.level
                                                           = uu____1029;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1031;
                                                    FStar_Parser_AST.level =
                                                      uu____1032;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1034;
                FStar_Parser_AST.level = uu____1035;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1037;
           FStar_Parser_AST.level = uu____1038;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1040 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1050 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1051;
           FStar_Parser_AST.range = uu____1052;
           FStar_Parser_AST.level = uu____1053;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1054;
                                                         FStar_Parser_AST.range
                                                           = uu____1055;
                                                         FStar_Parser_AST.level
                                                           = uu____1056;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1058;
                                                    FStar_Parser_AST.level =
                                                      uu____1059;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1060;
                FStar_Parser_AST.range = uu____1061;
                FStar_Parser_AST.level = uu____1062;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1064;
           FStar_Parser_AST.level = uu____1065;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1067 = extract_from_ref_set e1  in
        let uu____1070 = extract_from_ref_set e2  in
        FStar_List.append uu____1067 uu____1070
    | uu____1073 ->
        let uu____1074 =
          let uu____1075 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1075  in
        failwith uu____1074
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1083 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1083
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1089 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1089
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1097 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1097 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1105 = FStar_Ident.text_of_id op  in uu____1105 <> "~"))
  
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
      | uu____1171 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1187 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1193 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1199 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___105_1220  ->
    match uu___105_1220 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___106_1245  ->
      match uu___106_1245 with
      | FStar_Util.Inl c ->
          let uu____1254 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1254 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1265 .
    Prims.string ->
      ('Auu____1265,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1286  ->
      match uu____1286 with
      | (assoc_levels,tokens) ->
          let uu____1314 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1314 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___107_1432 =
    match uu___107_1432 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1462  ->
         match uu____1462 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1521 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1521 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1561) ->
          assoc_levels
      | uu____1590 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1626 .
    ('Auu____1626,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1671 =
        FStar_List.tryFind
          (fun uu____1701  ->
             match uu____1701 with
             | (uu____1714,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1671 with
      | FStar_Pervasives_Native.Some ((uu____1736,l1,uu____1738),uu____1739)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1774 =
            let uu____1775 =
              let uu____1776 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1776  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1775
             in
          failwith uu____1774
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1798 = assign_levels level_associativity_spec op  in
    match uu____1798 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1828 =
      let uu____1831 =
        let uu____1836 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1836  in
      FStar_List.tryFind uu____1831 operatorInfix0ad12  in
    uu____1828 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1894 =
      let uu____1908 =
        let uu____1924 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1924  in
      FStar_List.tryFind uu____1908 opinfix34  in
    uu____1894 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1980 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1980
    then (Prims.parse_int "1")
    else
      (let uu____1982 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1982
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____1991 . FStar_Ident.ident -> 'Auu____1991 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2007 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2007 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2009 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2009
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2010 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2010 [".()<-"; ".[]<-"]
      | uu____2011 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2049 .
    ('Auu____2049 -> FStar_Pprint.document) ->
      'Auu____2049 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2090 = FStar_ST.op_Bang comment_stack  in
          match uu____2090 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2149 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2149
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2186 =
                    let uu____2187 =
                      let uu____2188 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2188
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2187  in
                  comments_before_pos uu____2186 print_pos lookahead_pos))
              else
                (let uu____2190 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2190))
           in
        let uu____2191 =
          let uu____2196 =
            let uu____2197 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2197  in
          let uu____2198 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2196 uu____2198  in
        match uu____2191 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2204 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2204
              else comments  in
            let uu____2210 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2210
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2231 = FStar_ST.op_Bang comment_stack  in
          match uu____2231 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2315 =
                    let uu____2316 =
                      let uu____2317 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2317  in
                    uu____2316 - lbegin  in
                  max k uu____2315  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2320 =
                    let uu____2321 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2322 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2321 uu____2322  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2320  in
                let uu____2323 =
                  let uu____2324 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2324  in
                place_comments_until_pos (Prims.parse_int "1") uu____2323
                  pos_end doc2))
          | uu____2325 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2334 =
                     let uu____2335 = FStar_Range.line_of_pos pos_end  in
                     uu____2335 - lbegin  in
                   max (Prims.parse_int "1") uu____2334  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2337 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2337)
  
let separate_map_with_comments :
  'Auu____2350 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2350 -> FStar_Pprint.document) ->
          'Auu____2350 Prims.list ->
            ('Auu____2350 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2407 x =
              match uu____2407 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2421 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2421 doc1
                     in
                  let uu____2422 =
                    let uu____2423 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2423  in
                  let uu____2424 =
                    let uu____2425 =
                      let uu____2426 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2426  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2425  in
                  (uu____2422, uu____2424)
               in
            let uu____2427 =
              let uu____2434 = FStar_List.hd xs  in
              let uu____2435 = FStar_List.tl xs  in (uu____2434, uu____2435)
               in
            match uu____2427 with
            | (x,xs1) ->
                let init1 =
                  let uu____2451 =
                    let uu____2452 =
                      let uu____2453 = extract_range x  in
                      FStar_Range.end_of_range uu____2453  in
                    FStar_Range.line_of_pos uu____2452  in
                  let uu____2454 =
                    let uu____2455 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2455  in
                  (uu____2451, uu____2454)  in
                let uu____2456 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2456
  
let separate_map_with_comments_kw :
  'Auu____2479 'Auu____2480 .
    'Auu____2479 ->
      'Auu____2479 ->
        ('Auu____2479 -> 'Auu____2480 -> FStar_Pprint.document) ->
          'Auu____2480 Prims.list ->
            ('Auu____2480 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2542 x =
              match uu____2542 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2556 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2556 doc1
                     in
                  let uu____2557 =
                    let uu____2558 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2558  in
                  let uu____2559 =
                    let uu____2560 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2560  in
                  (uu____2557, uu____2559)
               in
            let uu____2561 =
              let uu____2568 = FStar_List.hd xs  in
              let uu____2569 = FStar_List.tl xs  in (uu____2568, uu____2569)
               in
            match uu____2561 with
            | (x,xs1) ->
                let init1 =
                  let uu____2585 =
                    let uu____2586 =
                      let uu____2587 = extract_range x  in
                      FStar_Range.end_of_range uu____2587  in
                    FStar_Range.line_of_pos uu____2586  in
                  let uu____2588 = f prefix1 x  in (uu____2585, uu____2588)
                   in
                let uu____2589 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2589
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3299)) ->
          let uu____3302 =
            let uu____3303 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3303 FStar_Util.is_upper  in
          if uu____3302
          then
            let uu____3306 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3306 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3308 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3315 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3316 =
      let uu____3317 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3318 =
        let uu____3319 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3319  in
      FStar_Pprint.op_Hat_Hat uu____3317 uu____3318  in
    FStar_Pprint.op_Hat_Hat uu____3315 uu____3316

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3321 ->
        let uu____3322 =
          let uu____3323 = str "@ "  in
          let uu____3324 =
            let uu____3325 =
              let uu____3326 =
                let uu____3327 =
                  let uu____3328 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3328  in
                FStar_Pprint.op_Hat_Hat uu____3327 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3326  in
            FStar_Pprint.op_Hat_Hat uu____3325 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3323 uu____3324  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3322

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3331  ->
    match uu____3331 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3367 =
                match uu____3367 with
                | (kwd,arg) ->
                    let uu____3374 = str "@"  in
                    let uu____3375 =
                      let uu____3376 = str kwd  in
                      let uu____3377 =
                        let uu____3378 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3378
                         in
                      FStar_Pprint.op_Hat_Hat uu____3376 uu____3377  in
                    FStar_Pprint.op_Hat_Hat uu____3374 uu____3375
                 in
              let uu____3379 =
                let uu____3380 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3380 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3379
           in
        let uu____3385 =
          let uu____3386 =
            let uu____3387 =
              let uu____3388 =
                let uu____3389 = str doc1  in
                let uu____3390 =
                  let uu____3391 =
                    let uu____3392 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3392  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3391  in
                FStar_Pprint.op_Hat_Hat uu____3389 uu____3390  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3388  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3387  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3386  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3385

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3396 =
          let uu____3397 = str "val"  in
          let uu____3398 =
            let uu____3399 =
              let uu____3400 = p_lident lid  in
              let uu____3401 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3400 uu____3401  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3399  in
          FStar_Pprint.op_Hat_Hat uu____3397 uu____3398  in
        let uu____3402 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3396 uu____3402
    | FStar_Parser_AST.TopLevelLet (uu____3403,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3428 =
               let uu____3429 = str "let"  in p_letlhs uu____3429 lb  in
             FStar_Pprint.group uu____3428) lbs
    | uu____3430 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___108_3445 =
          match uu___108_3445 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3453 = f x  in
              let uu____3454 =
                let uu____3455 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3455  in
              FStar_Pprint.op_Hat_Hat uu____3453 uu____3454
           in
        let uu____3456 = str "["  in
        let uu____3457 =
          let uu____3458 = p_list' l  in
          let uu____3459 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3458 uu____3459  in
        FStar_Pprint.op_Hat_Hat uu____3456 uu____3457

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3462 =
          let uu____3463 = str "open"  in
          let uu____3464 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3463 uu____3464  in
        FStar_Pprint.group uu____3462
    | FStar_Parser_AST.Include uid ->
        let uu____3466 =
          let uu____3467 = str "include"  in
          let uu____3468 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3467 uu____3468  in
        FStar_Pprint.group uu____3466
    | FStar_Parser_AST.Friend uid ->
        let uu____3470 =
          let uu____3471 = str "friend"  in
          let uu____3472 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3471 uu____3472  in
        FStar_Pprint.group uu____3470
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3475 =
          let uu____3476 = str "module"  in
          let uu____3477 =
            let uu____3478 =
              let uu____3479 = p_uident uid1  in
              let uu____3480 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3479 uu____3480  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3478  in
          FStar_Pprint.op_Hat_Hat uu____3476 uu____3477  in
        let uu____3481 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3475 uu____3481
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3483 =
          let uu____3484 = str "module"  in
          let uu____3485 =
            let uu____3486 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3486  in
          FStar_Pprint.op_Hat_Hat uu____3484 uu____3485  in
        FStar_Pprint.group uu____3483
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3487,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3520 = str "effect"  in
          let uu____3521 =
            let uu____3522 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3522  in
          FStar_Pprint.op_Hat_Hat uu____3520 uu____3521  in
        let uu____3523 =
          let uu____3524 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3524 FStar_Pprint.equals
           in
        let uu____3525 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3523 uu____3525
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3546 =
          let uu____3547 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3547  in
        let uu____3560 =
          let uu____3561 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3599 =
                    let uu____3600 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3600 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3599)) uu____3561
           in
        FStar_Pprint.op_Hat_Hat uu____3546 uu____3560
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3616 = str "let"  in
          let uu____3617 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3616 uu____3617  in
        let uu____3618 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3618 p_letbinding lbs
          (fun uu____3626  ->
             match uu____3626 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3635 = str "val"  in
        let uu____3636 =
          let uu____3637 =
            let uu____3638 = p_lident lid  in
            let uu____3639 =
              let uu____3640 =
                let uu____3641 =
                  let uu____3642 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3642  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3641  in
              FStar_Pprint.group uu____3640  in
            FStar_Pprint.op_Hat_Hat uu____3638 uu____3639  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3637  in
        FStar_Pprint.op_Hat_Hat uu____3635 uu____3636
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3646 =
            let uu____3647 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3647 FStar_Util.is_upper  in
          if uu____3646
          then FStar_Pprint.empty
          else
            (let uu____3651 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3651 FStar_Pprint.space)
           in
        let uu____3652 =
          let uu____3653 = p_ident id1  in
          let uu____3654 =
            let uu____3655 =
              let uu____3656 =
                let uu____3657 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3657  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3656  in
            FStar_Pprint.group uu____3655  in
          FStar_Pprint.op_Hat_Hat uu____3653 uu____3654  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3652
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3664 = str "exception"  in
        let uu____3665 =
          let uu____3666 =
            let uu____3667 = p_uident uid  in
            let uu____3668 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3672 =
                     let uu____3673 = str "of"  in
                     let uu____3674 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3673 uu____3674  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3672) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3667 uu____3668  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3666  in
        FStar_Pprint.op_Hat_Hat uu____3664 uu____3665
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3676 = str "new_effect"  in
        let uu____3677 =
          let uu____3678 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3678  in
        FStar_Pprint.op_Hat_Hat uu____3676 uu____3677
    | FStar_Parser_AST.SubEffect se ->
        let uu____3680 = str "sub_effect"  in
        let uu____3681 =
          let uu____3682 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3682  in
        FStar_Pprint.op_Hat_Hat uu____3680 uu____3681
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3685 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3685 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3686 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3687,uu____3688) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3711 = str "%splice"  in
        let uu____3712 =
          let uu____3713 =
            let uu____3714 = str ";"  in p_list p_uident uu____3714 ids  in
          let uu____3715 =
            let uu____3716 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3716  in
          FStar_Pprint.op_Hat_Hat uu____3713 uu____3715  in
        FStar_Pprint.op_Hat_Hat uu____3711 uu____3712

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___109_3717  ->
    match uu___109_3717 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3719 = str "#set-options"  in
        let uu____3720 =
          let uu____3721 =
            let uu____3722 = str s  in FStar_Pprint.dquotes uu____3722  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3721  in
        FStar_Pprint.op_Hat_Hat uu____3719 uu____3720
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3726 = str "#reset-options"  in
        let uu____3727 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3731 =
                 let uu____3732 = str s  in FStar_Pprint.dquotes uu____3732
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3731) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3726 uu____3727
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3736 = str "#push-options"  in
        let uu____3737 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3741 =
                 let uu____3742 = str s  in FStar_Pprint.dquotes uu____3742
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3741) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3736 uu____3737
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
    fun uu____3767  ->
      match uu____3767 with
      | (typedecl,fsdoc_opt) ->
          let uu____3780 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3780 with
           | (decl,body) ->
               let uu____3798 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3798)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___110_3800  ->
      match uu___110_3800 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3830 = FStar_Pprint.empty  in
          let uu____3831 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3831, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3852 =
            let uu____3853 = p_typ false false t  in jump2 uu____3853  in
          let uu____3854 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3854, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3908 =
            match uu____3908 with
            | (lid1,t,doc_opt) ->
                let uu____3924 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3924
             in
          let p_fields uu____3940 =
            let uu____3941 =
              let uu____3942 =
                let uu____3943 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3943 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3942  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3941  in
          let uu____3952 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3952, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4013 =
            match uu____4013 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4039 =
                    let uu____4040 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4040  in
                  FStar_Range.extend_to_end_of_line uu____4039  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4066 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4079 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4079,
            ((fun uu____4085  ->
                let uu____4086 = datacon_doc ()  in jump2 uu____4086)))

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
  fun uu____4087  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4087 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4121 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4121  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4123 =
                        let uu____4126 =
                          let uu____4129 = p_fsdoc fsdoc  in
                          let uu____4130 =
                            let uu____4133 = cont lid_doc  in [uu____4133]
                             in
                          uu____4129 :: uu____4130  in
                        kw :: uu____4126  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4123
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4138 =
                        let uu____4139 =
                          let uu____4140 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4140 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4139
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4138
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4155 =
                          let uu____4156 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4156  in
                        prefix2 uu____4155 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4158  ->
      match uu____4158 with
      | (lid,t,doc_opt) ->
          let uu____4174 =
            let uu____4175 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4176 =
              let uu____4177 = p_lident lid  in
              let uu____4178 =
                let uu____4179 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4179  in
              FStar_Pprint.op_Hat_Hat uu____4177 uu____4178  in
            FStar_Pprint.op_Hat_Hat uu____4175 uu____4176  in
          FStar_Pprint.group uu____4174

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4180  ->
    match uu____4180 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4208 =
            let uu____4209 =
              let uu____4210 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4210  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4209  in
          FStar_Pprint.group uu____4208  in
        let uu____4211 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4212 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4216 =
                 let uu____4217 =
                   let uu____4218 =
                     let uu____4219 =
                       let uu____4220 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4220
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4219  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4218  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4217  in
               FStar_Pprint.group uu____4216) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4211 uu____4212

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4222  ->
      match uu____4222 with
      | (pat,uu____4228) ->
          let uu____4229 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4248 =
                  let uu____4249 =
                    let uu____4250 =
                      let uu____4251 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4251
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4250  in
                  FStar_Pprint.group uu____4249  in
                (pat1, uu____4248)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4263 =
                  let uu____4264 =
                    let uu____4265 =
                      let uu____4266 =
                        let uu____4267 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4267
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4266
                       in
                    FStar_Pprint.group uu____4265  in
                  let uu____4268 =
                    let uu____4269 =
                      let uu____4270 = str "by"  in
                      let uu____4271 =
                        let uu____4272 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4272
                         in
                      FStar_Pprint.op_Hat_Hat uu____4270 uu____4271  in
                    FStar_Pprint.group uu____4269  in
                  FStar_Pprint.op_Hat_Hat uu____4264 uu____4268  in
                (pat1, uu____4263)
            | uu____4273 -> (pat, FStar_Pprint.empty)  in
          (match uu____4229 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4277);
                       FStar_Parser_AST.prange = uu____4278;_},pats)
                    ->
                    let uu____4288 =
                      let uu____4289 =
                        let uu____4290 =
                          let uu____4291 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4291  in
                        FStar_Pprint.group uu____4290  in
                      let uu____4292 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4289 uu____4292  in
                    prefix2_nonempty uu____4288 ascr_doc
                | uu____4293 ->
                    let uu____4294 =
                      let uu____4295 =
                        let uu____4296 =
                          let uu____4297 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4297  in
                        FStar_Pprint.group uu____4296  in
                      FStar_Pprint.op_Hat_Hat uu____4295 ascr_doc  in
                    FStar_Pprint.group uu____4294))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4299  ->
      match uu____4299 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4308 =
            let uu____4309 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4309  in
          let uu____4310 =
            let uu____4311 =
              let uu____4312 =
                let uu____4313 =
                  let uu____4314 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4314  in
                FStar_Pprint.group uu____4313  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4312  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4311  in
          FStar_Pprint.ifflat uu____4308 uu____4310

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___111_4315  ->
    match uu___111_4315 with
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
        let uu____4340 = p_uident uid  in
        let uu____4341 = p_binders true bs  in
        let uu____4342 =
          let uu____4343 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4343  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4340 uu____4341 uu____4342

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
          let uu____4353 =
            let uu____4354 =
              let uu____4355 =
                let uu____4356 = p_uident uid  in
                let uu____4357 = p_binders true bs  in
                let uu____4358 =
                  let uu____4359 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4359  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4356 uu____4357 uu____4358
                 in
              FStar_Pprint.group uu____4355  in
            let uu____4360 =
              let uu____4361 = str "with"  in
              let uu____4362 =
                let uu____4363 =
                  let uu____4364 =
                    let uu____4365 =
                      let uu____4366 =
                        let uu____4367 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4367
                         in
                      separate_map_last uu____4366 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4365  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4364  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4363  in
              FStar_Pprint.op_Hat_Hat uu____4361 uu____4362  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4354 uu____4360  in
          braces_with_nesting uu____4353

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4370,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4399 =
            let uu____4400 = p_lident lid  in
            let uu____4401 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4400 uu____4401  in
          let uu____4402 = p_simpleTerm ps false e  in
          prefix2 uu____4399 uu____4402
      | uu____4403 ->
          let uu____4404 =
            let uu____4405 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4405
             in
          failwith uu____4404

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4467 =
        match uu____4467 with
        | (kwd,t) ->
            let uu____4474 =
              let uu____4475 = str kwd  in
              let uu____4476 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4475 uu____4476  in
            let uu____4477 = p_simpleTerm ps false t  in
            prefix2 uu____4474 uu____4477
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4482 =
      let uu____4483 =
        let uu____4484 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4485 =
          let uu____4486 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4486  in
        FStar_Pprint.op_Hat_Hat uu____4484 uu____4485  in
      let uu____4487 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4483 uu____4487  in
    let uu____4488 =
      let uu____4489 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4489  in
    FStar_Pprint.op_Hat_Hat uu____4482 uu____4488

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___112_4490  ->
    match uu___112_4490 with
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
    | uu____4492 ->
        let uu____4493 =
          let uu____4494 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4494  in
        FStar_Pprint.op_Hat_Hat uu____4493 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___113_4497  ->
    match uu___113_4497 with
    | FStar_Parser_AST.Rec  ->
        let uu____4498 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4498
    | FStar_Parser_AST.Mutable  ->
        let uu____4499 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4499
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___114_4500  ->
    match uu___114_4500 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4502 = str "#["  in
        let uu____4503 =
          let uu____4504 = p_term false false t  in
          let uu____4505 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4504 uu____4505  in
        FStar_Pprint.op_Hat_Hat uu____4502 uu____4503

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4510 =
          let uu____4511 =
            let uu____4512 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4512  in
          FStar_Pprint.separate_map uu____4511 p_tuplePattern pats  in
        FStar_Pprint.group uu____4510
    | uu____4513 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4520 =
          let uu____4521 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4521 p_constructorPattern pats  in
        FStar_Pprint.group uu____4520
    | uu____4522 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4525;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4530 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4531 = p_constructorPattern hd1  in
        let uu____4532 = p_constructorPattern tl1  in
        infix0 uu____4530 uu____4531 uu____4532
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4534;_},pats)
        ->
        let uu____4540 = p_quident uid  in
        let uu____4541 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4540 uu____4541
    | uu____4542 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4558;
               FStar_Parser_AST.blevel = uu____4559;
               FStar_Parser_AST.aqual = uu____4560;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4568 =
               let uu____4569 = p_ident lid  in
               p_refinement aqual uu____4569 t1 phi  in
             soft_parens_with_nesting uu____4568
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4572;
               FStar_Parser_AST.blevel = uu____4573;
               FStar_Parser_AST.aqual = uu____4574;_},phi))
             ->
             let uu____4580 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4580
         | uu____4581 ->
             let uu____4586 =
               let uu____4587 = p_tuplePattern pat  in
               let uu____4588 =
                 let uu____4589 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4589
                  in
               FStar_Pprint.op_Hat_Hat uu____4587 uu____4588  in
             soft_parens_with_nesting uu____4586)
    | FStar_Parser_AST.PatList pats ->
        let uu____4593 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4593 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4610 =
          match uu____4610 with
          | (lid,pat) ->
              let uu____4617 = p_qlident lid  in
              let uu____4618 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4617 uu____4618
           in
        let uu____4619 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4619
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4629 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4630 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4631 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4629 uu____4630 uu____4631
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4640 =
          let uu____4641 =
            let uu____4642 =
              let uu____4643 = FStar_Ident.text_of_id op  in str uu____4643
               in
            let uu____4644 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4642 uu____4644  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4641  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4640
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4648 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4648 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4656 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4657 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4656 uu____4657
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4659 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4662;
           FStar_Parser_AST.prange = uu____4663;_},uu____4664)
        ->
        let uu____4669 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4669
    | FStar_Parser_AST.PatTuple (uu____4670,false ) ->
        let uu____4675 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4675
    | uu____4676 ->
        let uu____4677 =
          let uu____4678 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4678  in
        failwith uu____4677

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4680;_},uu____4681)
        -> true
    | uu____4686 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4690 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4691 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4690 uu____4691
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4698;
                   FStar_Parser_AST.blevel = uu____4699;
                   FStar_Parser_AST.aqual = uu____4700;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4704 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4704 t1 phi
            | uu____4705 ->
                let t' =
                  let uu____4707 = is_typ_tuple t  in
                  if uu____4707
                  then
                    let uu____4708 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4708
                  else p_tmFormula t  in
                let uu____4710 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4711 =
                  let uu____4712 = p_lident lid  in
                  let uu____4713 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4712 uu____4713  in
                FStar_Pprint.op_Hat_Hat uu____4710 uu____4711
             in
          if is_atomic
          then
            let uu____4714 =
              let uu____4715 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4715  in
            FStar_Pprint.group uu____4714
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4717 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4724;
                  FStar_Parser_AST.blevel = uu____4725;
                  FStar_Parser_AST.aqual = uu____4726;_},phi)
               ->
               if is_atomic
               then
                 let uu____4730 =
                   let uu____4731 =
                     let uu____4732 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4732 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4731  in
                 FStar_Pprint.group uu____4730
               else
                 (let uu____4734 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4734)
           | uu____4735 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____4744 -> false
            | FStar_Parser_AST.App uu____4755 -> false
            | FStar_Parser_AST.Op uu____4762 -> false
            | uu____4769 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4773 =
            let uu____4774 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4775 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4774 uu____4775  in
          let uu____4776 =
            let uu____4777 = p_appTerm t  in
            let uu____4778 =
              let uu____4779 =
                let uu____4780 =
                  let uu____4781 = soft_braces_with_nesting_tight phi1  in
                  let uu____4782 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4781 uu____4782  in
                FStar_Pprint.group uu____4780  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4779
               in
            FStar_Pprint.op_Hat_Hat uu____4777 uu____4778  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4773 uu____4776

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4793 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4793

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4798 = FStar_Ident.text_of_id lid  in str uu____4798)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4801 = FStar_Ident.text_of_lid lid  in str uu____4801)

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

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____4819 =
              let uu____4820 =
                let uu____4821 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4821 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4820  in
            let uu____4822 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4819 uu____4822
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4826 =
              let uu____4827 =
                let uu____4828 =
                  let uu____4829 = p_lident x  in
                  let uu____4830 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4829 uu____4830  in
                let uu____4831 =
                  let uu____4832 = p_noSeqTerm true false e1  in
                  let uu____4833 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4832 uu____4833  in
                op_Hat_Slash_Plus_Hat uu____4828 uu____4831  in
              FStar_Pprint.group uu____4827  in
            let uu____4834 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4826 uu____4834
        | uu____4835 ->
            let uu____4836 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4836

and (p_noSeqTerm :
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
            let uu____4847 =
              let uu____4848 = p_tmIff e1  in
              let uu____4849 =
                let uu____4850 =
                  let uu____4851 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4851
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4850  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4848 uu____4849  in
            FStar_Pprint.group uu____4847
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4857 =
              let uu____4858 = p_tmIff e1  in
              let uu____4859 =
                let uu____4860 =
                  let uu____4861 =
                    let uu____4862 = p_typ false false t  in
                    let uu____4863 =
                      let uu____4864 = str "by"  in
                      let uu____4865 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4864 uu____4865  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4862 uu____4863  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4861
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4860  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4858 uu____4859  in
            FStar_Pprint.group uu____4857
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4866;_},e1::e2::e3::[])
            ->
            let uu____4872 =
              let uu____4873 =
                let uu____4874 =
                  let uu____4875 = p_atomicTermNotQUident e1  in
                  let uu____4876 =
                    let uu____4877 =
                      let uu____4878 =
                        let uu____4879 = p_term false false e2  in
                        soft_parens_with_nesting uu____4879  in
                      let uu____4880 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4878 uu____4880  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4877  in
                  FStar_Pprint.op_Hat_Hat uu____4875 uu____4876  in
                FStar_Pprint.group uu____4874  in
              let uu____4881 =
                let uu____4882 = p_noSeqTerm ps pb e3  in jump2 uu____4882
                 in
              FStar_Pprint.op_Hat_Hat uu____4873 uu____4881  in
            FStar_Pprint.group uu____4872
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4883;_},e1::e2::e3::[])
            ->
            let uu____4889 =
              let uu____4890 =
                let uu____4891 =
                  let uu____4892 = p_atomicTermNotQUident e1  in
                  let uu____4893 =
                    let uu____4894 =
                      let uu____4895 =
                        let uu____4896 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4896  in
                      let uu____4897 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4895 uu____4897  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4894  in
                  FStar_Pprint.op_Hat_Hat uu____4892 uu____4893  in
                FStar_Pprint.group uu____4891  in
              let uu____4898 =
                let uu____4899 = p_noSeqTerm ps pb e3  in jump2 uu____4899
                 in
              FStar_Pprint.op_Hat_Hat uu____4890 uu____4898  in
            FStar_Pprint.group uu____4889
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4907 =
              let uu____4908 = str "requires"  in
              let uu____4909 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4908 uu____4909  in
            FStar_Pprint.group uu____4907
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4917 =
              let uu____4918 = str "ensures"  in
              let uu____4919 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4918 uu____4919  in
            FStar_Pprint.group uu____4917
        | FStar_Parser_AST.Attributes es ->
            let uu____4923 =
              let uu____4924 = str "attributes"  in
              let uu____4925 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4924 uu____4925  in
            FStar_Pprint.group uu____4923
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4929 =
                let uu____4930 =
                  let uu____4931 = str "if"  in
                  let uu____4932 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4931 uu____4932  in
                let uu____4933 =
                  let uu____4934 = str "then"  in
                  let uu____4935 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4934 uu____4935  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4930 uu____4933  in
              FStar_Pprint.group uu____4929
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4938,uu____4939,e31) when
                     is_unit e31 ->
                     let uu____4941 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4941
                 | uu____4942 -> p_noSeqTerm false false e2  in
               let uu____4943 =
                 let uu____4944 =
                   let uu____4945 = str "if"  in
                   let uu____4946 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4945 uu____4946  in
                 let uu____4947 =
                   let uu____4948 =
                     let uu____4949 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4949 e2_doc  in
                   let uu____4950 =
                     let uu____4951 = str "else"  in
                     let uu____4952 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4951 uu____4952  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4948 uu____4950  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4944 uu____4947  in
               FStar_Pprint.group uu____4943)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4975 =
              let uu____4976 =
                let uu____4977 =
                  let uu____4978 = str "try"  in
                  let uu____4979 = p_noSeqTerm false false e1  in
                  prefix2 uu____4978 uu____4979  in
                let uu____4980 =
                  let uu____4981 = str "with"  in
                  let uu____4982 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4981 uu____4982  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4977 uu____4980  in
              FStar_Pprint.group uu____4976  in
            let uu____4991 = paren_if (ps || pb)  in uu____4991 uu____4975
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5018 =
              let uu____5019 =
                let uu____5020 =
                  let uu____5021 = str "match"  in
                  let uu____5022 = p_noSeqTerm false false e1  in
                  let uu____5023 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5021 uu____5022 uu____5023
                   in
                let uu____5024 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5020 uu____5024  in
              FStar_Pprint.group uu____5019  in
            let uu____5033 = paren_if (ps || pb)  in uu____5033 uu____5018
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5040 =
              let uu____5041 =
                let uu____5042 =
                  let uu____5043 = str "let open"  in
                  let uu____5044 = p_quident uid  in
                  let uu____5045 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5043 uu____5044 uu____5045
                   in
                let uu____5046 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5042 uu____5046  in
              FStar_Pprint.group uu____5041  in
            let uu____5047 = paren_if ps  in uu____5047 uu____5040
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5111 is_last =
              match uu____5111 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5144 =
                          let uu____5145 = str "let"  in
                          let uu____5146 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5145 uu____5146
                           in
                        FStar_Pprint.group uu____5144
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5147 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5152 =
                    if is_last
                    then
                      let uu____5153 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5154 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5153 doc_expr uu____5154
                    else
                      (let uu____5156 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5156)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5152
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5202 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5202
                     else
                       (let uu____5210 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5210)) lbs
               in
            let lbs_doc =
              let uu____5218 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5218  in
            let uu____5219 =
              let uu____5220 =
                let uu____5221 =
                  let uu____5222 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5222
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5221  in
              FStar_Pprint.group uu____5220  in
            let uu____5223 = paren_if ps  in uu____5223 uu____5219
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5230;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5233;
                                                             FStar_Parser_AST.level
                                                               = uu____5234;_})
            when matches_var maybe_x x ->
            let uu____5261 =
              let uu____5262 =
                let uu____5263 = str "function"  in
                let uu____5264 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5263 uu____5264  in
              FStar_Pprint.group uu____5262  in
            let uu____5273 = paren_if (ps || pb)  in uu____5273 uu____5261
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5279 =
              let uu____5280 = str "quote"  in
              let uu____5281 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5280 uu____5281  in
            FStar_Pprint.group uu____5279
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5283 =
              let uu____5284 = str "`"  in
              let uu____5285 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5284 uu____5285  in
            FStar_Pprint.group uu____5283
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5287 =
              let uu____5288 = str "`%"  in
              let uu____5289 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5288 uu____5289  in
            FStar_Pprint.group uu____5287
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5291;
              FStar_Parser_AST.level = uu____5292;_}
            ->
            let uu____5293 =
              let uu____5294 = str "`@"  in
              let uu____5295 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5294 uu____5295  in
            FStar_Pprint.group uu____5293
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5297 =
              let uu____5298 = str "`#"  in
              let uu____5299 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5298 uu____5299  in
            FStar_Pprint.group uu____5297
        | uu____5300 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___115_5301  ->
    match uu___115_5301 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5313 =
          let uu____5314 = str "[@"  in
          let uu____5315 =
            let uu____5316 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5317 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5316 uu____5317  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5314 uu____5315  in
        FStar_Pprint.group uu____5313

and (p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and (p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5343 =
                   let uu____5344 =
                     let uu____5345 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5345 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5344 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5343 term_doc
             | pats ->
                 let uu____5351 =
                   let uu____5352 =
                     let uu____5353 =
                       let uu____5354 =
                         let uu____5355 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5355
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5354 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5356 = p_trigger trigger  in
                     prefix2 uu____5353 uu____5356  in
                   FStar_Pprint.group uu____5352  in
                 prefix2 uu____5351 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5376 =
                   let uu____5377 =
                     let uu____5378 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5378 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5377 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5376 term_doc
             | pats ->
                 let uu____5384 =
                   let uu____5385 =
                     let uu____5386 =
                       let uu____5387 =
                         let uu____5388 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5388
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5387 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5389 = p_trigger trigger  in
                     prefix2 uu____5386 uu____5389  in
                   FStar_Pprint.group uu____5385  in
                 prefix2 uu____5384 term_doc)
        | uu____5390 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5392 -> str "forall"
    | FStar_Parser_AST.QExists uu____5405 -> str "exists"
    | uu____5418 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___116_5419  ->
    match uu___116_5419 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5431 =
          let uu____5432 =
            let uu____5433 =
              let uu____5434 = str "pattern"  in
              let uu____5435 =
                let uu____5436 =
                  let uu____5437 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5437
                   in
                FStar_Pprint.op_Hat_Hat uu____5436 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5434 uu____5435  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5433  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5432  in
        FStar_Pprint.group uu____5431

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5443 = str "\\/"  in
    FStar_Pprint.separate_map uu____5443 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5449 =
      let uu____5450 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5450 p_appTerm pats  in
    FStar_Pprint.group uu____5449

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5460 =
              let uu____5461 =
                let uu____5462 = str "fun"  in
                let uu____5463 =
                  let uu____5464 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5464
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5462 uu____5463  in
              let uu____5465 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5461 uu____5465  in
            let uu____5466 = paren_if ps  in uu____5466 uu____5460
        | uu____5471 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5475  ->
      match uu____5475 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5498 =
                    let uu____5499 =
                      let uu____5500 =
                        let uu____5501 = p_tuplePattern p  in
                        let uu____5502 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5501 uu____5502  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5500
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5499  in
                  FStar_Pprint.group uu____5498
              | FStar_Pervasives_Native.Some f ->
                  let uu____5504 =
                    let uu____5505 =
                      let uu____5506 =
                        let uu____5507 =
                          let uu____5508 =
                            let uu____5509 = p_tuplePattern p  in
                            let uu____5510 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5509
                              uu____5510
                             in
                          FStar_Pprint.group uu____5508  in
                        let uu____5511 =
                          let uu____5512 =
                            let uu____5515 = p_tmFormula f  in
                            [uu____5515; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5512  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5507 uu____5511
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5506
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5505  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5504
               in
            let uu____5516 =
              let uu____5517 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5517  in
            FStar_Pprint.group uu____5516  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5526 =
                      let uu____5527 =
                        let uu____5528 =
                          let uu____5529 =
                            let uu____5530 =
                              let uu____5531 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5531  in
                            FStar_Pprint.separate_map uu____5530
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5529
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5528
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5527  in
                    FStar_Pprint.group uu____5526
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5532 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5534;_},e1::e2::[])
        ->
        let uu____5539 = str "<==>"  in
        let uu____5540 = p_tmImplies e1  in
        let uu____5541 = p_tmIff e2  in
        infix0 uu____5539 uu____5540 uu____5541
    | uu____5542 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5544;_},e1::e2::[])
        ->
        let uu____5549 = str "==>"  in
        let uu____5550 = p_tmArrow p_tmFormula e1  in
        let uu____5551 = p_tmImplies e2  in
        infix0 uu____5549 uu____5550 uu____5551
    | uu____5552 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5560 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5560 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_5 when _0_5 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5581 ->
               let uu____5582 =
                 let uu____5583 =
                   let uu____5584 =
                     let uu____5585 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5585
                      in
                   FStar_Pprint.separate uu____5584 terms  in
                 let uu____5586 =
                   let uu____5587 =
                     let uu____5588 =
                       let uu____5589 =
                         let uu____5590 =
                           let uu____5591 =
                             let uu____5592 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5592
                              in
                           FStar_Pprint.separate uu____5591 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5590 last_op  in
                       let uu____5593 =
                         let uu____5594 =
                           let uu____5595 =
                             let uu____5596 =
                               let uu____5597 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5597
                                in
                             FStar_Pprint.separate uu____5596 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5595 last_op  in
                         jump2 uu____5594  in
                       FStar_Pprint.ifflat uu____5589 uu____5593  in
                     FStar_Pprint.group uu____5588  in
                   let uu____5598 = FStar_List.hd last1  in
                   prefix2 uu____5587 uu____5598  in
                 FStar_Pprint.ifflat uu____5583 uu____5586  in
               FStar_Pprint.group uu____5582)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5611 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5616 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5611 uu____5616
      | uu____5619 -> let uu____5620 = p_Tm e  in [uu____5620]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5623 =
        let uu____5624 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5624 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5623  in
    let disj =
      let uu____5626 =
        let uu____5627 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5627 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5626  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5646;_},e1::e2::[])
        ->
        let uu____5651 = p_tmDisjunction e1  in
        let uu____5656 = let uu____5661 = p_tmConjunction e2  in [uu____5661]
           in
        FStar_List.append uu____5651 uu____5656
    | uu____5670 -> let uu____5671 = p_tmConjunction e  in [uu____5671]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5681;_},e1::e2::[])
        ->
        let uu____5686 = p_tmConjunction e1  in
        let uu____5689 = let uu____5692 = p_tmTuple e2  in [uu____5692]  in
        FStar_List.append uu____5686 uu____5689
    | uu____5693 -> let uu____5694 = p_tmTuple e  in [uu____5694]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5711 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5711
          (fun uu____5719  ->
             match uu____5719 with | (e1,uu____5725) -> p_tmEq e1) args
    | uu____5726 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5731 =
             let uu____5732 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5732  in
           FStar_Pprint.group uu____5731)

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
               (let uu____5749 = FStar_Ident.text_of_id op  in
                uu____5749 = "="))
              ||
              (let uu____5751 = FStar_Ident.text_of_id op  in
               uu____5751 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5753 = levels op1  in
            (match uu____5753 with
             | (left1,mine,right1) ->
                 let uu____5763 =
                   let uu____5764 = FStar_All.pipe_left str op1  in
                   let uu____5765 = p_tmEqWith' p_X left1 e1  in
                   let uu____5766 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5764 uu____5765 uu____5766  in
                 paren_if_gt curr mine uu____5763)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5767;_},e1::e2::[])
            ->
            let uu____5772 =
              let uu____5773 = p_tmEqWith p_X e1  in
              let uu____5774 =
                let uu____5775 =
                  let uu____5776 =
                    let uu____5777 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5777  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5776  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5775  in
              FStar_Pprint.op_Hat_Hat uu____5773 uu____5774  in
            FStar_Pprint.group uu____5772
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5778;_},e1::[])
            ->
            let uu____5782 = levels "-"  in
            (match uu____5782 with
             | (left1,mine,right1) ->
                 let uu____5792 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5792)
        | uu____5793 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5837)::(e2,uu____5839)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5859 = is_list e  in Prims.op_Negation uu____5859)
              ->
              let op = "::"  in
              let uu____5861 = levels op  in
              (match uu____5861 with
               | (left1,mine,right1) ->
                   let uu____5871 =
                     let uu____5872 = str op  in
                     let uu____5873 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5874 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5872 uu____5873 uu____5874  in
                   paren_if_gt curr mine uu____5871)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5882 = levels op  in
              (match uu____5882 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5898 = p_binder false b  in
                     let uu____5899 =
                       let uu____5900 =
                         let uu____5901 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5901 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5900
                        in
                     FStar_Pprint.op_Hat_Hat uu____5898 uu____5899  in
                   let uu____5902 =
                     let uu____5903 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5904 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5903 uu____5904  in
                   paren_if_gt curr mine uu____5902)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5905;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5930 = levels op  in
              (match uu____5930 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5940 = str op  in
                     let uu____5941 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5942 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5940 uu____5941 uu____5942
                   else
                     (let uu____5944 =
                        let uu____5945 = str op  in
                        let uu____5946 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5947 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5945 uu____5946 uu____5947  in
                      paren_if_gt curr mine uu____5944))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5954 = levels op1  in
              (match uu____5954 with
               | (left1,mine,right1) ->
                   let uu____5964 =
                     let uu____5965 = str op1  in
                     let uu____5966 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5967 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5965 uu____5966 uu____5967  in
                   paren_if_gt curr mine uu____5964)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5986 =
                let uu____5987 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5988 =
                  let uu____5989 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5989 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5987 uu____5988  in
              braces_with_nesting uu____5986
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5994;_},e1::[])
              ->
              let uu____5998 =
                let uu____5999 = str "~"  in
                let uu____6000 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5999 uu____6000  in
              FStar_Pprint.group uu____5998
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6002;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6008 = levels op  in
                   (match uu____6008 with
                    | (left1,mine,right1) ->
                        let uu____6018 =
                          let uu____6019 = str op  in
                          let uu____6020 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6021 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6019 uu____6020 uu____6021  in
                        paren_if_gt curr mine uu____6018)
               | uu____6022 -> p_X e)
          | uu____6023 -> p_X e

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
        let uu____6030 =
          let uu____6031 = p_lident lid  in
          let uu____6032 =
            let uu____6033 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6033  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6031 uu____6032  in
        FStar_Pprint.group uu____6030
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6036 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6038 = p_appTerm e  in
    let uu____6039 =
      let uu____6040 =
        let uu____6041 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6041 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6040  in
    FStar_Pprint.op_Hat_Hat uu____6038 uu____6039

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6046 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6046 t phi
      | FStar_Parser_AST.TAnnotated uu____6047 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6052 ->
          let uu____6053 =
            let uu____6054 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6054
             in
          failwith uu____6053
      | FStar_Parser_AST.TVariable uu____6055 ->
          let uu____6056 =
            let uu____6057 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6057
             in
          failwith uu____6056
      | FStar_Parser_AST.NoName uu____6058 ->
          let uu____6059 =
            let uu____6060 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6060
             in
          failwith uu____6059

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6062  ->
      match uu____6062 with
      | (lid,e) ->
          let uu____6069 =
            let uu____6070 = p_qlident lid  in
            let uu____6071 =
              let uu____6072 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6072
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6070 uu____6071  in
          FStar_Pprint.group uu____6069

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6074 when is_general_application e ->
        let uu____6081 = head_and_args e  in
        (match uu____6081 with
         | (head1,args) ->
             let uu____6106 =
               let uu____6117 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6117
               then
                 let uu____6147 =
                   FStar_Util.take
                     (fun uu____6171  ->
                        match uu____6171 with
                        | (uu____6176,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6147 with
                 | (fs_typ_args,args1) ->
                     let uu____6214 =
                       let uu____6215 = p_indexingTerm head1  in
                       let uu____6216 =
                         let uu____6217 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6217 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6215 uu____6216  in
                     (uu____6214, args1)
               else
                 (let uu____6229 = p_indexingTerm head1  in
                  (uu____6229, args))
                in
             (match uu____6106 with
              | (head_doc,args1) ->
                  let uu____6250 =
                    let uu____6251 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6251 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6250))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6271 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6271)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6289 =
               let uu____6290 = p_quident lid  in
               let uu____6291 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6290 uu____6291  in
             FStar_Pprint.group uu____6289
         | hd1::tl1 ->
             let uu____6308 =
               let uu____6309 =
                 let uu____6310 =
                   let uu____6311 = p_quident lid  in
                   let uu____6312 = p_argTerm hd1  in
                   prefix2 uu____6311 uu____6312  in
                 FStar_Pprint.group uu____6310  in
               let uu____6313 =
                 let uu____6314 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6314  in
               FStar_Pprint.op_Hat_Hat uu____6309 uu____6313  in
             FStar_Pprint.group uu____6308)
    | uu____6319 -> p_indexingTerm e

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
         (let uu____6328 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6328 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6330 = str "#"  in
        let uu____6331 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6330 uu____6331
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6334 = str "#["  in
        let uu____6335 =
          let uu____6336 = p_indexingTerm t  in
          let uu____6337 =
            let uu____6338 = str "]"  in
            let uu____6339 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6338 uu____6339  in
          FStar_Pprint.op_Hat_Hat uu____6336 uu____6337  in
        FStar_Pprint.op_Hat_Hat uu____6334 uu____6335
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6341  ->
    match uu____6341 with | (e,uu____6347) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6352;_},e1::e2::[])
          ->
          let uu____6357 =
            let uu____6358 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6359 =
              let uu____6360 =
                let uu____6361 = p_term false false e2  in
                soft_parens_with_nesting uu____6361  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6360  in
            FStar_Pprint.op_Hat_Hat uu____6358 uu____6359  in
          FStar_Pprint.group uu____6357
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6362;_},e1::e2::[])
          ->
          let uu____6367 =
            let uu____6368 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6369 =
              let uu____6370 =
                let uu____6371 = p_term false false e2  in
                soft_brackets_with_nesting uu____6371  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6370  in
            FStar_Pprint.op_Hat_Hat uu____6368 uu____6369  in
          FStar_Pprint.group uu____6367
      | uu____6372 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6377 = p_quident lid  in
        let uu____6378 =
          let uu____6379 =
            let uu____6380 = p_term false false e1  in
            soft_parens_with_nesting uu____6380  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6379  in
        FStar_Pprint.op_Hat_Hat uu____6377 uu____6378
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6386 =
          let uu____6387 = FStar_Ident.text_of_id op  in str uu____6387  in
        let uu____6388 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6386 uu____6388
    | uu____6389 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____6398 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6405 =
          let uu____6406 = FStar_Ident.text_of_id op  in str uu____6406  in
        let uu____6407 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6405 uu____6407
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6411 =
          let uu____6412 =
            let uu____6413 =
              let uu____6414 = FStar_Ident.text_of_id op  in str uu____6414
               in
            let uu____6415 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6413 uu____6415  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6412  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6411
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6430 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6431 =
          let uu____6432 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6433 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6432 p_tmEq uu____6433  in
        let uu____6440 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6430 uu____6431 uu____6440
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6443 =
          let uu____6444 = p_atomicTermNotQUident e1  in
          let uu____6445 =
            let uu____6446 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6446  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6444 uu____6445
           in
        FStar_Pprint.group uu____6443
    | uu____6447 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6452 = p_quident constr_lid  in
        let uu____6453 =
          let uu____6454 =
            let uu____6455 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6455  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6454  in
        FStar_Pprint.op_Hat_Hat uu____6452 uu____6453
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6457 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6457 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6459 = p_term false false e1  in
        soft_parens_with_nesting uu____6459
    | uu____6460 when is_array e ->
        let es = extract_from_list e  in
        let uu____6464 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6465 =
          let uu____6466 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6466
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6469 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6464 uu____6465 uu____6469
    | uu____6470 when is_list e ->
        let uu____6471 =
          let uu____6472 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6473 = extract_from_list e  in
          separate_map_or_flow_last uu____6472
            (fun ps  -> p_noSeqTerm ps false) uu____6473
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6471 FStar_Pprint.rbracket
    | uu____6478 when is_lex_list e ->
        let uu____6479 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6480 =
          let uu____6481 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6482 = extract_from_list e  in
          separate_map_or_flow_last uu____6481
            (fun ps  -> p_noSeqTerm ps false) uu____6482
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6479 uu____6480 FStar_Pprint.rbracket
    | uu____6487 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6491 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6492 =
          let uu____6493 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6493 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6491 uu____6492 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6497 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6498 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6497 uu____6498
    | FStar_Parser_AST.Op (op,args) when
        let uu____6505 = handleable_op op args  in
        Prims.op_Negation uu____6505 ->
        let uu____6506 =
          let uu____6507 =
            let uu____6508 = FStar_Ident.text_of_id op  in
            let uu____6509 =
              let uu____6510 =
                let uu____6511 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6511
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6510  in
            Prims.strcat uu____6508 uu____6509  in
          Prims.strcat "Operation " uu____6507  in
        failwith uu____6506
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6513 = str "u#"  in
        let uu____6514 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6513 uu____6514
    | FStar_Parser_AST.Wild  ->
        let uu____6515 = p_term false false e  in
        soft_parens_with_nesting uu____6515
    | FStar_Parser_AST.Const uu____6516 ->
        let uu____6517 = p_term false false e  in
        soft_parens_with_nesting uu____6517
    | FStar_Parser_AST.Op uu____6518 ->
        let uu____6525 = p_term false false e  in
        soft_parens_with_nesting uu____6525
    | FStar_Parser_AST.Tvar uu____6526 ->
        let uu____6527 = p_term false false e  in
        soft_parens_with_nesting uu____6527
    | FStar_Parser_AST.Var uu____6528 ->
        let uu____6529 = p_term false false e  in
        soft_parens_with_nesting uu____6529
    | FStar_Parser_AST.Name uu____6530 ->
        let uu____6531 = p_term false false e  in
        soft_parens_with_nesting uu____6531
    | FStar_Parser_AST.Construct uu____6532 ->
        let uu____6543 = p_term false false e  in
        soft_parens_with_nesting uu____6543
    | FStar_Parser_AST.Abs uu____6544 ->
        let uu____6551 = p_term false false e  in
        soft_parens_with_nesting uu____6551
    | FStar_Parser_AST.App uu____6552 ->
        let uu____6559 = p_term false false e  in
        soft_parens_with_nesting uu____6559
    | FStar_Parser_AST.Let uu____6560 ->
        let uu____6581 = p_term false false e  in
        soft_parens_with_nesting uu____6581
    | FStar_Parser_AST.LetOpen uu____6582 ->
        let uu____6587 = p_term false false e  in
        soft_parens_with_nesting uu____6587
    | FStar_Parser_AST.Seq uu____6588 ->
        let uu____6593 = p_term false false e  in
        soft_parens_with_nesting uu____6593
    | FStar_Parser_AST.Bind uu____6594 ->
        let uu____6601 = p_term false false e  in
        soft_parens_with_nesting uu____6601
    | FStar_Parser_AST.If uu____6602 ->
        let uu____6609 = p_term false false e  in
        soft_parens_with_nesting uu____6609
    | FStar_Parser_AST.Match uu____6610 ->
        let uu____6625 = p_term false false e  in
        soft_parens_with_nesting uu____6625
    | FStar_Parser_AST.TryWith uu____6626 ->
        let uu____6641 = p_term false false e  in
        soft_parens_with_nesting uu____6641
    | FStar_Parser_AST.Ascribed uu____6642 ->
        let uu____6651 = p_term false false e  in
        soft_parens_with_nesting uu____6651
    | FStar_Parser_AST.Record uu____6652 ->
        let uu____6665 = p_term false false e  in
        soft_parens_with_nesting uu____6665
    | FStar_Parser_AST.Project uu____6666 ->
        let uu____6671 = p_term false false e  in
        soft_parens_with_nesting uu____6671
    | FStar_Parser_AST.Product uu____6672 ->
        let uu____6679 = p_term false false e  in
        soft_parens_with_nesting uu____6679
    | FStar_Parser_AST.Sum uu____6680 ->
        let uu____6687 = p_term false false e  in
        soft_parens_with_nesting uu____6687
    | FStar_Parser_AST.QForall uu____6688 ->
        let uu____6701 = p_term false false e  in
        soft_parens_with_nesting uu____6701
    | FStar_Parser_AST.QExists uu____6702 ->
        let uu____6715 = p_term false false e  in
        soft_parens_with_nesting uu____6715
    | FStar_Parser_AST.Refine uu____6716 ->
        let uu____6721 = p_term false false e  in
        soft_parens_with_nesting uu____6721
    | FStar_Parser_AST.NamedTyp uu____6722 ->
        let uu____6727 = p_term false false e  in
        soft_parens_with_nesting uu____6727
    | FStar_Parser_AST.Requires uu____6728 ->
        let uu____6735 = p_term false false e  in
        soft_parens_with_nesting uu____6735
    | FStar_Parser_AST.Ensures uu____6736 ->
        let uu____6743 = p_term false false e  in
        soft_parens_with_nesting uu____6743
    | FStar_Parser_AST.Attributes uu____6744 ->
        let uu____6747 = p_term false false e  in
        soft_parens_with_nesting uu____6747
    | FStar_Parser_AST.Quote uu____6748 ->
        let uu____6753 = p_term false false e  in
        soft_parens_with_nesting uu____6753
    | FStar_Parser_AST.VQuote uu____6754 ->
        let uu____6755 = p_term false false e  in
        soft_parens_with_nesting uu____6755
    | FStar_Parser_AST.Antiquote uu____6756 ->
        let uu____6757 = p_term false false e  in
        soft_parens_with_nesting uu____6757

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___119_6758  ->
    match uu___119_6758 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6764) ->
        let uu____6765 = str s  in FStar_Pprint.dquotes uu____6765
    | FStar_Const.Const_bytearray (bytes,uu____6767) ->
        let uu____6774 =
          let uu____6775 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6775  in
        let uu____6776 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6774 uu____6776
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___117_6796 =
          match uu___117_6796 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___118_6802 =
          match uu___118_6802 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6813  ->
               match uu____6813 with
               | (s,w) ->
                   let uu____6820 = signedness s  in
                   let uu____6821 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6820 uu____6821)
            sign_width_opt
           in
        let uu____6822 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6822 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6824 = FStar_Range.string_of_range r  in str uu____6824
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6826 = p_quident lid  in
        let uu____6827 =
          let uu____6828 =
            let uu____6829 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6829  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6828  in
        FStar_Pprint.op_Hat_Hat uu____6826 uu____6827

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6831 = str "u#"  in
    let uu____6832 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6831 uu____6832

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6834;_},u1::u2::[])
        ->
        let uu____6839 =
          let uu____6840 = p_universeFrom u1  in
          let uu____6841 =
            let uu____6842 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6842  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6840 uu____6841  in
        FStar_Pprint.group uu____6839
    | FStar_Parser_AST.App uu____6843 ->
        let uu____6850 = head_and_args u  in
        (match uu____6850 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6876 =
                    let uu____6877 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6878 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6886  ->
                           match uu____6886 with
                           | (u1,uu____6892) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6877 uu____6878  in
                  FStar_Pprint.group uu____6876
              | uu____6893 ->
                  let uu____6894 =
                    let uu____6895 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6895
                     in
                  failwith uu____6894))
    | uu____6896 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6919 = FStar_Ident.text_of_id id1  in str uu____6919
    | FStar_Parser_AST.Paren u1 ->
        let uu____6921 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6921
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6922;_},uu____6923::uu____6924::[])
        ->
        let uu____6927 = p_universeFrom u  in
        soft_parens_with_nesting uu____6927
    | FStar_Parser_AST.App uu____6928 ->
        let uu____6935 = p_universeFrom u  in
        soft_parens_with_nesting uu____6935
    | uu____6936 ->
        let uu____6937 =
          let uu____6938 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6938
           in
        failwith uu____6937

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
       | FStar_Parser_AST.Module (uu____7010,decls) ->
           let uu____7016 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7016
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7025,decls,uu____7027) ->
           let uu____7032 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7032
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7085  ->
         match uu____7085 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7129,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7135,decls,uu____7137) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7182 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7195;
                 FStar_Parser_AST.doc = uu____7196;
                 FStar_Parser_AST.quals = uu____7197;
                 FStar_Parser_AST.attrs = uu____7198;_}::uu____7199 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7205 =
                   let uu____7208 =
                     let uu____7211 = FStar_List.tl ds  in d :: uu____7211
                      in
                   d0 :: uu____7208  in
                 (uu____7205, (d0.FStar_Parser_AST.drange))
             | uu____7216 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7182 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7276 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7276 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7372 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7372, comments1))))))
  