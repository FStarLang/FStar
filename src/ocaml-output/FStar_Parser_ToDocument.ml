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
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2007 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2007 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2009 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2009
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
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
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___114_4499  ->
    match uu___114_4499 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4501 = str "#["  in
        let uu____4502 =
          let uu____4503 = p_term false false t  in
          let uu____4504 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4503 uu____4504  in
        FStar_Pprint.op_Hat_Hat uu____4501 uu____4502

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4509 =
          let uu____4510 =
            let uu____4511 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4511  in
          FStar_Pprint.separate_map uu____4510 p_tuplePattern pats  in
        FStar_Pprint.group uu____4509
    | uu____4512 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4519 =
          let uu____4520 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4520 p_constructorPattern pats  in
        FStar_Pprint.group uu____4519
    | uu____4521 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4524;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4529 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4530 = p_constructorPattern hd1  in
        let uu____4531 = p_constructorPattern tl1  in
        infix0 uu____4529 uu____4530 uu____4531
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4533;_},pats)
        ->
        let uu____4539 = p_quident uid  in
        let uu____4540 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4539 uu____4540
    | uu____4541 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4557;
               FStar_Parser_AST.blevel = uu____4558;
               FStar_Parser_AST.aqual = uu____4559;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4567 =
               let uu____4568 = p_ident lid  in
               p_refinement aqual uu____4568 t1 phi  in
             soft_parens_with_nesting uu____4567
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4571;
               FStar_Parser_AST.blevel = uu____4572;
               FStar_Parser_AST.aqual = uu____4573;_},phi))
             ->
             let uu____4579 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4579
         | uu____4580 ->
             let uu____4585 =
               let uu____4586 = p_tuplePattern pat  in
               let uu____4587 =
                 let uu____4588 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4588
                  in
               FStar_Pprint.op_Hat_Hat uu____4586 uu____4587  in
             soft_parens_with_nesting uu____4585)
    | FStar_Parser_AST.PatList pats ->
        let uu____4592 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4592 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4609 =
          match uu____4609 with
          | (lid,pat) ->
              let uu____4616 = p_qlident lid  in
              let uu____4617 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4616 uu____4617
           in
        let uu____4618 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4618
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4628 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4629 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4630 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4628 uu____4629 uu____4630
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4639 =
          let uu____4640 =
            let uu____4641 =
              let uu____4642 = FStar_Ident.text_of_id op  in str uu____4642
               in
            let uu____4643 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4641 uu____4643  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4640  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4639
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4647 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4647 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4655 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4656 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4655 uu____4656
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4658 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4661;
           FStar_Parser_AST.prange = uu____4662;_},uu____4663)
        ->
        let uu____4668 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4668
    | FStar_Parser_AST.PatTuple (uu____4669,false ) ->
        let uu____4674 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4674
    | uu____4675 ->
        let uu____4676 =
          let uu____4677 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4677  in
        failwith uu____4676

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4679;_},uu____4680)
        -> true
    | uu____4685 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4689 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4690 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4689 uu____4690
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4697;
                   FStar_Parser_AST.blevel = uu____4698;
                   FStar_Parser_AST.aqual = uu____4699;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4703 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4703 t1 phi
            | uu____4704 ->
                let t' =
                  let uu____4706 = is_typ_tuple t  in
                  if uu____4706
                  then
                    let uu____4707 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4707
                  else p_tmFormula t  in
                let uu____4709 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4710 =
                  let uu____4711 = p_lident lid  in
                  let uu____4712 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4711 uu____4712  in
                FStar_Pprint.op_Hat_Hat uu____4709 uu____4710
             in
          if is_atomic
          then
            let uu____4713 =
              let uu____4714 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4714  in
            FStar_Pprint.group uu____4713
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4716 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4723;
                  FStar_Parser_AST.blevel = uu____4724;
                  FStar_Parser_AST.aqual = uu____4725;_},phi)
               ->
               if is_atomic
               then
                 let uu____4729 =
                   let uu____4730 =
                     let uu____4731 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4731 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4730  in
                 FStar_Pprint.group uu____4729
               else
                 (let uu____4733 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4733)
           | uu____4734 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4743 -> false
            | FStar_Parser_AST.App uu____4754 -> false
            | FStar_Parser_AST.Op uu____4761 -> false
            | uu____4768 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4772 =
            let uu____4773 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4774 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4773 uu____4774  in
          let uu____4775 =
            let uu____4776 = p_appTerm t  in
            let uu____4777 =
              let uu____4778 =
                let uu____4779 =
                  let uu____4780 = soft_braces_with_nesting_tight phi1  in
                  let uu____4781 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4780 uu____4781  in
                FStar_Pprint.group uu____4779  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4778
               in
            FStar_Pprint.op_Hat_Hat uu____4776 uu____4777  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4772 uu____4775

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4792 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4792

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4797 = FStar_Ident.text_of_id lid  in str uu____4797)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4800 = FStar_Ident.text_of_lid lid  in str uu____4800)

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
            let uu____4818 =
              let uu____4819 =
                let uu____4820 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4820 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4819  in
            let uu____4821 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4818 uu____4821
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4825 =
              let uu____4826 =
                let uu____4827 =
                  let uu____4828 = p_lident x  in
                  let uu____4829 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4828 uu____4829  in
                let uu____4830 =
                  let uu____4831 = p_noSeqTerm true false e1  in
                  let uu____4832 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4831 uu____4832  in
                op_Hat_Slash_Plus_Hat uu____4827 uu____4830  in
              FStar_Pprint.group uu____4826  in
            let uu____4833 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4825 uu____4833
        | uu____4834 ->
            let uu____4835 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4835

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
            let uu____4846 =
              let uu____4847 = p_tmIff e1  in
              let uu____4848 =
                let uu____4849 =
                  let uu____4850 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4850
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4849  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4847 uu____4848  in
            FStar_Pprint.group uu____4846
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4856 =
              let uu____4857 = p_tmIff e1  in
              let uu____4858 =
                let uu____4859 =
                  let uu____4860 =
                    let uu____4861 = p_typ false false t  in
                    let uu____4862 =
                      let uu____4863 = str "by"  in
                      let uu____4864 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4863 uu____4864  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4861 uu____4862  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4860
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4859  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4857 uu____4858  in
            FStar_Pprint.group uu____4856
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4865;_},e1::e2::e3::[])
            ->
            let uu____4871 =
              let uu____4872 =
                let uu____4873 =
                  let uu____4874 = p_atomicTermNotQUident e1  in
                  let uu____4875 =
                    let uu____4876 =
                      let uu____4877 =
                        let uu____4878 = p_term false false e2  in
                        soft_parens_with_nesting uu____4878  in
                      let uu____4879 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4877 uu____4879  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4876  in
                  FStar_Pprint.op_Hat_Hat uu____4874 uu____4875  in
                FStar_Pprint.group uu____4873  in
              let uu____4880 =
                let uu____4881 = p_noSeqTerm ps pb e3  in jump2 uu____4881
                 in
              FStar_Pprint.op_Hat_Hat uu____4872 uu____4880  in
            FStar_Pprint.group uu____4871
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4882;_},e1::e2::e3::[])
            ->
            let uu____4888 =
              let uu____4889 =
                let uu____4890 =
                  let uu____4891 = p_atomicTermNotQUident e1  in
                  let uu____4892 =
                    let uu____4893 =
                      let uu____4894 =
                        let uu____4895 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4895  in
                      let uu____4896 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4894 uu____4896  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4893  in
                  FStar_Pprint.op_Hat_Hat uu____4891 uu____4892  in
                FStar_Pprint.group uu____4890  in
              let uu____4897 =
                let uu____4898 = p_noSeqTerm ps pb e3  in jump2 uu____4898
                 in
              FStar_Pprint.op_Hat_Hat uu____4889 uu____4897  in
            FStar_Pprint.group uu____4888
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4906 =
              let uu____4907 = str "requires"  in
              let uu____4908 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4907 uu____4908  in
            FStar_Pprint.group uu____4906
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4916 =
              let uu____4917 = str "ensures"  in
              let uu____4918 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4917 uu____4918  in
            FStar_Pprint.group uu____4916
        | FStar_Parser_AST.Attributes es ->
            let uu____4922 =
              let uu____4923 = str "attributes"  in
              let uu____4924 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4923 uu____4924  in
            FStar_Pprint.group uu____4922
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4928 =
                let uu____4929 =
                  let uu____4930 = str "if"  in
                  let uu____4931 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4930 uu____4931  in
                let uu____4932 =
                  let uu____4933 = str "then"  in
                  let uu____4934 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4933 uu____4934  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4929 uu____4932  in
              FStar_Pprint.group uu____4928
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4937,uu____4938,e31) when
                     is_unit e31 ->
                     let uu____4940 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4940
                 | uu____4941 -> p_noSeqTerm false false e2  in
               let uu____4942 =
                 let uu____4943 =
                   let uu____4944 = str "if"  in
                   let uu____4945 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4944 uu____4945  in
                 let uu____4946 =
                   let uu____4947 =
                     let uu____4948 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4948 e2_doc  in
                   let uu____4949 =
                     let uu____4950 = str "else"  in
                     let uu____4951 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4950 uu____4951  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4947 uu____4949  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4943 uu____4946  in
               FStar_Pprint.group uu____4942)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4974 =
              let uu____4975 =
                let uu____4976 =
                  let uu____4977 = str "try"  in
                  let uu____4978 = p_noSeqTerm false false e1  in
                  prefix2 uu____4977 uu____4978  in
                let uu____4979 =
                  let uu____4980 = str "with"  in
                  let uu____4981 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4980 uu____4981  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4976 uu____4979  in
              FStar_Pprint.group uu____4975  in
            let uu____4990 = paren_if (ps || pb)  in uu____4990 uu____4974
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5017 =
              let uu____5018 =
                let uu____5019 =
                  let uu____5020 = str "match"  in
                  let uu____5021 = p_noSeqTerm false false e1  in
                  let uu____5022 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5020 uu____5021 uu____5022
                   in
                let uu____5023 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5019 uu____5023  in
              FStar_Pprint.group uu____5018  in
            let uu____5032 = paren_if (ps || pb)  in uu____5032 uu____5017
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5039 =
              let uu____5040 =
                let uu____5041 =
                  let uu____5042 = str "let open"  in
                  let uu____5043 = p_quident uid  in
                  let uu____5044 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5042 uu____5043 uu____5044
                   in
                let uu____5045 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5041 uu____5045  in
              FStar_Pprint.group uu____5040  in
            let uu____5046 = paren_if ps  in uu____5046 uu____5039
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5110 is_last =
              match uu____5110 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5143 =
                          let uu____5144 = str "let"  in
                          let uu____5145 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5144 uu____5145
                           in
                        FStar_Pprint.group uu____5143
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5146 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5151 =
                    if is_last
                    then
                      let uu____5152 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5153 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5152 doc_expr uu____5153
                    else
                      (let uu____5155 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5155)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5151
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5201 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5201
                     else
                       (let uu____5209 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5209)) lbs
               in
            let lbs_doc =
              let uu____5217 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5217  in
            let uu____5218 =
              let uu____5219 =
                let uu____5220 =
                  let uu____5221 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5221
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5220  in
              FStar_Pprint.group uu____5219  in
            let uu____5222 = paren_if ps  in uu____5222 uu____5218
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5229;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5232;
                                                             FStar_Parser_AST.level
                                                               = uu____5233;_})
            when matches_var maybe_x x ->
            let uu____5260 =
              let uu____5261 =
                let uu____5262 = str "function"  in
                let uu____5263 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5262 uu____5263  in
              FStar_Pprint.group uu____5261  in
            let uu____5272 = paren_if (ps || pb)  in uu____5272 uu____5260
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5278 =
              let uu____5279 = str "quote"  in
              let uu____5280 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5279 uu____5280  in
            FStar_Pprint.group uu____5278
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5282 =
              let uu____5283 = str "`"  in
              let uu____5284 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5283 uu____5284  in
            FStar_Pprint.group uu____5282
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5286 =
              let uu____5287 = str "`%"  in
              let uu____5288 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5287 uu____5288  in
            FStar_Pprint.group uu____5286
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5290;
              FStar_Parser_AST.level = uu____5291;_}
            ->
            let uu____5292 =
              let uu____5293 = str "`@"  in
              let uu____5294 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5293 uu____5294  in
            FStar_Pprint.group uu____5292
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5296 =
              let uu____5297 = str "`#"  in
              let uu____5298 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5297 uu____5298  in
            FStar_Pprint.group uu____5296
        | uu____5299 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___115_5300  ->
    match uu___115_5300 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5312 =
          let uu____5313 = str "[@"  in
          let uu____5314 =
            let uu____5315 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5316 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5315 uu____5316  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5313 uu____5314  in
        FStar_Pprint.group uu____5312

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
                 let uu____5342 =
                   let uu____5343 =
                     let uu____5344 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5344 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5343 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5342 term_doc
             | pats ->
                 let uu____5350 =
                   let uu____5351 =
                     let uu____5352 =
                       let uu____5353 =
                         let uu____5354 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5354
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5353 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5355 = p_trigger trigger  in
                     prefix2 uu____5352 uu____5355  in
                   FStar_Pprint.group uu____5351  in
                 prefix2 uu____5350 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5375 =
                   let uu____5376 =
                     let uu____5377 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5377 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5376 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5375 term_doc
             | pats ->
                 let uu____5383 =
                   let uu____5384 =
                     let uu____5385 =
                       let uu____5386 =
                         let uu____5387 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5387
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5386 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5388 = p_trigger trigger  in
                     prefix2 uu____5385 uu____5388  in
                   FStar_Pprint.group uu____5384  in
                 prefix2 uu____5383 term_doc)
        | uu____5389 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5391 -> str "forall"
    | FStar_Parser_AST.QExists uu____5404 -> str "exists"
    | uu____5417 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___116_5418  ->
    match uu___116_5418 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5430 =
          let uu____5431 =
            let uu____5432 =
              let uu____5433 = str "pattern"  in
              let uu____5434 =
                let uu____5435 =
                  let uu____5436 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5436
                   in
                FStar_Pprint.op_Hat_Hat uu____5435 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5433 uu____5434  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5432  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5431  in
        FStar_Pprint.group uu____5430

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5442 = str "\\/"  in
    FStar_Pprint.separate_map uu____5442 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5448 =
      let uu____5449 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5449 p_appTerm pats  in
    FStar_Pprint.group uu____5448

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5459 =
              let uu____5460 =
                let uu____5461 = str "fun"  in
                let uu____5462 =
                  let uu____5463 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5463
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5461 uu____5462  in
              let uu____5464 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5460 uu____5464  in
            let uu____5465 = paren_if ps  in uu____5465 uu____5459
        | uu____5470 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5474  ->
      match uu____5474 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5497 =
                    let uu____5498 =
                      let uu____5499 =
                        let uu____5500 = p_tuplePattern p  in
                        let uu____5501 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5500 uu____5501  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5499
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5498  in
                  FStar_Pprint.group uu____5497
              | FStar_Pervasives_Native.Some f ->
                  let uu____5503 =
                    let uu____5504 =
                      let uu____5505 =
                        let uu____5506 =
                          let uu____5507 =
                            let uu____5508 = p_tuplePattern p  in
                            let uu____5509 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5508
                              uu____5509
                             in
                          FStar_Pprint.group uu____5507  in
                        let uu____5510 =
                          let uu____5511 =
                            let uu____5514 = p_tmFormula f  in
                            [uu____5514; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5511  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5506 uu____5510
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5505
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5504  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5503
               in
            let uu____5515 =
              let uu____5516 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5516  in
            FStar_Pprint.group uu____5515  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5525 =
                      let uu____5526 =
                        let uu____5527 =
                          let uu____5528 =
                            let uu____5529 =
                              let uu____5530 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5530  in
                            FStar_Pprint.separate_map uu____5529
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5528
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5527
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5526  in
                    FStar_Pprint.group uu____5525
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5531 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5533;_},e1::e2::[])
        ->
        let uu____5538 = str "<==>"  in
        let uu____5539 = p_tmImplies e1  in
        let uu____5540 = p_tmIff e2  in
        infix0 uu____5538 uu____5539 uu____5540
    | uu____5541 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5543;_},e1::e2::[])
        ->
        let uu____5548 = str "==>"  in
        let uu____5549 = p_tmArrow p_tmFormula e1  in
        let uu____5550 = p_tmImplies e2  in
        infix0 uu____5548 uu____5549 uu____5550
    | uu____5551 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5559 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5559 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5580 ->
               let uu____5581 =
                 let uu____5582 =
                   let uu____5583 =
                     let uu____5584 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5584
                      in
                   FStar_Pprint.separate uu____5583 terms  in
                 let uu____5585 =
                   let uu____5586 =
                     let uu____5587 =
                       let uu____5588 =
                         let uu____5589 =
                           let uu____5590 =
                             let uu____5591 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5591
                              in
                           FStar_Pprint.separate uu____5590 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5589 last_op  in
                       let uu____5592 =
                         let uu____5593 =
                           let uu____5594 =
                             let uu____5595 =
                               let uu____5596 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5596
                                in
                             FStar_Pprint.separate uu____5595 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5594 last_op  in
                         jump2 uu____5593  in
                       FStar_Pprint.ifflat uu____5588 uu____5592  in
                     FStar_Pprint.group uu____5587  in
                   let uu____5597 = FStar_List.hd last1  in
                   prefix2 uu____5586 uu____5597  in
                 FStar_Pprint.ifflat uu____5582 uu____5585  in
               FStar_Pprint.group uu____5581)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5610 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5615 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5610 uu____5615
      | uu____5618 -> let uu____5619 = p_Tm e  in [uu____5619]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5622 =
        let uu____5623 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5623 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5622  in
    let disj =
      let uu____5625 =
        let uu____5626 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5626 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5625  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5645;_},e1::e2::[])
        ->
        let uu____5650 = p_tmDisjunction e1  in
        let uu____5655 = let uu____5660 = p_tmConjunction e2  in [uu____5660]
           in
        FStar_List.append uu____5650 uu____5655
    | uu____5669 -> let uu____5670 = p_tmConjunction e  in [uu____5670]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5680;_},e1::e2::[])
        ->
        let uu____5685 = p_tmConjunction e1  in
        let uu____5688 = let uu____5691 = p_tmTuple e2  in [uu____5691]  in
        FStar_List.append uu____5685 uu____5688
    | uu____5692 -> let uu____5693 = p_tmTuple e  in [uu____5693]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5710 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5710
          (fun uu____5718  ->
             match uu____5718 with | (e1,uu____5724) -> p_tmEq e1) args
    | uu____5725 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5730 =
             let uu____5731 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5731  in
           FStar_Pprint.group uu____5730)

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
               (let uu____5748 = FStar_Ident.text_of_id op  in
                uu____5748 = "="))
              ||
              (let uu____5750 = FStar_Ident.text_of_id op  in
               uu____5750 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5752 = levels op1  in
            (match uu____5752 with
             | (left1,mine,right1) ->
                 let uu____5762 =
                   let uu____5763 = FStar_All.pipe_left str op1  in
                   let uu____5764 = p_tmEqWith' p_X left1 e1  in
                   let uu____5765 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5763 uu____5764 uu____5765  in
                 paren_if_gt curr mine uu____5762)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5766;_},e1::e2::[])
            ->
            let uu____5771 =
              let uu____5772 = p_tmEqWith p_X e1  in
              let uu____5773 =
                let uu____5774 =
                  let uu____5775 =
                    let uu____5776 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5776  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5775  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5774  in
              FStar_Pprint.op_Hat_Hat uu____5772 uu____5773  in
            FStar_Pprint.group uu____5771
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5777;_},e1::[])
            ->
            let uu____5781 = levels "-"  in
            (match uu____5781 with
             | (left1,mine,right1) ->
                 let uu____5791 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5791)
        | uu____5792 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5836)::(e2,uu____5838)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5858 = is_list e  in Prims.op_Negation uu____5858)
              ->
              let op = "::"  in
              let uu____5860 = levels op  in
              (match uu____5860 with
               | (left1,mine,right1) ->
                   let uu____5870 =
                     let uu____5871 = str op  in
                     let uu____5872 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5873 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5871 uu____5872 uu____5873  in
                   paren_if_gt curr mine uu____5870)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5881 = levels op  in
              (match uu____5881 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5897 = p_binder false b  in
                     let uu____5898 =
                       let uu____5899 =
                         let uu____5900 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5900 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5899
                        in
                     FStar_Pprint.op_Hat_Hat uu____5897 uu____5898  in
                   let uu____5901 =
                     let uu____5902 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5903 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5902 uu____5903  in
                   paren_if_gt curr mine uu____5901)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5904;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5929 = levels op  in
              (match uu____5929 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5939 = str op  in
                     let uu____5940 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5941 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5939 uu____5940 uu____5941
                   else
                     (let uu____5943 =
                        let uu____5944 = str op  in
                        let uu____5945 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5946 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5944 uu____5945 uu____5946  in
                      paren_if_gt curr mine uu____5943))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5953 = levels op1  in
              (match uu____5953 with
               | (left1,mine,right1) ->
                   let uu____5963 =
                     let uu____5964 = str op1  in
                     let uu____5965 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5966 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5964 uu____5965 uu____5966  in
                   paren_if_gt curr mine uu____5963)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5985 =
                let uu____5986 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5987 =
                  let uu____5988 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5988 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5986 uu____5987  in
              braces_with_nesting uu____5985
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5993;_},e1::[])
              ->
              let uu____5997 =
                let uu____5998 = str "~"  in
                let uu____5999 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5998 uu____5999  in
              FStar_Pprint.group uu____5997
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6001;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6007 = levels op  in
                   (match uu____6007 with
                    | (left1,mine,right1) ->
                        let uu____6017 =
                          let uu____6018 = str op  in
                          let uu____6019 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6020 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6018 uu____6019 uu____6020  in
                        paren_if_gt curr mine uu____6017)
               | uu____6021 -> p_X e)
          | uu____6022 -> p_X e

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
        let uu____6029 =
          let uu____6030 = p_lident lid  in
          let uu____6031 =
            let uu____6032 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6032  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6030 uu____6031  in
        FStar_Pprint.group uu____6029
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6035 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6037 = p_appTerm e  in
    let uu____6038 =
      let uu____6039 =
        let uu____6040 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6040 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6039  in
    FStar_Pprint.op_Hat_Hat uu____6037 uu____6038

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6045 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6045 t phi
      | FStar_Parser_AST.TAnnotated uu____6046 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6051 ->
          let uu____6052 =
            let uu____6053 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6053
             in
          failwith uu____6052
      | FStar_Parser_AST.TVariable uu____6054 ->
          let uu____6055 =
            let uu____6056 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6056
             in
          failwith uu____6055
      | FStar_Parser_AST.NoName uu____6057 ->
          let uu____6058 =
            let uu____6059 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6059
             in
          failwith uu____6058

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6061  ->
      match uu____6061 with
      | (lid,e) ->
          let uu____6068 =
            let uu____6069 = p_qlident lid  in
            let uu____6070 =
              let uu____6071 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6071
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6069 uu____6070  in
          FStar_Pprint.group uu____6068

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6073 when is_general_application e ->
        let uu____6080 = head_and_args e  in
        (match uu____6080 with
         | (head1,args) ->
             let uu____6105 =
               let uu____6116 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6116
               then
                 let uu____6146 =
                   FStar_Util.take
                     (fun uu____6170  ->
                        match uu____6170 with
                        | (uu____6175,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6146 with
                 | (fs_typ_args,args1) ->
                     let uu____6213 =
                       let uu____6214 = p_indexingTerm head1  in
                       let uu____6215 =
                         let uu____6216 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6216 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6214 uu____6215  in
                     (uu____6213, args1)
               else
                 (let uu____6228 = p_indexingTerm head1  in
                  (uu____6228, args))
                in
             (match uu____6105 with
              | (head_doc,args1) ->
                  let uu____6249 =
                    let uu____6250 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6250 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6249))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6270 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6270)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6288 =
               let uu____6289 = p_quident lid  in
               let uu____6290 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6289 uu____6290  in
             FStar_Pprint.group uu____6288
         | hd1::tl1 ->
             let uu____6307 =
               let uu____6308 =
                 let uu____6309 =
                   let uu____6310 = p_quident lid  in
                   let uu____6311 = p_argTerm hd1  in
                   prefix2 uu____6310 uu____6311  in
                 FStar_Pprint.group uu____6309  in
               let uu____6312 =
                 let uu____6313 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6313  in
               FStar_Pprint.op_Hat_Hat uu____6308 uu____6312  in
             FStar_Pprint.group uu____6307)
    | uu____6318 -> p_indexingTerm e

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
         (let uu____6327 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6327 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6329 = str "#"  in
        let uu____6330 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6329 uu____6330
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6333 = str "#["  in
        let uu____6334 =
          let uu____6335 = p_indexingTerm t  in
          let uu____6336 =
            let uu____6337 = str "]"  in
            let uu____6338 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6337 uu____6338  in
          FStar_Pprint.op_Hat_Hat uu____6335 uu____6336  in
        FStar_Pprint.op_Hat_Hat uu____6333 uu____6334
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6340  ->
    match uu____6340 with | (e,uu____6346) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6351;_},e1::e2::[])
          ->
          let uu____6356 =
            let uu____6357 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6358 =
              let uu____6359 =
                let uu____6360 = p_term false false e2  in
                soft_parens_with_nesting uu____6360  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6359  in
            FStar_Pprint.op_Hat_Hat uu____6357 uu____6358  in
          FStar_Pprint.group uu____6356
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6361;_},e1::e2::[])
          ->
          let uu____6366 =
            let uu____6367 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6368 =
              let uu____6369 =
                let uu____6370 = p_term false false e2  in
                soft_brackets_with_nesting uu____6370  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6369  in
            FStar_Pprint.op_Hat_Hat uu____6367 uu____6368  in
          FStar_Pprint.group uu____6366
      | uu____6371 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6376 = p_quident lid  in
        let uu____6377 =
          let uu____6378 =
            let uu____6379 = p_term false false e1  in
            soft_parens_with_nesting uu____6379  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6378  in
        FStar_Pprint.op_Hat_Hat uu____6376 uu____6377
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6385 =
          let uu____6386 = FStar_Ident.text_of_id op  in str uu____6386  in
        let uu____6387 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6385 uu____6387
    | uu____6388 -> p_atomicTermNotQUident e

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
         | uu____6397 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6404 =
          let uu____6405 = FStar_Ident.text_of_id op  in str uu____6405  in
        let uu____6406 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6404 uu____6406
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6410 =
          let uu____6411 =
            let uu____6412 =
              let uu____6413 = FStar_Ident.text_of_id op  in str uu____6413
               in
            let uu____6414 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6412 uu____6414  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6411  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6410
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6429 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6430 =
          let uu____6431 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6432 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6431 p_tmEq uu____6432  in
        let uu____6439 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6429 uu____6430 uu____6439
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6442 =
          let uu____6443 = p_atomicTermNotQUident e1  in
          let uu____6444 =
            let uu____6445 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6445  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6443 uu____6444
           in
        FStar_Pprint.group uu____6442
    | uu____6446 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6451 = p_quident constr_lid  in
        let uu____6452 =
          let uu____6453 =
            let uu____6454 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6454  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6453  in
        FStar_Pprint.op_Hat_Hat uu____6451 uu____6452
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6456 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6456 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6458 = p_term false false e1  in
        soft_parens_with_nesting uu____6458
    | uu____6459 when is_array e ->
        let es = extract_from_list e  in
        let uu____6463 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6464 =
          let uu____6465 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6465
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6468 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6463 uu____6464 uu____6468
    | uu____6469 when is_list e ->
        let uu____6470 =
          let uu____6471 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6472 = extract_from_list e  in
          separate_map_or_flow_last uu____6471
            (fun ps  -> p_noSeqTerm ps false) uu____6472
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6470 FStar_Pprint.rbracket
    | uu____6477 when is_lex_list e ->
        let uu____6478 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6479 =
          let uu____6480 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6481 = extract_from_list e  in
          separate_map_or_flow_last uu____6480
            (fun ps  -> p_noSeqTerm ps false) uu____6481
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6478 uu____6479 FStar_Pprint.rbracket
    | uu____6486 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6490 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6491 =
          let uu____6492 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6492 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6490 uu____6491 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6496 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6497 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6496 uu____6497
    | FStar_Parser_AST.Op (op,args) when
        let uu____6504 = handleable_op op args  in
        Prims.op_Negation uu____6504 ->
        let uu____6505 =
          let uu____6506 =
            let uu____6507 = FStar_Ident.text_of_id op  in
            let uu____6508 =
              let uu____6509 =
                let uu____6510 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6510
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6509  in
            Prims.strcat uu____6507 uu____6508  in
          Prims.strcat "Operation " uu____6506  in
        failwith uu____6505
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6512 = str "u#"  in
        let uu____6513 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6512 uu____6513
    | FStar_Parser_AST.Wild  ->
        let uu____6514 = p_term false false e  in
        soft_parens_with_nesting uu____6514
    | FStar_Parser_AST.Const uu____6515 ->
        let uu____6516 = p_term false false e  in
        soft_parens_with_nesting uu____6516
    | FStar_Parser_AST.Op uu____6517 ->
        let uu____6524 = p_term false false e  in
        soft_parens_with_nesting uu____6524
    | FStar_Parser_AST.Tvar uu____6525 ->
        let uu____6526 = p_term false false e  in
        soft_parens_with_nesting uu____6526
    | FStar_Parser_AST.Var uu____6527 ->
        let uu____6528 = p_term false false e  in
        soft_parens_with_nesting uu____6528
    | FStar_Parser_AST.Name uu____6529 ->
        let uu____6530 = p_term false false e  in
        soft_parens_with_nesting uu____6530
    | FStar_Parser_AST.Construct uu____6531 ->
        let uu____6542 = p_term false false e  in
        soft_parens_with_nesting uu____6542
    | FStar_Parser_AST.Abs uu____6543 ->
        let uu____6550 = p_term false false e  in
        soft_parens_with_nesting uu____6550
    | FStar_Parser_AST.App uu____6551 ->
        let uu____6558 = p_term false false e  in
        soft_parens_with_nesting uu____6558
    | FStar_Parser_AST.Let uu____6559 ->
        let uu____6580 = p_term false false e  in
        soft_parens_with_nesting uu____6580
    | FStar_Parser_AST.LetOpen uu____6581 ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586
    | FStar_Parser_AST.Seq uu____6587 ->
        let uu____6592 = p_term false false e  in
        soft_parens_with_nesting uu____6592
    | FStar_Parser_AST.Bind uu____6593 ->
        let uu____6600 = p_term false false e  in
        soft_parens_with_nesting uu____6600
    | FStar_Parser_AST.If uu____6601 ->
        let uu____6608 = p_term false false e  in
        soft_parens_with_nesting uu____6608
    | FStar_Parser_AST.Match uu____6609 ->
        let uu____6624 = p_term false false e  in
        soft_parens_with_nesting uu____6624
    | FStar_Parser_AST.TryWith uu____6625 ->
        let uu____6640 = p_term false false e  in
        soft_parens_with_nesting uu____6640
    | FStar_Parser_AST.Ascribed uu____6641 ->
        let uu____6650 = p_term false false e  in
        soft_parens_with_nesting uu____6650
    | FStar_Parser_AST.Record uu____6651 ->
        let uu____6664 = p_term false false e  in
        soft_parens_with_nesting uu____6664
    | FStar_Parser_AST.Project uu____6665 ->
        let uu____6670 = p_term false false e  in
        soft_parens_with_nesting uu____6670
    | FStar_Parser_AST.Product uu____6671 ->
        let uu____6678 = p_term false false e  in
        soft_parens_with_nesting uu____6678
    | FStar_Parser_AST.Sum uu____6679 ->
        let uu____6686 = p_term false false e  in
        soft_parens_with_nesting uu____6686
    | FStar_Parser_AST.QForall uu____6687 ->
        let uu____6700 = p_term false false e  in
        soft_parens_with_nesting uu____6700
    | FStar_Parser_AST.QExists uu____6701 ->
        let uu____6714 = p_term false false e  in
        soft_parens_with_nesting uu____6714
    | FStar_Parser_AST.Refine uu____6715 ->
        let uu____6720 = p_term false false e  in
        soft_parens_with_nesting uu____6720
    | FStar_Parser_AST.NamedTyp uu____6721 ->
        let uu____6726 = p_term false false e  in
        soft_parens_with_nesting uu____6726
    | FStar_Parser_AST.Requires uu____6727 ->
        let uu____6734 = p_term false false e  in
        soft_parens_with_nesting uu____6734
    | FStar_Parser_AST.Ensures uu____6735 ->
        let uu____6742 = p_term false false e  in
        soft_parens_with_nesting uu____6742
    | FStar_Parser_AST.Attributes uu____6743 ->
        let uu____6746 = p_term false false e  in
        soft_parens_with_nesting uu____6746
    | FStar_Parser_AST.Quote uu____6747 ->
        let uu____6752 = p_term false false e  in
        soft_parens_with_nesting uu____6752
    | FStar_Parser_AST.VQuote uu____6753 ->
        let uu____6754 = p_term false false e  in
        soft_parens_with_nesting uu____6754
    | FStar_Parser_AST.Antiquote uu____6755 ->
        let uu____6756 = p_term false false e  in
        soft_parens_with_nesting uu____6756

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___119_6757  ->
    match uu___119_6757 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6763) ->
        let uu____6764 = str s  in FStar_Pprint.dquotes uu____6764
    | FStar_Const.Const_bytearray (bytes,uu____6766) ->
        let uu____6771 =
          let uu____6772 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6772  in
        let uu____6773 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6771 uu____6773
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___117_6793 =
          match uu___117_6793 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___118_6799 =
          match uu___118_6799 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6810  ->
               match uu____6810 with
               | (s,w) ->
                   let uu____6817 = signedness s  in
                   let uu____6818 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6817 uu____6818)
            sign_width_opt
           in
        let uu____6819 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6819 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6821 = FStar_Range.string_of_range r  in str uu____6821
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6823 = p_quident lid  in
        let uu____6824 =
          let uu____6825 =
            let uu____6826 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6826  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6825  in
        FStar_Pprint.op_Hat_Hat uu____6823 uu____6824

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6828 = str "u#"  in
    let uu____6829 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6828 uu____6829

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6831;_},u1::u2::[])
        ->
        let uu____6836 =
          let uu____6837 = p_universeFrom u1  in
          let uu____6838 =
            let uu____6839 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6839  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6837 uu____6838  in
        FStar_Pprint.group uu____6836
    | FStar_Parser_AST.App uu____6840 ->
        let uu____6847 = head_and_args u  in
        (match uu____6847 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6873 =
                    let uu____6874 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6875 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6883  ->
                           match uu____6883 with
                           | (u1,uu____6889) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6874 uu____6875  in
                  FStar_Pprint.group uu____6873
              | uu____6890 ->
                  let uu____6891 =
                    let uu____6892 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6892
                     in
                  failwith uu____6891))
    | uu____6893 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6916 = FStar_Ident.text_of_id id1  in str uu____6916
    | FStar_Parser_AST.Paren u1 ->
        let uu____6918 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6918
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6919;_},uu____6920::uu____6921::[])
        ->
        let uu____6924 = p_universeFrom u  in
        soft_parens_with_nesting uu____6924
    | FStar_Parser_AST.App uu____6925 ->
        let uu____6932 = p_universeFrom u  in
        soft_parens_with_nesting uu____6932
    | uu____6933 ->
        let uu____6934 =
          let uu____6935 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6935
           in
        failwith uu____6934

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
       | FStar_Parser_AST.Module (uu____7007,decls) ->
           let uu____7013 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7013
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7022,decls,uu____7024) ->
           let uu____7029 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7029
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7082  ->
         match uu____7082 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7126,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7132,decls,uu____7134) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7179 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7192;
                 FStar_Parser_AST.doc = uu____7193;
                 FStar_Parser_AST.quals = uu____7194;
                 FStar_Parser_AST.attrs = uu____7195;_}::uu____7196 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7202 =
                   let uu____7205 =
                     let uu____7208 = FStar_List.tl ds  in d :: uu____7208
                      in
                   d0 :: uu____7205  in
                 (uu____7202, (d0.FStar_Parser_AST.drange))
             | uu____7213 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7179 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7273 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7273 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7369 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7369, comments1))))))
  