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
  fun uu___104_1220  ->
    match uu___104_1220 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___105_1245  ->
      match uu___105_1245 with
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
  let levels_from_associativity l uu___106_1432 =
    match uu___106_1432 with
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
        let rec p_list' uu___107_3445 =
          match uu___107_3445 with
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
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3471 =
          let uu____3472 = str "module"  in
          let uu____3473 =
            let uu____3474 =
              let uu____3475 = p_uident uid1  in
              let uu____3476 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3475 uu____3476  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3474  in
          FStar_Pprint.op_Hat_Hat uu____3472 uu____3473  in
        let uu____3477 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3471 uu____3477
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3479 =
          let uu____3480 = str "module"  in
          let uu____3481 =
            let uu____3482 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3482  in
          FStar_Pprint.op_Hat_Hat uu____3480 uu____3481  in
        FStar_Pprint.group uu____3479
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3515 = str "effect"  in
          let uu____3516 =
            let uu____3517 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3517  in
          FStar_Pprint.op_Hat_Hat uu____3515 uu____3516  in
        let uu____3518 =
          let uu____3519 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3519 FStar_Pprint.equals
           in
        let uu____3520 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3518 uu____3520
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3538 =
          let uu____3539 = str "type"  in
          let uu____3540 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3539 uu____3540  in
        let uu____3553 =
          let uu____3554 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3592 =
                    let uu____3593 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3593 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3592)) uu____3554
           in
        FStar_Pprint.op_Hat_Hat uu____3538 uu____3553
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3609 = str "let"  in
          let uu____3610 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3609 uu____3610  in
        let uu____3611 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3611 p_letbinding lbs
          (fun uu____3619  ->
             match uu____3619 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3628 = str "val"  in
        let uu____3629 =
          let uu____3630 =
            let uu____3631 = p_lident lid  in
            let uu____3632 =
              let uu____3633 =
                let uu____3634 =
                  let uu____3635 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3635  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3634  in
              FStar_Pprint.group uu____3633  in
            FStar_Pprint.op_Hat_Hat uu____3631 uu____3632  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3630  in
        FStar_Pprint.op_Hat_Hat uu____3628 uu____3629
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3639 =
            let uu____3640 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3640 FStar_Util.is_upper  in
          if uu____3639
          then FStar_Pprint.empty
          else
            (let uu____3644 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3644 FStar_Pprint.space)
           in
        let uu____3645 =
          let uu____3646 = p_ident id1  in
          let uu____3647 =
            let uu____3648 =
              let uu____3649 =
                let uu____3650 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3650  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3649  in
            FStar_Pprint.group uu____3648  in
          FStar_Pprint.op_Hat_Hat uu____3646 uu____3647  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3645
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3657 = str "exception"  in
        let uu____3658 =
          let uu____3659 =
            let uu____3660 = p_uident uid  in
            let uu____3661 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3665 =
                     let uu____3666 = str "of"  in
                     let uu____3667 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3666 uu____3667  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3665) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3660 uu____3661  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3659  in
        FStar_Pprint.op_Hat_Hat uu____3657 uu____3658
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3669 = str "new_effect"  in
        let uu____3670 =
          let uu____3671 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3671  in
        FStar_Pprint.op_Hat_Hat uu____3669 uu____3670
    | FStar_Parser_AST.SubEffect se ->
        let uu____3673 = str "sub_effect"  in
        let uu____3674 =
          let uu____3675 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3675  in
        FStar_Pprint.op_Hat_Hat uu____3673 uu____3674
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3678 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3678 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3679 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3680) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3703 = str "%splice"  in
        let uu____3704 =
          let uu____3705 =
            let uu____3706 = str ";"  in p_list p_uident uu____3706 ids  in
          let uu____3707 =
            let uu____3708 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3708  in
          FStar_Pprint.op_Hat_Hat uu____3705 uu____3707  in
        FStar_Pprint.op_Hat_Hat uu____3703 uu____3704

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___108_3709  ->
    match uu___108_3709 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3711 = str "#set-options"  in
        let uu____3712 =
          let uu____3713 =
            let uu____3714 = str s  in FStar_Pprint.dquotes uu____3714  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3713  in
        FStar_Pprint.op_Hat_Hat uu____3711 uu____3712
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3718 = str "#reset-options"  in
        let uu____3719 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3723 =
                 let uu____3724 = str s  in FStar_Pprint.dquotes uu____3724
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3723) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3718 uu____3719
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3728 = str "#push-options"  in
        let uu____3729 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3733 =
                 let uu____3734 = str s  in FStar_Pprint.dquotes uu____3734
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3733) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3728 uu____3729
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
    fun uu____3759  ->
      match uu____3759 with
      | (typedecl,fsdoc_opt) ->
          let uu____3772 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3772 with
           | (decl,body) ->
               let uu____3790 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3790)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___109_3792  ->
      match uu___109_3792 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3822 = FStar_Pprint.empty  in
          let uu____3823 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3823, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3844 =
            let uu____3845 = p_typ false false t  in jump2 uu____3845  in
          let uu____3846 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3846, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3900 =
            match uu____3900 with
            | (lid1,t,doc_opt) ->
                let uu____3916 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3916
             in
          let p_fields uu____3932 =
            let uu____3933 =
              let uu____3934 =
                let uu____3935 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3935 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3934  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3933  in
          let uu____3944 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3944, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4005 =
            match uu____4005 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4031 =
                    let uu____4032 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4032  in
                  FStar_Range.extend_to_end_of_line uu____4031  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4058 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4071 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4071,
            ((fun uu____4077  ->
                let uu____4078 = datacon_doc ()  in jump2 uu____4078)))

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
  fun uu____4079  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4079 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4113 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4113  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4115 =
                        let uu____4118 =
                          let uu____4121 = p_fsdoc fsdoc  in
                          let uu____4122 =
                            let uu____4125 = cont lid_doc  in [uu____4125]
                             in
                          uu____4121 :: uu____4122  in
                        kw :: uu____4118  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4115
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4130 =
                        let uu____4131 =
                          let uu____4132 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4132 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4131
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4130
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4147 =
                          let uu____4148 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4148  in
                        prefix2 uu____4147 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4150  ->
      match uu____4150 with
      | (lid,t,doc_opt) ->
          let uu____4166 =
            let uu____4167 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4168 =
              let uu____4169 = p_lident lid  in
              let uu____4170 =
                let uu____4171 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4171  in
              FStar_Pprint.op_Hat_Hat uu____4169 uu____4170  in
            FStar_Pprint.op_Hat_Hat uu____4167 uu____4168  in
          FStar_Pprint.group uu____4166

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4172  ->
    match uu____4172 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4200 =
            let uu____4201 =
              let uu____4202 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4202  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4201  in
          FStar_Pprint.group uu____4200  in
        let uu____4203 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4204 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4208 =
                 let uu____4209 =
                   let uu____4210 =
                     let uu____4211 =
                       let uu____4212 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4212
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4211  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4210  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4209  in
               FStar_Pprint.group uu____4208) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4203 uu____4204

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4214  ->
      match uu____4214 with
      | (pat,uu____4220) ->
          let uu____4221 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4240 =
                  let uu____4241 =
                    let uu____4242 =
                      let uu____4243 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4243
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4242  in
                  FStar_Pprint.group uu____4241  in
                (pat1, uu____4240)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4255 =
                  let uu____4256 =
                    let uu____4257 =
                      let uu____4258 =
                        let uu____4259 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4259
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4258
                       in
                    FStar_Pprint.group uu____4257  in
                  let uu____4260 =
                    let uu____4261 =
                      let uu____4262 = str "by"  in
                      let uu____4263 =
                        let uu____4264 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4264
                         in
                      FStar_Pprint.op_Hat_Hat uu____4262 uu____4263  in
                    FStar_Pprint.group uu____4261  in
                  FStar_Pprint.op_Hat_Hat uu____4256 uu____4260  in
                (pat1, uu____4255)
            | uu____4265 -> (pat, FStar_Pprint.empty)  in
          (match uu____4221 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4269);
                       FStar_Parser_AST.prange = uu____4270;_},pats)
                    ->
                    let uu____4280 =
                      let uu____4281 =
                        let uu____4282 =
                          let uu____4283 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4283  in
                        FStar_Pprint.group uu____4282  in
                      let uu____4284 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4281 uu____4284  in
                    prefix2_nonempty uu____4280 ascr_doc
                | uu____4285 ->
                    let uu____4286 =
                      let uu____4287 =
                        let uu____4288 =
                          let uu____4289 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4289  in
                        FStar_Pprint.group uu____4288  in
                      FStar_Pprint.op_Hat_Hat uu____4287 ascr_doc  in
                    FStar_Pprint.group uu____4286))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4291  ->
      match uu____4291 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4300 =
            let uu____4301 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4301  in
          let uu____4302 =
            let uu____4303 =
              let uu____4304 =
                let uu____4305 =
                  let uu____4306 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4306  in
                FStar_Pprint.group uu____4305  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4304  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4303  in
          FStar_Pprint.ifflat uu____4300 uu____4302

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___110_4307  ->
    match uu___110_4307 with
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
        let uu____4332 = p_uident uid  in
        let uu____4333 = p_binders true bs  in
        let uu____4334 =
          let uu____4335 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4335  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4332 uu____4333 uu____4334

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
          let uu____4345 =
            let uu____4346 =
              let uu____4347 =
                let uu____4348 = p_uident uid  in
                let uu____4349 = p_binders true bs  in
                let uu____4350 =
                  let uu____4351 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4351  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4348 uu____4349 uu____4350
                 in
              FStar_Pprint.group uu____4347  in
            let uu____4352 =
              let uu____4353 = str "with"  in
              let uu____4354 =
                let uu____4355 =
                  let uu____4356 =
                    let uu____4357 =
                      let uu____4358 =
                        let uu____4359 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4359
                         in
                      separate_map_last uu____4358 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4357  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4356  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4355  in
              FStar_Pprint.op_Hat_Hat uu____4353 uu____4354  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4346 uu____4352  in
          braces_with_nesting uu____4345

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,(FStar_Parser_AST.TyconAbbrev
             (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
             )::[])
          ->
          let uu____4390 =
            let uu____4391 = p_lident lid  in
            let uu____4392 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4391 uu____4392  in
          let uu____4393 = p_simpleTerm ps false e  in
          prefix2 uu____4390 uu____4393
      | uu____4394 ->
          let uu____4395 =
            let uu____4396 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4396
             in
          failwith uu____4395

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4458 =
        match uu____4458 with
        | (kwd,t) ->
            let uu____4465 =
              let uu____4466 = str kwd  in
              let uu____4467 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4466 uu____4467  in
            let uu____4468 = p_simpleTerm ps false t  in
            prefix2 uu____4465 uu____4468
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4473 =
      let uu____4474 =
        let uu____4475 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4476 =
          let uu____4477 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4477  in
        FStar_Pprint.op_Hat_Hat uu____4475 uu____4476  in
      let uu____4478 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4474 uu____4478  in
    let uu____4479 =
      let uu____4480 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4480  in
    FStar_Pprint.op_Hat_Hat uu____4473 uu____4479

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___111_4481  ->
    match uu___111_4481 with
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
    | uu____4483 ->
        let uu____4484 =
          let uu____4485 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4485  in
        FStar_Pprint.op_Hat_Hat uu____4484 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___112_4488  ->
    match uu___112_4488 with
    | FStar_Parser_AST.Rec  ->
        let uu____4489 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4489
    | FStar_Parser_AST.Mutable  ->
        let uu____4490 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4490
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___113_4491  ->
    match uu___113_4491 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4493 = str "#["  in
        let uu____4494 =
          let uu____4495 = p_term false false t  in
          let uu____4496 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4495 uu____4496  in
        FStar_Pprint.op_Hat_Hat uu____4493 uu____4494

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4501 =
          let uu____4502 =
            let uu____4503 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4503  in
          FStar_Pprint.separate_map uu____4502 p_tuplePattern pats  in
        FStar_Pprint.group uu____4501
    | uu____4504 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4511 =
          let uu____4512 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4512 p_constructorPattern pats  in
        FStar_Pprint.group uu____4511
    | uu____4513 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4516;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4521 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4522 = p_constructorPattern hd1  in
        let uu____4523 = p_constructorPattern tl1  in
        infix0 uu____4521 uu____4522 uu____4523
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4525;_},pats)
        ->
        let uu____4531 = p_quident uid  in
        let uu____4532 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4531 uu____4532
    | uu____4533 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4549;
               FStar_Parser_AST.blevel = uu____4550;
               FStar_Parser_AST.aqual = uu____4551;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4559 =
               let uu____4560 = p_ident lid  in
               p_refinement aqual uu____4560 t1 phi  in
             soft_parens_with_nesting uu____4559
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4562;
               FStar_Parser_AST.blevel = uu____4563;
               FStar_Parser_AST.aqual = uu____4564;_},phi))
             ->
             let uu____4568 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4568
         | uu____4569 ->
             let uu____4574 =
               let uu____4575 = p_tuplePattern pat  in
               let uu____4576 =
                 let uu____4577 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4577
                  in
               FStar_Pprint.op_Hat_Hat uu____4575 uu____4576  in
             soft_parens_with_nesting uu____4574)
    | FStar_Parser_AST.PatList pats ->
        let uu____4581 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4581 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4598 =
          match uu____4598 with
          | (lid,pat) ->
              let uu____4605 = p_qlident lid  in
              let uu____4606 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4605 uu____4606
           in
        let uu____4607 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4607
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4617 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4618 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4619 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4617 uu____4618 uu____4619
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4628 =
          let uu____4629 =
            let uu____4630 =
              let uu____4631 = FStar_Ident.text_of_id op  in str uu____4631
               in
            let uu____4632 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4630 uu____4632  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4629  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4628
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4640 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4641 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4640 uu____4641
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4643 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4646;
           FStar_Parser_AST.prange = uu____4647;_},uu____4648)
        ->
        let uu____4653 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4653
    | FStar_Parser_AST.PatTuple (uu____4654,false ) ->
        let uu____4659 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4659
    | uu____4660 ->
        let uu____4661 =
          let uu____4662 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4662  in
        failwith uu____4661

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4664;_},uu____4665)
        -> true
    | uu____4670 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4674 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4675 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4674 uu____4675
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4682;
                   FStar_Parser_AST.blevel = uu____4683;
                   FStar_Parser_AST.aqual = uu____4684;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4688 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4688 t1 phi
            | uu____4689 ->
                let t' =
                  let uu____4691 = is_typ_tuple t  in
                  if uu____4691
                  then
                    let uu____4692 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4692
                  else p_tmFormula t  in
                let uu____4694 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4695 =
                  let uu____4696 = p_lident lid  in
                  let uu____4697 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4696 uu____4697  in
                FStar_Pprint.op_Hat_Hat uu____4694 uu____4695
             in
          if is_atomic
          then
            let uu____4698 =
              let uu____4699 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4699  in
            FStar_Pprint.group uu____4698
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4701 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4708;
                  FStar_Parser_AST.blevel = uu____4709;
                  FStar_Parser_AST.aqual = uu____4710;_},phi)
               ->
               if is_atomic
               then
                 let uu____4714 =
                   let uu____4715 =
                     let uu____4716 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4716 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4715  in
                 FStar_Pprint.group uu____4714
               else
                 (let uu____4718 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4718)
           | uu____4719 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4728 -> false
            | FStar_Parser_AST.App uu____4739 -> false
            | FStar_Parser_AST.Op uu____4746 -> false
            | uu____4753 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4757 =
            let uu____4758 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4759 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4758 uu____4759  in
          let uu____4760 =
            let uu____4761 = p_appTerm t  in
            let uu____4762 =
              let uu____4763 =
                let uu____4764 =
                  let uu____4765 = soft_braces_with_nesting_tight phi1  in
                  let uu____4766 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4765 uu____4766  in
                FStar_Pprint.group uu____4764  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4763
               in
            FStar_Pprint.op_Hat_Hat uu____4761 uu____4762  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4757 uu____4760

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4777 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4777

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4782 = FStar_Ident.text_of_id lid  in str uu____4782)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4785 = FStar_Ident.text_of_lid lid  in str uu____4785)

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
            let uu____4803 =
              let uu____4804 =
                let uu____4805 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4805 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4804  in
            let uu____4806 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4803 uu____4806
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4810 =
              let uu____4811 =
                let uu____4812 =
                  let uu____4813 = p_lident x  in
                  let uu____4814 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4813 uu____4814  in
                let uu____4815 =
                  let uu____4816 = p_noSeqTerm true false e1  in
                  let uu____4817 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4816 uu____4817  in
                op_Hat_Slash_Plus_Hat uu____4812 uu____4815  in
              FStar_Pprint.group uu____4811  in
            let uu____4818 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4810 uu____4818
        | uu____4819 ->
            let uu____4820 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4820

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
            let uu____4831 =
              let uu____4832 = p_tmIff e1  in
              let uu____4833 =
                let uu____4834 =
                  let uu____4835 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4835
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4834  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4832 uu____4833  in
            FStar_Pprint.group uu____4831
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4841 =
              let uu____4842 = p_tmIff e1  in
              let uu____4843 =
                let uu____4844 =
                  let uu____4845 =
                    let uu____4846 = p_typ false false t  in
                    let uu____4847 =
                      let uu____4848 = str "by"  in
                      let uu____4849 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4848 uu____4849  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4846 uu____4847  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4845
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4844  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4842 uu____4843  in
            FStar_Pprint.group uu____4841
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4850;_},e1::e2::e3::[])
            ->
            let uu____4856 =
              let uu____4857 =
                let uu____4858 =
                  let uu____4859 = p_atomicTermNotQUident e1  in
                  let uu____4860 =
                    let uu____4861 =
                      let uu____4862 =
                        let uu____4863 = p_term false false e2  in
                        soft_parens_with_nesting uu____4863  in
                      let uu____4864 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4862 uu____4864  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4861  in
                  FStar_Pprint.op_Hat_Hat uu____4859 uu____4860  in
                FStar_Pprint.group uu____4858  in
              let uu____4865 =
                let uu____4866 = p_noSeqTerm ps pb e3  in jump2 uu____4866
                 in
              FStar_Pprint.op_Hat_Hat uu____4857 uu____4865  in
            FStar_Pprint.group uu____4856
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4867;_},e1::e2::e3::[])
            ->
            let uu____4873 =
              let uu____4874 =
                let uu____4875 =
                  let uu____4876 = p_atomicTermNotQUident e1  in
                  let uu____4877 =
                    let uu____4878 =
                      let uu____4879 =
                        let uu____4880 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4880  in
                      let uu____4881 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4879 uu____4881  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4878  in
                  FStar_Pprint.op_Hat_Hat uu____4876 uu____4877  in
                FStar_Pprint.group uu____4875  in
              let uu____4882 =
                let uu____4883 = p_noSeqTerm ps pb e3  in jump2 uu____4883
                 in
              FStar_Pprint.op_Hat_Hat uu____4874 uu____4882  in
            FStar_Pprint.group uu____4873
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4891 =
              let uu____4892 = str "requires"  in
              let uu____4893 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4892 uu____4893  in
            FStar_Pprint.group uu____4891
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4901 =
              let uu____4902 = str "ensures"  in
              let uu____4903 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4902 uu____4903  in
            FStar_Pprint.group uu____4901
        | FStar_Parser_AST.Attributes es ->
            let uu____4907 =
              let uu____4908 = str "attributes"  in
              let uu____4909 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4908 uu____4909  in
            FStar_Pprint.group uu____4907
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4913 =
                let uu____4914 =
                  let uu____4915 = str "if"  in
                  let uu____4916 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4915 uu____4916  in
                let uu____4917 =
                  let uu____4918 = str "then"  in
                  let uu____4919 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4918 uu____4919  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4914 uu____4917  in
              FStar_Pprint.group uu____4913
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4922,uu____4923,e31) when
                     is_unit e31 ->
                     let uu____4925 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4925
                 | uu____4926 -> p_noSeqTerm false false e2  in
               let uu____4927 =
                 let uu____4928 =
                   let uu____4929 = str "if"  in
                   let uu____4930 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4929 uu____4930  in
                 let uu____4931 =
                   let uu____4932 =
                     let uu____4933 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4933 e2_doc  in
                   let uu____4934 =
                     let uu____4935 = str "else"  in
                     let uu____4936 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4935 uu____4936  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4932 uu____4934  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4928 uu____4931  in
               FStar_Pprint.group uu____4927)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4959 =
              let uu____4960 =
                let uu____4961 =
                  let uu____4962 = str "try"  in
                  let uu____4963 = p_noSeqTerm false false e1  in
                  prefix2 uu____4962 uu____4963  in
                let uu____4964 =
                  let uu____4965 = str "with"  in
                  let uu____4966 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4965 uu____4966  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4961 uu____4964  in
              FStar_Pprint.group uu____4960  in
            let uu____4975 = paren_if (ps || pb)  in uu____4975 uu____4959
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5002 =
              let uu____5003 =
                let uu____5004 =
                  let uu____5005 = str "match"  in
                  let uu____5006 = p_noSeqTerm false false e1  in
                  let uu____5007 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5005 uu____5006 uu____5007
                   in
                let uu____5008 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5004 uu____5008  in
              FStar_Pprint.group uu____5003  in
            let uu____5017 = paren_if (ps || pb)  in uu____5017 uu____5002
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5024 =
              let uu____5025 =
                let uu____5026 =
                  let uu____5027 = str "let open"  in
                  let uu____5028 = p_quident uid  in
                  let uu____5029 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5027 uu____5028 uu____5029
                   in
                let uu____5030 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5026 uu____5030  in
              FStar_Pprint.group uu____5025  in
            let uu____5031 = paren_if ps  in uu____5031 uu____5024
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5095 is_last =
              match uu____5095 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5128 =
                          let uu____5129 = str "let"  in
                          let uu____5130 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5129 uu____5130
                           in
                        FStar_Pprint.group uu____5128
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5131 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5136 =
                    if is_last
                    then
                      let uu____5137 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5138 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5137 doc_expr uu____5138
                    else
                      (let uu____5140 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5140)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5136
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5186 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5186
                     else
                       (let uu____5194 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5194)) lbs
               in
            let lbs_doc =
              let uu____5202 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5202  in
            let uu____5203 =
              let uu____5204 =
                let uu____5205 =
                  let uu____5206 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5206
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5205  in
              FStar_Pprint.group uu____5204  in
            let uu____5207 = paren_if ps  in uu____5207 uu____5203
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5214;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5217;
                                                             FStar_Parser_AST.level
                                                               = uu____5218;_})
            when matches_var maybe_x x ->
            let uu____5245 =
              let uu____5246 =
                let uu____5247 = str "function"  in
                let uu____5248 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5247 uu____5248  in
              FStar_Pprint.group uu____5246  in
            let uu____5257 = paren_if (ps || pb)  in uu____5257 uu____5245
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5263 =
              let uu____5264 = str "quote"  in
              let uu____5265 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5265  in
            FStar_Pprint.group uu____5263
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5267 =
              let uu____5268 = str "`"  in
              let uu____5269 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5268 uu____5269  in
            FStar_Pprint.group uu____5267
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5271 =
              let uu____5272 = str "`%"  in
              let uu____5273 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5272 uu____5273  in
            FStar_Pprint.group uu____5271
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5275 =
              let uu____5276 = str "`#"  in
              let uu____5277 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5276 uu____5277  in
            FStar_Pprint.group uu____5275
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5279 =
              let uu____5280 = str "`@"  in
              let uu____5281 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5280 uu____5281  in
            FStar_Pprint.group uu____5279
        | uu____5282 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___114_5283  ->
    match uu___114_5283 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5295 =
          let uu____5296 = str "[@"  in
          let uu____5297 =
            let uu____5298 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5299 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5298 uu____5299  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5296 uu____5297  in
        FStar_Pprint.group uu____5295

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
                 let uu____5325 =
                   let uu____5326 =
                     let uu____5327 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5327 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5326 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5325 term_doc
             | pats ->
                 let uu____5333 =
                   let uu____5334 =
                     let uu____5335 =
                       let uu____5336 =
                         let uu____5337 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5337
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5336 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5338 = p_trigger trigger  in
                     prefix2 uu____5335 uu____5338  in
                   FStar_Pprint.group uu____5334  in
                 prefix2 uu____5333 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5358 =
                   let uu____5359 =
                     let uu____5360 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5360 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5359 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5358 term_doc
             | pats ->
                 let uu____5366 =
                   let uu____5367 =
                     let uu____5368 =
                       let uu____5369 =
                         let uu____5370 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5370
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5369 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5371 = p_trigger trigger  in
                     prefix2 uu____5368 uu____5371  in
                   FStar_Pprint.group uu____5367  in
                 prefix2 uu____5366 term_doc)
        | uu____5372 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5374 -> str "forall"
    | FStar_Parser_AST.QExists uu____5387 -> str "exists"
    | uu____5400 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___115_5401  ->
    match uu___115_5401 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5413 =
          let uu____5414 =
            let uu____5415 =
              let uu____5416 = str "pattern"  in
              let uu____5417 =
                let uu____5418 =
                  let uu____5419 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5419
                   in
                FStar_Pprint.op_Hat_Hat uu____5418 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5416 uu____5417  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5415  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5414  in
        FStar_Pprint.group uu____5413

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5425 = str "\\/"  in
    FStar_Pprint.separate_map uu____5425 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5431 =
      let uu____5432 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5432 p_appTerm pats  in
    FStar_Pprint.group uu____5431

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5442 =
              let uu____5443 =
                let uu____5444 = str "fun"  in
                let uu____5445 =
                  let uu____5446 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5446
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5444 uu____5445  in
              let uu____5447 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5443 uu____5447  in
            let uu____5448 = paren_if ps  in uu____5448 uu____5442
        | uu____5453 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5457  ->
      match uu____5457 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5480 =
                    let uu____5481 =
                      let uu____5482 =
                        let uu____5483 = p_tuplePattern p  in
                        let uu____5484 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5483 uu____5484  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5482
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5481  in
                  FStar_Pprint.group uu____5480
              | FStar_Pervasives_Native.Some f ->
                  let uu____5486 =
                    let uu____5487 =
                      let uu____5488 =
                        let uu____5489 =
                          let uu____5490 =
                            let uu____5491 = p_tuplePattern p  in
                            let uu____5492 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5491
                              uu____5492
                             in
                          FStar_Pprint.group uu____5490  in
                        let uu____5493 =
                          let uu____5494 =
                            let uu____5497 = p_tmFormula f  in
                            [uu____5497; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5494  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5489 uu____5493
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5488
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5487  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5486
               in
            let uu____5498 =
              let uu____5499 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5499  in
            FStar_Pprint.group uu____5498  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5508 =
                      let uu____5509 =
                        let uu____5510 =
                          let uu____5511 =
                            let uu____5512 =
                              let uu____5513 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5513  in
                            FStar_Pprint.separate_map uu____5512
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5511
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5510
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5509  in
                    FStar_Pprint.group uu____5508
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5514 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5516;_},e1::e2::[])
        ->
        let uu____5521 = str "<==>"  in
        let uu____5522 = p_tmImplies e1  in
        let uu____5523 = p_tmIff e2  in
        infix0 uu____5521 uu____5522 uu____5523
    | uu____5524 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5526;_},e1::e2::[])
        ->
        let uu____5531 = str "==>"  in
        let uu____5532 = p_tmArrow p_tmFormula e1  in
        let uu____5533 = p_tmImplies e2  in
        infix0 uu____5531 uu____5532 uu____5533
    | uu____5534 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5542 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5542 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5563 ->
               let uu____5564 =
                 let uu____5565 =
                   let uu____5566 =
                     let uu____5567 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5567
                      in
                   FStar_Pprint.separate uu____5566 terms  in
                 let uu____5568 =
                   let uu____5569 =
                     let uu____5570 =
                       let uu____5571 =
                         let uu____5572 =
                           let uu____5573 =
                             let uu____5574 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5574
                              in
                           FStar_Pprint.separate uu____5573 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5572 last_op  in
                       let uu____5575 =
                         let uu____5576 =
                           let uu____5577 =
                             let uu____5578 =
                               let uu____5579 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5579
                                in
                             FStar_Pprint.separate uu____5578 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5577 last_op  in
                         jump2 uu____5576  in
                       FStar_Pprint.ifflat uu____5571 uu____5575  in
                     FStar_Pprint.group uu____5570  in
                   let uu____5580 = FStar_List.hd last1  in
                   prefix2 uu____5569 uu____5580  in
                 FStar_Pprint.ifflat uu____5565 uu____5568  in
               FStar_Pprint.group uu____5564)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5593 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5598 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5593 uu____5598
      | uu____5601 -> let uu____5602 = p_Tm e  in [uu____5602]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5605 =
        let uu____5606 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5606 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5605  in
    let disj =
      let uu____5608 =
        let uu____5609 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5609 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5608  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5628;_},e1::e2::[])
        ->
        let uu____5633 = p_tmDisjunction e1  in
        let uu____5638 = let uu____5643 = p_tmConjunction e2  in [uu____5643]
           in
        FStar_List.append uu____5633 uu____5638
    | uu____5652 -> let uu____5653 = p_tmConjunction e  in [uu____5653]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5663;_},e1::e2::[])
        ->
        let uu____5668 = p_tmConjunction e1  in
        let uu____5671 = let uu____5674 = p_tmTuple e2  in [uu____5674]  in
        FStar_List.append uu____5668 uu____5671
    | uu____5675 -> let uu____5676 = p_tmTuple e  in [uu____5676]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5693 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5693
          (fun uu____5701  ->
             match uu____5701 with | (e1,uu____5707) -> p_tmEq e1) args
    | uu____5708 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5713 =
             let uu____5714 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5714  in
           FStar_Pprint.group uu____5713)

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
               (let uu____5731 = FStar_Ident.text_of_id op  in
                uu____5731 = "="))
              ||
              (let uu____5733 = FStar_Ident.text_of_id op  in
               uu____5733 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5735 = levels op1  in
            (match uu____5735 with
             | (left1,mine,right1) ->
                 let uu____5745 =
                   let uu____5746 = FStar_All.pipe_left str op1  in
                   let uu____5747 = p_tmEqWith' p_X left1 e1  in
                   let uu____5748 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5746 uu____5747 uu____5748  in
                 paren_if_gt curr mine uu____5745)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5749;_},e1::e2::[])
            ->
            let uu____5754 =
              let uu____5755 = p_tmEqWith p_X e1  in
              let uu____5756 =
                let uu____5757 =
                  let uu____5758 =
                    let uu____5759 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5759  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5758  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5757  in
              FStar_Pprint.op_Hat_Hat uu____5755 uu____5756  in
            FStar_Pprint.group uu____5754
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5760;_},e1::[])
            ->
            let uu____5764 = levels "-"  in
            (match uu____5764 with
             | (left1,mine,right1) ->
                 let uu____5774 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5774)
        | uu____5775 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5819)::(e2,uu____5821)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5841 = is_list e  in Prims.op_Negation uu____5841)
              ->
              let op = "::"  in
              let uu____5843 = levels op  in
              (match uu____5843 with
               | (left1,mine,right1) ->
                   let uu____5853 =
                     let uu____5854 = str op  in
                     let uu____5855 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5856 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5854 uu____5855 uu____5856  in
                   paren_if_gt curr mine uu____5853)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5864 = levels op  in
              (match uu____5864 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5880 = p_binder false b  in
                     let uu____5881 =
                       let uu____5882 =
                         let uu____5883 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5883 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5882
                        in
                     FStar_Pprint.op_Hat_Hat uu____5880 uu____5881  in
                   let uu____5884 =
                     let uu____5885 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5886 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5885 uu____5886  in
                   paren_if_gt curr mine uu____5884)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5887;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5912 = levels op  in
              (match uu____5912 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5922 = str op  in
                     let uu____5923 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5924 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5922 uu____5923 uu____5924
                   else
                     (let uu____5926 =
                        let uu____5927 = str op  in
                        let uu____5928 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5929 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5927 uu____5928 uu____5929  in
                      paren_if_gt curr mine uu____5926))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5936 = levels op1  in
              (match uu____5936 with
               | (left1,mine,right1) ->
                   let uu____5946 =
                     let uu____5947 = str op1  in
                     let uu____5948 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5949 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5947 uu____5948 uu____5949  in
                   paren_if_gt curr mine uu____5946)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5968 =
                let uu____5969 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5970 =
                  let uu____5971 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5971 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5969 uu____5970  in
              braces_with_nesting uu____5968
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5976;_},e1::[])
              ->
              let uu____5980 =
                let uu____5981 = str "~"  in
                let uu____5982 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5981 uu____5982  in
              FStar_Pprint.group uu____5980
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____5984;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____5990 = levels op  in
                   (match uu____5990 with
                    | (left1,mine,right1) ->
                        let uu____6000 =
                          let uu____6001 = str op  in
                          let uu____6002 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6003 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6001 uu____6002 uu____6003  in
                        paren_if_gt curr mine uu____6000)
               | uu____6004 -> p_X e)
          | uu____6005 -> p_X e

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
        let uu____6012 =
          let uu____6013 = p_lident lid  in
          let uu____6014 =
            let uu____6015 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6015  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6013 uu____6014  in
        FStar_Pprint.group uu____6012
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6018 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6020 = p_appTerm e  in
    let uu____6021 =
      let uu____6022 =
        let uu____6023 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6023 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6022  in
    FStar_Pprint.op_Hat_Hat uu____6020 uu____6021

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6028 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6028 t phi
      | FStar_Parser_AST.TAnnotated uu____6029 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6034 ->
          let uu____6035 =
            let uu____6036 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6036
             in
          failwith uu____6035
      | FStar_Parser_AST.TVariable uu____6037 ->
          let uu____6038 =
            let uu____6039 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6039
             in
          failwith uu____6038
      | FStar_Parser_AST.NoName uu____6040 ->
          let uu____6041 =
            let uu____6042 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6042
             in
          failwith uu____6041

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6044  ->
      match uu____6044 with
      | (lid,e) ->
          let uu____6051 =
            let uu____6052 = p_qlident lid  in
            let uu____6053 =
              let uu____6054 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6054
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6052 uu____6053  in
          FStar_Pprint.group uu____6051

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6056 when is_general_application e ->
        let uu____6063 = head_and_args e  in
        (match uu____6063 with
         | (head1,args) ->
             let uu____6088 =
               let uu____6099 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6099
               then
                 let uu____6129 =
                   FStar_Util.take
                     (fun uu____6153  ->
                        match uu____6153 with
                        | (uu____6158,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6129 with
                 | (fs_typ_args,args1) ->
                     let uu____6196 =
                       let uu____6197 = p_indexingTerm head1  in
                       let uu____6198 =
                         let uu____6199 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6199 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6197 uu____6198  in
                     (uu____6196, args1)
               else
                 (let uu____6211 = p_indexingTerm head1  in
                  (uu____6211, args))
                in
             (match uu____6088 with
              | (head_doc,args1) ->
                  let uu____6232 =
                    let uu____6233 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6233 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6232))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6253 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6253)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6271 =
               let uu____6272 = p_quident lid  in
               let uu____6273 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6272 uu____6273  in
             FStar_Pprint.group uu____6271
         | hd1::tl1 ->
             let uu____6290 =
               let uu____6291 =
                 let uu____6292 =
                   let uu____6293 = p_quident lid  in
                   let uu____6294 = p_argTerm hd1  in
                   prefix2 uu____6293 uu____6294  in
                 FStar_Pprint.group uu____6292  in
               let uu____6295 =
                 let uu____6296 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6296  in
               FStar_Pprint.op_Hat_Hat uu____6291 uu____6295  in
             FStar_Pprint.group uu____6290)
    | uu____6301 -> p_indexingTerm e

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
         (let uu____6310 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6310 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6312 = str "#"  in
        let uu____6313 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6312 uu____6313
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6316 = str "#["  in
        let uu____6317 =
          let uu____6318 = p_indexingTerm t  in
          let uu____6319 =
            let uu____6320 = str "]"  in
            let uu____6321 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6320 uu____6321  in
          FStar_Pprint.op_Hat_Hat uu____6318 uu____6319  in
        FStar_Pprint.op_Hat_Hat uu____6316 uu____6317
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6323  ->
    match uu____6323 with | (e,uu____6329) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6334;_},e1::e2::[])
          ->
          let uu____6339 =
            let uu____6340 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6341 =
              let uu____6342 =
                let uu____6343 = p_term false false e2  in
                soft_parens_with_nesting uu____6343  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6342  in
            FStar_Pprint.op_Hat_Hat uu____6340 uu____6341  in
          FStar_Pprint.group uu____6339
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6344;_},e1::e2::[])
          ->
          let uu____6349 =
            let uu____6350 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6351 =
              let uu____6352 =
                let uu____6353 = p_term false false e2  in
                soft_brackets_with_nesting uu____6353  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6352  in
            FStar_Pprint.op_Hat_Hat uu____6350 uu____6351  in
          FStar_Pprint.group uu____6349
      | uu____6354 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6359 = p_quident lid  in
        let uu____6360 =
          let uu____6361 =
            let uu____6362 = p_term false false e1  in
            soft_parens_with_nesting uu____6362  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6361  in
        FStar_Pprint.op_Hat_Hat uu____6359 uu____6360
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6368 =
          let uu____6369 = FStar_Ident.text_of_id op  in str uu____6369  in
        let uu____6370 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6368 uu____6370
    | uu____6371 -> p_atomicTermNotQUident e

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
         | uu____6380 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6387 =
          let uu____6388 = FStar_Ident.text_of_id op  in str uu____6388  in
        let uu____6389 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6387 uu____6389
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6393 =
          let uu____6394 =
            let uu____6395 =
              let uu____6396 = FStar_Ident.text_of_id op  in str uu____6396
               in
            let uu____6397 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6395 uu____6397  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6394  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6393
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6412 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6413 =
          let uu____6414 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6415 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6414 p_tmEq uu____6415  in
        let uu____6422 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6412 uu____6413 uu____6422
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6425 =
          let uu____6426 = p_atomicTermNotQUident e1  in
          let uu____6427 =
            let uu____6428 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6428  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6426 uu____6427
           in
        FStar_Pprint.group uu____6425
    | uu____6429 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6434 = p_quident constr_lid  in
        let uu____6435 =
          let uu____6436 =
            let uu____6437 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6437  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6436  in
        FStar_Pprint.op_Hat_Hat uu____6434 uu____6435
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6439 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6439 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6441 = p_term false false e1  in
        soft_parens_with_nesting uu____6441
    | uu____6442 when is_array e ->
        let es = extract_from_list e  in
        let uu____6446 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6447 =
          let uu____6448 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6448
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6451 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6446 uu____6447 uu____6451
    | uu____6452 when is_list e ->
        let uu____6453 =
          let uu____6454 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6455 = extract_from_list e  in
          separate_map_or_flow_last uu____6454
            (fun ps  -> p_noSeqTerm ps false) uu____6455
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6453 FStar_Pprint.rbracket
    | uu____6460 when is_lex_list e ->
        let uu____6461 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6462 =
          let uu____6463 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6464 = extract_from_list e  in
          separate_map_or_flow_last uu____6463
            (fun ps  -> p_noSeqTerm ps false) uu____6464
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6461 uu____6462 FStar_Pprint.rbracket
    | uu____6469 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6473 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6474 =
          let uu____6475 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6475 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6473 uu____6474 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6479 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6480 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6479 uu____6480
    | FStar_Parser_AST.Op (op,args) when
        let uu____6487 = handleable_op op args  in
        Prims.op_Negation uu____6487 ->
        let uu____6488 =
          let uu____6489 =
            let uu____6490 = FStar_Ident.text_of_id op  in
            let uu____6491 =
              let uu____6492 =
                let uu____6493 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6493
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6492  in
            Prims.strcat uu____6490 uu____6491  in
          Prims.strcat "Operation " uu____6489  in
        failwith uu____6488
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6495 = str "u#"  in
        let uu____6496 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6495 uu____6496
    | FStar_Parser_AST.Wild  ->
        let uu____6497 = p_term false false e  in
        soft_parens_with_nesting uu____6497
    | FStar_Parser_AST.Const uu____6498 ->
        let uu____6499 = p_term false false e  in
        soft_parens_with_nesting uu____6499
    | FStar_Parser_AST.Op uu____6500 ->
        let uu____6507 = p_term false false e  in
        soft_parens_with_nesting uu____6507
    | FStar_Parser_AST.Tvar uu____6508 ->
        let uu____6509 = p_term false false e  in
        soft_parens_with_nesting uu____6509
    | FStar_Parser_AST.Var uu____6510 ->
        let uu____6511 = p_term false false e  in
        soft_parens_with_nesting uu____6511
    | FStar_Parser_AST.Name uu____6512 ->
        let uu____6513 = p_term false false e  in
        soft_parens_with_nesting uu____6513
    | FStar_Parser_AST.Construct uu____6514 ->
        let uu____6525 = p_term false false e  in
        soft_parens_with_nesting uu____6525
    | FStar_Parser_AST.Abs uu____6526 ->
        let uu____6533 = p_term false false e  in
        soft_parens_with_nesting uu____6533
    | FStar_Parser_AST.App uu____6534 ->
        let uu____6541 = p_term false false e  in
        soft_parens_with_nesting uu____6541
    | FStar_Parser_AST.Let uu____6542 ->
        let uu____6563 = p_term false false e  in
        soft_parens_with_nesting uu____6563
    | FStar_Parser_AST.LetOpen uu____6564 ->
        let uu____6569 = p_term false false e  in
        soft_parens_with_nesting uu____6569
    | FStar_Parser_AST.Seq uu____6570 ->
        let uu____6575 = p_term false false e  in
        soft_parens_with_nesting uu____6575
    | FStar_Parser_AST.Bind uu____6576 ->
        let uu____6583 = p_term false false e  in
        soft_parens_with_nesting uu____6583
    | FStar_Parser_AST.If uu____6584 ->
        let uu____6591 = p_term false false e  in
        soft_parens_with_nesting uu____6591
    | FStar_Parser_AST.Match uu____6592 ->
        let uu____6607 = p_term false false e  in
        soft_parens_with_nesting uu____6607
    | FStar_Parser_AST.TryWith uu____6608 ->
        let uu____6623 = p_term false false e  in
        soft_parens_with_nesting uu____6623
    | FStar_Parser_AST.Ascribed uu____6624 ->
        let uu____6633 = p_term false false e  in
        soft_parens_with_nesting uu____6633
    | FStar_Parser_AST.Record uu____6634 ->
        let uu____6647 = p_term false false e  in
        soft_parens_with_nesting uu____6647
    | FStar_Parser_AST.Project uu____6648 ->
        let uu____6653 = p_term false false e  in
        soft_parens_with_nesting uu____6653
    | FStar_Parser_AST.Product uu____6654 ->
        let uu____6661 = p_term false false e  in
        soft_parens_with_nesting uu____6661
    | FStar_Parser_AST.Sum uu____6662 ->
        let uu____6669 = p_term false false e  in
        soft_parens_with_nesting uu____6669
    | FStar_Parser_AST.QForall uu____6670 ->
        let uu____6683 = p_term false false e  in
        soft_parens_with_nesting uu____6683
    | FStar_Parser_AST.QExists uu____6684 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.Refine uu____6698 ->
        let uu____6703 = p_term false false e  in
        soft_parens_with_nesting uu____6703
    | FStar_Parser_AST.NamedTyp uu____6704 ->
        let uu____6709 = p_term false false e  in
        soft_parens_with_nesting uu____6709
    | FStar_Parser_AST.Requires uu____6710 ->
        let uu____6717 = p_term false false e  in
        soft_parens_with_nesting uu____6717
    | FStar_Parser_AST.Ensures uu____6718 ->
        let uu____6725 = p_term false false e  in
        soft_parens_with_nesting uu____6725
    | FStar_Parser_AST.Attributes uu____6726 ->
        let uu____6729 = p_term false false e  in
        soft_parens_with_nesting uu____6729
    | FStar_Parser_AST.Quote uu____6730 ->
        let uu____6735 = p_term false false e  in
        soft_parens_with_nesting uu____6735
    | FStar_Parser_AST.VQuote uu____6736 ->
        let uu____6737 = p_term false false e  in
        soft_parens_with_nesting uu____6737
    | FStar_Parser_AST.Antiquote uu____6738 ->
        let uu____6743 = p_term false false e  in
        soft_parens_with_nesting uu____6743

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___118_6744  ->
    match uu___118_6744 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6750) ->
        let uu____6751 = str s  in FStar_Pprint.dquotes uu____6751
    | FStar_Const.Const_bytearray (bytes,uu____6753) ->
        let uu____6760 =
          let uu____6761 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6761  in
        let uu____6762 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6760 uu____6762
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___116_6782 =
          match uu___116_6782 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___117_6788 =
          match uu___117_6788 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6799  ->
               match uu____6799 with
               | (s,w) ->
                   let uu____6806 = signedness s  in
                   let uu____6807 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6806 uu____6807)
            sign_width_opt
           in
        let uu____6808 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6808 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6810 = FStar_Range.string_of_range r  in str uu____6810
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6812 = p_quident lid  in
        let uu____6813 =
          let uu____6814 =
            let uu____6815 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6815  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6814  in
        FStar_Pprint.op_Hat_Hat uu____6812 uu____6813

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6817 = str "u#"  in
    let uu____6818 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6817 uu____6818

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6820;_},u1::u2::[])
        ->
        let uu____6825 =
          let uu____6826 = p_universeFrom u1  in
          let uu____6827 =
            let uu____6828 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6828  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6826 uu____6827  in
        FStar_Pprint.group uu____6825
    | FStar_Parser_AST.App uu____6829 ->
        let uu____6836 = head_and_args u  in
        (match uu____6836 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6862 =
                    let uu____6863 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6864 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6872  ->
                           match uu____6872 with
                           | (u1,uu____6878) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6863 uu____6864  in
                  FStar_Pprint.group uu____6862
              | uu____6879 ->
                  let uu____6880 =
                    let uu____6881 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6881
                     in
                  failwith uu____6880))
    | uu____6882 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6905 = FStar_Ident.text_of_id id1  in str uu____6905
    | FStar_Parser_AST.Paren u1 ->
        let uu____6907 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6907
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6908;_},uu____6909::uu____6910::[])
        ->
        let uu____6913 = p_universeFrom u  in
        soft_parens_with_nesting uu____6913
    | FStar_Parser_AST.App uu____6914 ->
        let uu____6921 = p_universeFrom u  in
        soft_parens_with_nesting uu____6921
    | uu____6922 ->
        let uu____6923 =
          let uu____6924 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6924
           in
        failwith uu____6923

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
       | FStar_Parser_AST.Module (uu____6996,decls) ->
           let uu____7002 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7002
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7011,decls,uu____7013) ->
           let uu____7018 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7018
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7071  ->
         match uu____7071 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7115,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7121,decls,uu____7123) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7168 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7181;
                 FStar_Parser_AST.doc = uu____7182;
                 FStar_Parser_AST.quals = uu____7183;
                 FStar_Parser_AST.attrs = uu____7184;_}::uu____7185 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7191 =
                   let uu____7194 =
                     let uu____7197 = FStar_List.tl ds  in d :: uu____7197
                      in
                   d0 :: uu____7194  in
                 (uu____7191, (d0.FStar_Parser_AST.drange))
             | uu____7202 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7168 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7262 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7262 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7358 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7358, comments1))))))
  