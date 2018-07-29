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
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4563;
               FStar_Parser_AST.blevel = uu____4564;
               FStar_Parser_AST.aqual = uu____4565;_},phi))
             ->
             let uu____4571 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4571
         | uu____4572 ->
             let uu____4577 =
               let uu____4578 = p_tuplePattern pat  in
               let uu____4579 =
                 let uu____4580 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4580
                  in
               FStar_Pprint.op_Hat_Hat uu____4578 uu____4579  in
             soft_parens_with_nesting uu____4577)
    | FStar_Parser_AST.PatList pats ->
        let uu____4584 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4584 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4601 =
          match uu____4601 with
          | (lid,pat) ->
              let uu____4608 = p_qlident lid  in
              let uu____4609 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4608 uu____4609
           in
        let uu____4610 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4610
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4620 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4621 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4622 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4620 uu____4621 uu____4622
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4631 =
          let uu____4632 =
            let uu____4633 =
              let uu____4634 = FStar_Ident.text_of_id op  in str uu____4634
               in
            let uu____4635 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4633 uu____4635  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4632  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4631
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4639 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4639 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4647 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4648 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4647 uu____4648
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4650 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4653;
           FStar_Parser_AST.prange = uu____4654;_},uu____4655)
        ->
        let uu____4660 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4660
    | FStar_Parser_AST.PatTuple (uu____4661,false ) ->
        let uu____4666 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4666
    | uu____4667 ->
        let uu____4668 =
          let uu____4669 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4669  in
        failwith uu____4668

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4671;_},uu____4672)
        -> true
    | uu____4677 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4681 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4682 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4681 uu____4682
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4689;
                   FStar_Parser_AST.blevel = uu____4690;
                   FStar_Parser_AST.aqual = uu____4691;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4695 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4695 t1 phi
            | uu____4696 ->
                let t' =
                  let uu____4698 = is_typ_tuple t  in
                  if uu____4698
                  then
                    let uu____4699 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4699
                  else p_tmFormula t  in
                let uu____4701 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4702 =
                  let uu____4703 = p_lident lid  in
                  let uu____4704 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4703 uu____4704  in
                FStar_Pprint.op_Hat_Hat uu____4701 uu____4702
             in
          if is_atomic
          then
            let uu____4705 =
              let uu____4706 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4706  in
            FStar_Pprint.group uu____4705
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4708 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4715;
                  FStar_Parser_AST.blevel = uu____4716;
                  FStar_Parser_AST.aqual = uu____4717;_},phi)
               ->
               if is_atomic
               then
                 let uu____4721 =
                   let uu____4722 =
                     let uu____4723 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4723 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4722  in
                 FStar_Pprint.group uu____4721
               else
                 (let uu____4725 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4725)
           | uu____4726 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4735 -> false
            | FStar_Parser_AST.App uu____4746 -> false
            | FStar_Parser_AST.Op uu____4753 -> false
            | uu____4760 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4764 =
            let uu____4765 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4766 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4765 uu____4766  in
          let uu____4767 =
            let uu____4768 = p_appTerm t  in
            let uu____4769 =
              let uu____4770 =
                let uu____4771 =
                  let uu____4772 = soft_braces_with_nesting_tight phi1  in
                  let uu____4773 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4772 uu____4773  in
                FStar_Pprint.group uu____4771  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4770
               in
            FStar_Pprint.op_Hat_Hat uu____4768 uu____4769  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4764 uu____4767

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4784 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4784

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4789 = FStar_Ident.text_of_id lid  in str uu____4789)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4792 = FStar_Ident.text_of_lid lid  in str uu____4792)

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
            let uu____4810 =
              let uu____4811 =
                let uu____4812 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4812 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4811  in
            let uu____4813 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4810 uu____4813
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4817 =
              let uu____4818 =
                let uu____4819 =
                  let uu____4820 = p_lident x  in
                  let uu____4821 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4820 uu____4821  in
                let uu____4822 =
                  let uu____4823 = p_noSeqTerm true false e1  in
                  let uu____4824 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4823 uu____4824  in
                op_Hat_Slash_Plus_Hat uu____4819 uu____4822  in
              FStar_Pprint.group uu____4818  in
            let uu____4825 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4817 uu____4825
        | uu____4826 ->
            let uu____4827 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4827

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
            let uu____4838 =
              let uu____4839 = p_tmIff e1  in
              let uu____4840 =
                let uu____4841 =
                  let uu____4842 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4842
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4841  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4839 uu____4840  in
            FStar_Pprint.group uu____4838
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4848 =
              let uu____4849 = p_tmIff e1  in
              let uu____4850 =
                let uu____4851 =
                  let uu____4852 =
                    let uu____4853 = p_typ false false t  in
                    let uu____4854 =
                      let uu____4855 = str "by"  in
                      let uu____4856 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4855 uu____4856  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4853 uu____4854  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4852
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4851  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4849 uu____4850  in
            FStar_Pprint.group uu____4848
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4857;_},e1::e2::e3::[])
            ->
            let uu____4863 =
              let uu____4864 =
                let uu____4865 =
                  let uu____4866 = p_atomicTermNotQUident e1  in
                  let uu____4867 =
                    let uu____4868 =
                      let uu____4869 =
                        let uu____4870 = p_term false false e2  in
                        soft_parens_with_nesting uu____4870  in
                      let uu____4871 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4869 uu____4871  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4868  in
                  FStar_Pprint.op_Hat_Hat uu____4866 uu____4867  in
                FStar_Pprint.group uu____4865  in
              let uu____4872 =
                let uu____4873 = p_noSeqTerm ps pb e3  in jump2 uu____4873
                 in
              FStar_Pprint.op_Hat_Hat uu____4864 uu____4872  in
            FStar_Pprint.group uu____4863
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4874;_},e1::e2::e3::[])
            ->
            let uu____4880 =
              let uu____4881 =
                let uu____4882 =
                  let uu____4883 = p_atomicTermNotQUident e1  in
                  let uu____4884 =
                    let uu____4885 =
                      let uu____4886 =
                        let uu____4887 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4887  in
                      let uu____4888 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4886 uu____4888  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4885  in
                  FStar_Pprint.op_Hat_Hat uu____4883 uu____4884  in
                FStar_Pprint.group uu____4882  in
              let uu____4889 =
                let uu____4890 = p_noSeqTerm ps pb e3  in jump2 uu____4890
                 in
              FStar_Pprint.op_Hat_Hat uu____4881 uu____4889  in
            FStar_Pprint.group uu____4880
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4898 =
              let uu____4899 = str "requires"  in
              let uu____4900 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4899 uu____4900  in
            FStar_Pprint.group uu____4898
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4908 =
              let uu____4909 = str "ensures"  in
              let uu____4910 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4909 uu____4910  in
            FStar_Pprint.group uu____4908
        | FStar_Parser_AST.Attributes es ->
            let uu____4914 =
              let uu____4915 = str "attributes"  in
              let uu____4916 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4915 uu____4916  in
            FStar_Pprint.group uu____4914
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4920 =
                let uu____4921 =
                  let uu____4922 = str "if"  in
                  let uu____4923 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4922 uu____4923  in
                let uu____4924 =
                  let uu____4925 = str "then"  in
                  let uu____4926 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4925 uu____4926  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4921 uu____4924  in
              FStar_Pprint.group uu____4920
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4929,uu____4930,e31) when
                     is_unit e31 ->
                     let uu____4932 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4932
                 | uu____4933 -> p_noSeqTerm false false e2  in
               let uu____4934 =
                 let uu____4935 =
                   let uu____4936 = str "if"  in
                   let uu____4937 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4936 uu____4937  in
                 let uu____4938 =
                   let uu____4939 =
                     let uu____4940 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4940 e2_doc  in
                   let uu____4941 =
                     let uu____4942 = str "else"  in
                     let uu____4943 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4942 uu____4943  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4939 uu____4941  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4935 uu____4938  in
               FStar_Pprint.group uu____4934)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4966 =
              let uu____4967 =
                let uu____4968 =
                  let uu____4969 = str "try"  in
                  let uu____4970 = p_noSeqTerm false false e1  in
                  prefix2 uu____4969 uu____4970  in
                let uu____4971 =
                  let uu____4972 = str "with"  in
                  let uu____4973 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4972 uu____4973  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4968 uu____4971  in
              FStar_Pprint.group uu____4967  in
            let uu____4982 = paren_if (ps || pb)  in uu____4982 uu____4966
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5009 =
              let uu____5010 =
                let uu____5011 =
                  let uu____5012 = str "match"  in
                  let uu____5013 = p_noSeqTerm false false e1  in
                  let uu____5014 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5012 uu____5013 uu____5014
                   in
                let uu____5015 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5011 uu____5015  in
              FStar_Pprint.group uu____5010  in
            let uu____5024 = paren_if (ps || pb)  in uu____5024 uu____5009
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5031 =
              let uu____5032 =
                let uu____5033 =
                  let uu____5034 = str "let open"  in
                  let uu____5035 = p_quident uid  in
                  let uu____5036 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5034 uu____5035 uu____5036
                   in
                let uu____5037 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5033 uu____5037  in
              FStar_Pprint.group uu____5032  in
            let uu____5038 = paren_if ps  in uu____5038 uu____5031
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5102 is_last =
              match uu____5102 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5135 =
                          let uu____5136 = str "let"  in
                          let uu____5137 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5136 uu____5137
                           in
                        FStar_Pprint.group uu____5135
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5138 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5143 =
                    if is_last
                    then
                      let uu____5144 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5145 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5144 doc_expr uu____5145
                    else
                      (let uu____5147 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5147)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5143
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5193 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5193
                     else
                       (let uu____5201 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5201)) lbs
               in
            let lbs_doc =
              let uu____5209 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5209  in
            let uu____5210 =
              let uu____5211 =
                let uu____5212 =
                  let uu____5213 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5213
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5212  in
              FStar_Pprint.group uu____5211  in
            let uu____5214 = paren_if ps  in uu____5214 uu____5210
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5221;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5224;
                                                             FStar_Parser_AST.level
                                                               = uu____5225;_})
            when matches_var maybe_x x ->
            let uu____5252 =
              let uu____5253 =
                let uu____5254 = str "function"  in
                let uu____5255 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5254 uu____5255  in
              FStar_Pprint.group uu____5253  in
            let uu____5264 = paren_if (ps || pb)  in uu____5264 uu____5252
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5270 =
              let uu____5271 = str "quote"  in
              let uu____5272 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5271 uu____5272  in
            FStar_Pprint.group uu____5270
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5274 =
              let uu____5275 = str "`"  in
              let uu____5276 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5275 uu____5276  in
            FStar_Pprint.group uu____5274
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5278 =
              let uu____5279 = str "`%"  in
              let uu____5280 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5279 uu____5280  in
            FStar_Pprint.group uu____5278
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5282;
              FStar_Parser_AST.level = uu____5283;_}
            ->
            let uu____5284 =
              let uu____5285 = str "`@"  in
              let uu____5286 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5285 uu____5286  in
            FStar_Pprint.group uu____5284
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5288 =
              let uu____5289 = str "`#"  in
              let uu____5290 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5289 uu____5290  in
            FStar_Pprint.group uu____5288
        | uu____5291 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___114_5292  ->
    match uu___114_5292 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5304 =
          let uu____5305 = str "[@"  in
          let uu____5306 =
            let uu____5307 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5308 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5307 uu____5308  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5305 uu____5306  in
        FStar_Pprint.group uu____5304

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
                 let uu____5334 =
                   let uu____5335 =
                     let uu____5336 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5336 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5335 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5334 term_doc
             | pats ->
                 let uu____5342 =
                   let uu____5343 =
                     let uu____5344 =
                       let uu____5345 =
                         let uu____5346 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5346
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5345 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5347 = p_trigger trigger  in
                     prefix2 uu____5344 uu____5347  in
                   FStar_Pprint.group uu____5343  in
                 prefix2 uu____5342 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5367 =
                   let uu____5368 =
                     let uu____5369 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5369 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5368 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5367 term_doc
             | pats ->
                 let uu____5375 =
                   let uu____5376 =
                     let uu____5377 =
                       let uu____5378 =
                         let uu____5379 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5379
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5378 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5380 = p_trigger trigger  in
                     prefix2 uu____5377 uu____5380  in
                   FStar_Pprint.group uu____5376  in
                 prefix2 uu____5375 term_doc)
        | uu____5381 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5383 -> str "forall"
    | FStar_Parser_AST.QExists uu____5396 -> str "exists"
    | uu____5409 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___115_5410  ->
    match uu___115_5410 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5422 =
          let uu____5423 =
            let uu____5424 =
              let uu____5425 = str "pattern"  in
              let uu____5426 =
                let uu____5427 =
                  let uu____5428 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5428
                   in
                FStar_Pprint.op_Hat_Hat uu____5427 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5425 uu____5426  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5424  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5423  in
        FStar_Pprint.group uu____5422

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5434 = str "\\/"  in
    FStar_Pprint.separate_map uu____5434 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5440 =
      let uu____5441 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5441 p_appTerm pats  in
    FStar_Pprint.group uu____5440

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5451 =
              let uu____5452 =
                let uu____5453 = str "fun"  in
                let uu____5454 =
                  let uu____5455 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5455
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5453 uu____5454  in
              let uu____5456 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5452 uu____5456  in
            let uu____5457 = paren_if ps  in uu____5457 uu____5451
        | uu____5462 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5466  ->
      match uu____5466 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5489 =
                    let uu____5490 =
                      let uu____5491 =
                        let uu____5492 = p_tuplePattern p  in
                        let uu____5493 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5492 uu____5493  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5491
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5490  in
                  FStar_Pprint.group uu____5489
              | FStar_Pervasives_Native.Some f ->
                  let uu____5495 =
                    let uu____5496 =
                      let uu____5497 =
                        let uu____5498 =
                          let uu____5499 =
                            let uu____5500 = p_tuplePattern p  in
                            let uu____5501 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5500
                              uu____5501
                             in
                          FStar_Pprint.group uu____5499  in
                        let uu____5502 =
                          let uu____5503 =
                            let uu____5506 = p_tmFormula f  in
                            [uu____5506; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5503  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5498 uu____5502
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5497
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5496  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5495
               in
            let uu____5507 =
              let uu____5508 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5508  in
            FStar_Pprint.group uu____5507  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5517 =
                      let uu____5518 =
                        let uu____5519 =
                          let uu____5520 =
                            let uu____5521 =
                              let uu____5522 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5522  in
                            FStar_Pprint.separate_map uu____5521
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5520
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5519
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5518  in
                    FStar_Pprint.group uu____5517
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5523 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5525;_},e1::e2::[])
        ->
        let uu____5530 = str "<==>"  in
        let uu____5531 = p_tmImplies e1  in
        let uu____5532 = p_tmIff e2  in
        infix0 uu____5530 uu____5531 uu____5532
    | uu____5533 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5535;_},e1::e2::[])
        ->
        let uu____5540 = str "==>"  in
        let uu____5541 = p_tmArrow p_tmFormula e1  in
        let uu____5542 = p_tmImplies e2  in
        infix0 uu____5540 uu____5541 uu____5542
    | uu____5543 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5551 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5551 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5572 ->
               let uu____5573 =
                 let uu____5574 =
                   let uu____5575 =
                     let uu____5576 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5576
                      in
                   FStar_Pprint.separate uu____5575 terms  in
                 let uu____5577 =
                   let uu____5578 =
                     let uu____5579 =
                       let uu____5580 =
                         let uu____5581 =
                           let uu____5582 =
                             let uu____5583 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5583
                              in
                           FStar_Pprint.separate uu____5582 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5581 last_op  in
                       let uu____5584 =
                         let uu____5585 =
                           let uu____5586 =
                             let uu____5587 =
                               let uu____5588 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5588
                                in
                             FStar_Pprint.separate uu____5587 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5586 last_op  in
                         jump2 uu____5585  in
                       FStar_Pprint.ifflat uu____5580 uu____5584  in
                     FStar_Pprint.group uu____5579  in
                   let uu____5589 = FStar_List.hd last1  in
                   prefix2 uu____5578 uu____5589  in
                 FStar_Pprint.ifflat uu____5574 uu____5577  in
               FStar_Pprint.group uu____5573)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5602 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5607 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5602 uu____5607
      | uu____5610 -> let uu____5611 = p_Tm e  in [uu____5611]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5614 =
        let uu____5615 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5615 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5614  in
    let disj =
      let uu____5617 =
        let uu____5618 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5618 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5617  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5637;_},e1::e2::[])
        ->
        let uu____5642 = p_tmDisjunction e1  in
        let uu____5647 = let uu____5652 = p_tmConjunction e2  in [uu____5652]
           in
        FStar_List.append uu____5642 uu____5647
    | uu____5661 -> let uu____5662 = p_tmConjunction e  in [uu____5662]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5672;_},e1::e2::[])
        ->
        let uu____5677 = p_tmConjunction e1  in
        let uu____5680 = let uu____5683 = p_tmTuple e2  in [uu____5683]  in
        FStar_List.append uu____5677 uu____5680
    | uu____5684 -> let uu____5685 = p_tmTuple e  in [uu____5685]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5702 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5702
          (fun uu____5710  ->
             match uu____5710 with | (e1,uu____5716) -> p_tmEq e1) args
    | uu____5717 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5722 =
             let uu____5723 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5723  in
           FStar_Pprint.group uu____5722)

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
               (let uu____5740 = FStar_Ident.text_of_id op  in
                uu____5740 = "="))
              ||
              (let uu____5742 = FStar_Ident.text_of_id op  in
               uu____5742 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5744 = levels op1  in
            (match uu____5744 with
             | (left1,mine,right1) ->
                 let uu____5754 =
                   let uu____5755 = FStar_All.pipe_left str op1  in
                   let uu____5756 = p_tmEqWith' p_X left1 e1  in
                   let uu____5757 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5755 uu____5756 uu____5757  in
                 paren_if_gt curr mine uu____5754)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5758;_},e1::e2::[])
            ->
            let uu____5763 =
              let uu____5764 = p_tmEqWith p_X e1  in
              let uu____5765 =
                let uu____5766 =
                  let uu____5767 =
                    let uu____5768 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5768  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5767  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5766  in
              FStar_Pprint.op_Hat_Hat uu____5764 uu____5765  in
            FStar_Pprint.group uu____5763
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5769;_},e1::[])
            ->
            let uu____5773 = levels "-"  in
            (match uu____5773 with
             | (left1,mine,right1) ->
                 let uu____5783 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5783)
        | uu____5784 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5828)::(e2,uu____5830)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5850 = is_list e  in Prims.op_Negation uu____5850)
              ->
              let op = "::"  in
              let uu____5852 = levels op  in
              (match uu____5852 with
               | (left1,mine,right1) ->
                   let uu____5862 =
                     let uu____5863 = str op  in
                     let uu____5864 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5865 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5863 uu____5864 uu____5865  in
                   paren_if_gt curr mine uu____5862)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5873 = levels op  in
              (match uu____5873 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5889 = p_binder false b  in
                     let uu____5890 =
                       let uu____5891 =
                         let uu____5892 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5892 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5891
                        in
                     FStar_Pprint.op_Hat_Hat uu____5889 uu____5890  in
                   let uu____5893 =
                     let uu____5894 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5895 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5894 uu____5895  in
                   paren_if_gt curr mine uu____5893)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5896;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5921 = levels op  in
              (match uu____5921 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5931 = str op  in
                     let uu____5932 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5933 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5931 uu____5932 uu____5933
                   else
                     (let uu____5935 =
                        let uu____5936 = str op  in
                        let uu____5937 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5938 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5936 uu____5937 uu____5938  in
                      paren_if_gt curr mine uu____5935))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5945 = levels op1  in
              (match uu____5945 with
               | (left1,mine,right1) ->
                   let uu____5955 =
                     let uu____5956 = str op1  in
                     let uu____5957 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5958 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5956 uu____5957 uu____5958  in
                   paren_if_gt curr mine uu____5955)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5977 =
                let uu____5978 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5979 =
                  let uu____5980 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5980 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5978 uu____5979  in
              braces_with_nesting uu____5977
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5985;_},e1::[])
              ->
              let uu____5989 =
                let uu____5990 = str "~"  in
                let uu____5991 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5990 uu____5991  in
              FStar_Pprint.group uu____5989
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____5993;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____5999 = levels op  in
                   (match uu____5999 with
                    | (left1,mine,right1) ->
                        let uu____6009 =
                          let uu____6010 = str op  in
                          let uu____6011 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6012 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6010 uu____6011 uu____6012  in
                        paren_if_gt curr mine uu____6009)
               | uu____6013 -> p_X e)
          | uu____6014 -> p_X e

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
        let uu____6021 =
          let uu____6022 = p_lident lid  in
          let uu____6023 =
            let uu____6024 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6024  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6022 uu____6023  in
        FStar_Pprint.group uu____6021
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6027 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6029 = p_appTerm e  in
    let uu____6030 =
      let uu____6031 =
        let uu____6032 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6032 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6031  in
    FStar_Pprint.op_Hat_Hat uu____6029 uu____6030

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6037 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6037 t phi
      | FStar_Parser_AST.TAnnotated uu____6038 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6043 ->
          let uu____6044 =
            let uu____6045 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6045
             in
          failwith uu____6044
      | FStar_Parser_AST.TVariable uu____6046 ->
          let uu____6047 =
            let uu____6048 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6048
             in
          failwith uu____6047
      | FStar_Parser_AST.NoName uu____6049 ->
          let uu____6050 =
            let uu____6051 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6051
             in
          failwith uu____6050

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6053  ->
      match uu____6053 with
      | (lid,e) ->
          let uu____6060 =
            let uu____6061 = p_qlident lid  in
            let uu____6062 =
              let uu____6063 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6063
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6061 uu____6062  in
          FStar_Pprint.group uu____6060

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6065 when is_general_application e ->
        let uu____6072 = head_and_args e  in
        (match uu____6072 with
         | (head1,args) ->
             let uu____6097 =
               let uu____6108 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6108
               then
                 let uu____6138 =
                   FStar_Util.take
                     (fun uu____6162  ->
                        match uu____6162 with
                        | (uu____6167,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6138 with
                 | (fs_typ_args,args1) ->
                     let uu____6205 =
                       let uu____6206 = p_indexingTerm head1  in
                       let uu____6207 =
                         let uu____6208 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6208 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6206 uu____6207  in
                     (uu____6205, args1)
               else
                 (let uu____6220 = p_indexingTerm head1  in
                  (uu____6220, args))
                in
             (match uu____6097 with
              | (head_doc,args1) ->
                  let uu____6241 =
                    let uu____6242 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6242 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6241))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6262 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6262)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6280 =
               let uu____6281 = p_quident lid  in
               let uu____6282 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6281 uu____6282  in
             FStar_Pprint.group uu____6280
         | hd1::tl1 ->
             let uu____6299 =
               let uu____6300 =
                 let uu____6301 =
                   let uu____6302 = p_quident lid  in
                   let uu____6303 = p_argTerm hd1  in
                   prefix2 uu____6302 uu____6303  in
                 FStar_Pprint.group uu____6301  in
               let uu____6304 =
                 let uu____6305 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6305  in
               FStar_Pprint.op_Hat_Hat uu____6300 uu____6304  in
             FStar_Pprint.group uu____6299)
    | uu____6310 -> p_indexingTerm e

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
         (let uu____6319 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6319 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6321 = str "#"  in
        let uu____6322 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6321 uu____6322
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6325 = str "#["  in
        let uu____6326 =
          let uu____6327 = p_indexingTerm t  in
          let uu____6328 =
            let uu____6329 = str "]"  in
            let uu____6330 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6329 uu____6330  in
          FStar_Pprint.op_Hat_Hat uu____6327 uu____6328  in
        FStar_Pprint.op_Hat_Hat uu____6325 uu____6326
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6332  ->
    match uu____6332 with | (e,uu____6338) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6343;_},e1::e2::[])
          ->
          let uu____6348 =
            let uu____6349 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6350 =
              let uu____6351 =
                let uu____6352 = p_term false false e2  in
                soft_parens_with_nesting uu____6352  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6351  in
            FStar_Pprint.op_Hat_Hat uu____6349 uu____6350  in
          FStar_Pprint.group uu____6348
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6353;_},e1::e2::[])
          ->
          let uu____6358 =
            let uu____6359 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6360 =
              let uu____6361 =
                let uu____6362 = p_term false false e2  in
                soft_brackets_with_nesting uu____6362  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6361  in
            FStar_Pprint.op_Hat_Hat uu____6359 uu____6360  in
          FStar_Pprint.group uu____6358
      | uu____6363 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6368 = p_quident lid  in
        let uu____6369 =
          let uu____6370 =
            let uu____6371 = p_term false false e1  in
            soft_parens_with_nesting uu____6371  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6370  in
        FStar_Pprint.op_Hat_Hat uu____6368 uu____6369
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6377 =
          let uu____6378 = FStar_Ident.text_of_id op  in str uu____6378  in
        let uu____6379 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6377 uu____6379
    | uu____6380 -> p_atomicTermNotQUident e

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
         | uu____6389 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6396 =
          let uu____6397 = FStar_Ident.text_of_id op  in str uu____6397  in
        let uu____6398 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6396 uu____6398
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6402 =
          let uu____6403 =
            let uu____6404 =
              let uu____6405 = FStar_Ident.text_of_id op  in str uu____6405
               in
            let uu____6406 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6404 uu____6406  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6403  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6402
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6421 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6422 =
          let uu____6423 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6424 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6423 p_tmEq uu____6424  in
        let uu____6431 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6421 uu____6422 uu____6431
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6434 =
          let uu____6435 = p_atomicTermNotQUident e1  in
          let uu____6436 =
            let uu____6437 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6437  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6435 uu____6436
           in
        FStar_Pprint.group uu____6434
    | uu____6438 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6443 = p_quident constr_lid  in
        let uu____6444 =
          let uu____6445 =
            let uu____6446 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6446  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6445  in
        FStar_Pprint.op_Hat_Hat uu____6443 uu____6444
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6448 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6448 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6450 = p_term false false e1  in
        soft_parens_with_nesting uu____6450
    | uu____6451 when is_array e ->
        let es = extract_from_list e  in
        let uu____6455 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6456 =
          let uu____6457 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6457
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6460 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6455 uu____6456 uu____6460
    | uu____6461 when is_list e ->
        let uu____6462 =
          let uu____6463 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6464 = extract_from_list e  in
          separate_map_or_flow_last uu____6463
            (fun ps  -> p_noSeqTerm ps false) uu____6464
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6462 FStar_Pprint.rbracket
    | uu____6469 when is_lex_list e ->
        let uu____6470 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6471 =
          let uu____6472 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6473 = extract_from_list e  in
          separate_map_or_flow_last uu____6472
            (fun ps  -> p_noSeqTerm ps false) uu____6473
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6470 uu____6471 FStar_Pprint.rbracket
    | uu____6478 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6482 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6483 =
          let uu____6484 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6484 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6482 uu____6483 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6488 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6489 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6488 uu____6489
    | FStar_Parser_AST.Op (op,args) when
        let uu____6496 = handleable_op op args  in
        Prims.op_Negation uu____6496 ->
        let uu____6497 =
          let uu____6498 =
            let uu____6499 = FStar_Ident.text_of_id op  in
            let uu____6500 =
              let uu____6501 =
                let uu____6502 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6502
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6501  in
            Prims.strcat uu____6499 uu____6500  in
          Prims.strcat "Operation " uu____6498  in
        failwith uu____6497
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6504 = str "u#"  in
        let uu____6505 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6504 uu____6505
    | FStar_Parser_AST.Wild  ->
        let uu____6506 = p_term false false e  in
        soft_parens_with_nesting uu____6506
    | FStar_Parser_AST.Const uu____6507 ->
        let uu____6508 = p_term false false e  in
        soft_parens_with_nesting uu____6508
    | FStar_Parser_AST.Op uu____6509 ->
        let uu____6516 = p_term false false e  in
        soft_parens_with_nesting uu____6516
    | FStar_Parser_AST.Tvar uu____6517 ->
        let uu____6518 = p_term false false e  in
        soft_parens_with_nesting uu____6518
    | FStar_Parser_AST.Var uu____6519 ->
        let uu____6520 = p_term false false e  in
        soft_parens_with_nesting uu____6520
    | FStar_Parser_AST.Name uu____6521 ->
        let uu____6522 = p_term false false e  in
        soft_parens_with_nesting uu____6522
    | FStar_Parser_AST.Construct uu____6523 ->
        let uu____6534 = p_term false false e  in
        soft_parens_with_nesting uu____6534
    | FStar_Parser_AST.Abs uu____6535 ->
        let uu____6542 = p_term false false e  in
        soft_parens_with_nesting uu____6542
    | FStar_Parser_AST.App uu____6543 ->
        let uu____6550 = p_term false false e  in
        soft_parens_with_nesting uu____6550
    | FStar_Parser_AST.Let uu____6551 ->
        let uu____6572 = p_term false false e  in
        soft_parens_with_nesting uu____6572
    | FStar_Parser_AST.LetOpen uu____6573 ->
        let uu____6578 = p_term false false e  in
        soft_parens_with_nesting uu____6578
    | FStar_Parser_AST.Seq uu____6579 ->
        let uu____6584 = p_term false false e  in
        soft_parens_with_nesting uu____6584
    | FStar_Parser_AST.Bind uu____6585 ->
        let uu____6592 = p_term false false e  in
        soft_parens_with_nesting uu____6592
    | FStar_Parser_AST.If uu____6593 ->
        let uu____6600 = p_term false false e  in
        soft_parens_with_nesting uu____6600
    | FStar_Parser_AST.Match uu____6601 ->
        let uu____6616 = p_term false false e  in
        soft_parens_with_nesting uu____6616
    | FStar_Parser_AST.TryWith uu____6617 ->
        let uu____6632 = p_term false false e  in
        soft_parens_with_nesting uu____6632
    | FStar_Parser_AST.Ascribed uu____6633 ->
        let uu____6642 = p_term false false e  in
        soft_parens_with_nesting uu____6642
    | FStar_Parser_AST.Record uu____6643 ->
        let uu____6656 = p_term false false e  in
        soft_parens_with_nesting uu____6656
    | FStar_Parser_AST.Project uu____6657 ->
        let uu____6662 = p_term false false e  in
        soft_parens_with_nesting uu____6662
    | FStar_Parser_AST.Product uu____6663 ->
        let uu____6670 = p_term false false e  in
        soft_parens_with_nesting uu____6670
    | FStar_Parser_AST.Sum uu____6671 ->
        let uu____6678 = p_term false false e  in
        soft_parens_with_nesting uu____6678
    | FStar_Parser_AST.QForall uu____6679 ->
        let uu____6692 = p_term false false e  in
        soft_parens_with_nesting uu____6692
    | FStar_Parser_AST.QExists uu____6693 ->
        let uu____6706 = p_term false false e  in
        soft_parens_with_nesting uu____6706
    | FStar_Parser_AST.Refine uu____6707 ->
        let uu____6712 = p_term false false e  in
        soft_parens_with_nesting uu____6712
    | FStar_Parser_AST.NamedTyp uu____6713 ->
        let uu____6718 = p_term false false e  in
        soft_parens_with_nesting uu____6718
    | FStar_Parser_AST.Requires uu____6719 ->
        let uu____6726 = p_term false false e  in
        soft_parens_with_nesting uu____6726
    | FStar_Parser_AST.Ensures uu____6727 ->
        let uu____6734 = p_term false false e  in
        soft_parens_with_nesting uu____6734
    | FStar_Parser_AST.Attributes uu____6735 ->
        let uu____6738 = p_term false false e  in
        soft_parens_with_nesting uu____6738
    | FStar_Parser_AST.Quote uu____6739 ->
        let uu____6744 = p_term false false e  in
        soft_parens_with_nesting uu____6744
    | FStar_Parser_AST.VQuote uu____6745 ->
        let uu____6746 = p_term false false e  in
        soft_parens_with_nesting uu____6746
    | FStar_Parser_AST.Antiquote uu____6747 ->
        let uu____6748 = p_term false false e  in
        soft_parens_with_nesting uu____6748

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___118_6749  ->
    match uu___118_6749 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6755) ->
        let uu____6756 = str s  in FStar_Pprint.dquotes uu____6756
    | FStar_Const.Const_bytearray (bytes,uu____6758) ->
        let uu____6765 =
          let uu____6766 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6766  in
        let uu____6767 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6765 uu____6767
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___116_6787 =
          match uu___116_6787 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___117_6793 =
          match uu___117_6793 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6804  ->
               match uu____6804 with
               | (s,w) ->
                   let uu____6811 = signedness s  in
                   let uu____6812 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6811 uu____6812)
            sign_width_opt
           in
        let uu____6813 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6813 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6815 = FStar_Range.string_of_range r  in str uu____6815
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6817 = p_quident lid  in
        let uu____6818 =
          let uu____6819 =
            let uu____6820 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6820  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6819  in
        FStar_Pprint.op_Hat_Hat uu____6817 uu____6818

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6822 = str "u#"  in
    let uu____6823 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6822 uu____6823

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6825;_},u1::u2::[])
        ->
        let uu____6830 =
          let uu____6831 = p_universeFrom u1  in
          let uu____6832 =
            let uu____6833 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6833  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6831 uu____6832  in
        FStar_Pprint.group uu____6830
    | FStar_Parser_AST.App uu____6834 ->
        let uu____6841 = head_and_args u  in
        (match uu____6841 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6867 =
                    let uu____6868 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6869 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6877  ->
                           match uu____6877 with
                           | (u1,uu____6883) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6868 uu____6869  in
                  FStar_Pprint.group uu____6867
              | uu____6884 ->
                  let uu____6885 =
                    let uu____6886 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6886
                     in
                  failwith uu____6885))
    | uu____6887 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6910 = FStar_Ident.text_of_id id1  in str uu____6910
    | FStar_Parser_AST.Paren u1 ->
        let uu____6912 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6912
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6913;_},uu____6914::uu____6915::[])
        ->
        let uu____6918 = p_universeFrom u  in
        soft_parens_with_nesting uu____6918
    | FStar_Parser_AST.App uu____6919 ->
        let uu____6926 = p_universeFrom u  in
        soft_parens_with_nesting uu____6926
    | uu____6927 ->
        let uu____6928 =
          let uu____6929 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6929
           in
        failwith uu____6928

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
       | FStar_Parser_AST.Module (uu____7001,decls) ->
           let uu____7007 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7007
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7016,decls,uu____7018) ->
           let uu____7023 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7023
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7076  ->
         match uu____7076 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7120,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7126,decls,uu____7128) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7173 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7186;
                 FStar_Parser_AST.doc = uu____7187;
                 FStar_Parser_AST.quals = uu____7188;
                 FStar_Parser_AST.attrs = uu____7189;_}::uu____7190 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7196 =
                   let uu____7199 =
                     let uu____7202 = FStar_List.tl ds  in d :: uu____7202
                      in
                   d0 :: uu____7199  in
                 (uu____7196, (d0.FStar_Parser_AST.drange))
             | uu____7207 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7173 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7267 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7267 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7363 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7363, comments1))))))
  