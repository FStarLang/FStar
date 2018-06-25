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
  fun uu___103_1220  ->
    match uu___103_1220 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___104_1245  ->
      match uu___104_1245 with
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
  let levels_from_associativity l uu___105_1432 =
    match uu___105_1432 with
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
        let rec p_list' uu___106_3445 =
          match uu___106_3445 with
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
  fun uu___107_3709  ->
    match uu___107_3709 with
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
    fun uu____3749  ->
      match uu____3749 with
      | (typedecl,fsdoc_opt) ->
          let uu____3762 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3762 with
           | (decl,body) ->
               let uu____3780 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3780)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___108_3782  ->
      match uu___108_3782 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3812 = FStar_Pprint.empty  in
          let uu____3813 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3813, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3834 =
            let uu____3835 = p_typ false false t  in jump2 uu____3835  in
          let uu____3836 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3836, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3890 =
            match uu____3890 with
            | (lid1,t,doc_opt) ->
                let uu____3906 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3906
             in
          let p_fields uu____3922 =
            let uu____3923 =
              let uu____3924 =
                let uu____3925 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3925 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3924  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3923  in
          let uu____3934 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3934, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____3995 =
            match uu____3995 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4021 =
                    let uu____4022 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4022  in
                  FStar_Range.extend_to_end_of_line uu____4021  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4048 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4061 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4061,
            ((fun uu____4067  ->
                let uu____4068 = datacon_doc ()  in jump2 uu____4068)))

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
  fun uu____4069  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4069 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4103 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4103  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4105 =
                        let uu____4108 =
                          let uu____4111 = p_fsdoc fsdoc  in
                          let uu____4112 =
                            let uu____4115 = cont lid_doc  in [uu____4115]
                             in
                          uu____4111 :: uu____4112  in
                        kw :: uu____4108  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4105
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4120 =
                        let uu____4121 =
                          let uu____4122 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4122 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4121
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4120
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4137 =
                          let uu____4138 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4138  in
                        prefix2 uu____4137 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4140  ->
      match uu____4140 with
      | (lid,t,doc_opt) ->
          let uu____4156 =
            let uu____4157 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4158 =
              let uu____4159 = p_lident lid  in
              let uu____4160 =
                let uu____4161 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4161  in
              FStar_Pprint.op_Hat_Hat uu____4159 uu____4160  in
            FStar_Pprint.op_Hat_Hat uu____4157 uu____4158  in
          FStar_Pprint.group uu____4156

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4162  ->
    match uu____4162 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4190 =
            let uu____4191 =
              let uu____4192 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4192  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4191  in
          FStar_Pprint.group uu____4190  in
        let uu____4193 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4194 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4198 =
                 let uu____4199 =
                   let uu____4200 =
                     let uu____4201 =
                       let uu____4202 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4202
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4201  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4200  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4199  in
               FStar_Pprint.group uu____4198) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4193 uu____4194

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4204  ->
      match uu____4204 with
      | (pat,uu____4210) ->
          let uu____4211 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4230 =
                  let uu____4231 =
                    let uu____4232 =
                      let uu____4233 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4233
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4232  in
                  FStar_Pprint.group uu____4231  in
                (pat1, uu____4230)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4245 =
                  let uu____4246 =
                    let uu____4247 =
                      let uu____4248 =
                        let uu____4249 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4249
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4248
                       in
                    FStar_Pprint.group uu____4247  in
                  let uu____4250 =
                    let uu____4251 =
                      let uu____4252 = str "by"  in
                      let uu____4253 =
                        let uu____4254 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4254
                         in
                      FStar_Pprint.op_Hat_Hat uu____4252 uu____4253  in
                    FStar_Pprint.group uu____4251  in
                  FStar_Pprint.op_Hat_Hat uu____4246 uu____4250  in
                (pat1, uu____4245)
            | uu____4255 -> (pat, FStar_Pprint.empty)  in
          (match uu____4211 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4259);
                       FStar_Parser_AST.prange = uu____4260;_},pats)
                    ->
                    let uu____4270 =
                      let uu____4271 =
                        let uu____4272 =
                          let uu____4273 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4273  in
                        FStar_Pprint.group uu____4272  in
                      let uu____4274 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4271 uu____4274  in
                    prefix2_nonempty uu____4270 ascr_doc
                | uu____4275 ->
                    let uu____4276 =
                      let uu____4277 =
                        let uu____4278 =
                          let uu____4279 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4279  in
                        FStar_Pprint.group uu____4278  in
                      FStar_Pprint.op_Hat_Hat uu____4277 ascr_doc  in
                    FStar_Pprint.group uu____4276))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4281  ->
      match uu____4281 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4290 =
            let uu____4291 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4291  in
          let uu____4292 =
            let uu____4293 =
              let uu____4294 =
                let uu____4295 =
                  let uu____4296 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4296  in
                FStar_Pprint.group uu____4295  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4294  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4293  in
          FStar_Pprint.ifflat uu____4290 uu____4292

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___109_4297  ->
    match uu___109_4297 with
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
        let uu____4322 = p_uident uid  in
        let uu____4323 = p_binders true bs  in
        let uu____4324 =
          let uu____4325 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4325  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4322 uu____4323 uu____4324

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
          let uu____4335 =
            let uu____4336 =
              let uu____4337 =
                let uu____4338 = p_uident uid  in
                let uu____4339 = p_binders true bs  in
                let uu____4340 =
                  let uu____4341 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4341  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4338 uu____4339 uu____4340
                 in
              FStar_Pprint.group uu____4337  in
            let uu____4342 =
              let uu____4343 = str "with"  in
              let uu____4344 =
                let uu____4345 =
                  let uu____4346 =
                    let uu____4347 =
                      let uu____4348 =
                        let uu____4349 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4349
                         in
                      separate_map_last uu____4348 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4347  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4346  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4345  in
              FStar_Pprint.op_Hat_Hat uu____4343 uu____4344  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4336 uu____4342  in
          braces_with_nesting uu____4335

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
          let uu____4380 =
            let uu____4381 = p_lident lid  in
            let uu____4382 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4381 uu____4382  in
          let uu____4383 = p_simpleTerm ps false e  in
          prefix2 uu____4380 uu____4383
      | uu____4384 ->
          let uu____4385 =
            let uu____4386 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4386
             in
          failwith uu____4385

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4448 =
        match uu____4448 with
        | (kwd,t) ->
            let uu____4455 =
              let uu____4456 = str kwd  in
              let uu____4457 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4456 uu____4457  in
            let uu____4458 = p_simpleTerm ps false t  in
            prefix2 uu____4455 uu____4458
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4463 =
      let uu____4464 =
        let uu____4465 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4466 =
          let uu____4467 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4467  in
        FStar_Pprint.op_Hat_Hat uu____4465 uu____4466  in
      let uu____4468 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4464 uu____4468  in
    let uu____4469 =
      let uu____4470 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4470  in
    FStar_Pprint.op_Hat_Hat uu____4463 uu____4469

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___110_4471  ->
    match uu___110_4471 with
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
    | uu____4473 ->
        let uu____4474 =
          let uu____4475 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4475  in
        FStar_Pprint.op_Hat_Hat uu____4474 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___111_4478  ->
    match uu___111_4478 with
    | FStar_Parser_AST.Rec  ->
        let uu____4479 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4479
    | FStar_Parser_AST.Mutable  ->
        let uu____4480 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4480
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___112_4481  ->
    match uu___112_4481 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4483 = str "#["  in
        let uu____4484 =
          let uu____4485 = p_term false false t  in
          let uu____4486 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4485 uu____4486  in
        FStar_Pprint.op_Hat_Hat uu____4483 uu____4484

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4491 =
          let uu____4492 =
            let uu____4493 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4493  in
          FStar_Pprint.separate_map uu____4492 p_tuplePattern pats  in
        FStar_Pprint.group uu____4491
    | uu____4494 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4501 =
          let uu____4502 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4502 p_constructorPattern pats  in
        FStar_Pprint.group uu____4501
    | uu____4503 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4506;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4511 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4512 = p_constructorPattern hd1  in
        let uu____4513 = p_constructorPattern tl1  in
        infix0 uu____4511 uu____4512 uu____4513
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4515;_},pats)
        ->
        let uu____4521 = p_quident uid  in
        let uu____4522 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4521 uu____4522
    | uu____4523 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4539;
               FStar_Parser_AST.blevel = uu____4540;
               FStar_Parser_AST.aqual = uu____4541;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4549 =
               let uu____4550 = p_ident lid  in
               p_refinement aqual uu____4550 t1 phi  in
             soft_parens_with_nesting uu____4549
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4552;
               FStar_Parser_AST.blevel = uu____4553;
               FStar_Parser_AST.aqual = uu____4554;_},phi))
             ->
             let uu____4558 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4558
         | uu____4559 ->
             let uu____4564 =
               let uu____4565 = p_tuplePattern pat  in
               let uu____4566 =
                 let uu____4567 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4567
                  in
               FStar_Pprint.op_Hat_Hat uu____4565 uu____4566  in
             soft_parens_with_nesting uu____4564)
    | FStar_Parser_AST.PatList pats ->
        let uu____4571 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4571 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4588 =
          match uu____4588 with
          | (lid,pat) ->
              let uu____4595 = p_qlident lid  in
              let uu____4596 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4595 uu____4596
           in
        let uu____4597 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4597
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4607 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4608 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4609 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4607 uu____4608 uu____4609
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4618 =
          let uu____4619 =
            let uu____4620 =
              let uu____4621 = FStar_Ident.text_of_id op  in str uu____4621
               in
            let uu____4622 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4620 uu____4622  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4619  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4618
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4630 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4631 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4630 uu____4631
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4633 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4636;
           FStar_Parser_AST.prange = uu____4637;_},uu____4638)
        ->
        let uu____4643 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4643
    | FStar_Parser_AST.PatTuple (uu____4644,false ) ->
        let uu____4649 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4649
    | uu____4650 ->
        let uu____4651 =
          let uu____4652 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4652  in
        failwith uu____4651

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4654;_},uu____4655)
        -> true
    | uu____4660 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4664 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4665 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4664 uu____4665
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4672;
                   FStar_Parser_AST.blevel = uu____4673;
                   FStar_Parser_AST.aqual = uu____4674;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4678 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4678 t1 phi
            | uu____4679 ->
                let t' =
                  let uu____4681 = is_typ_tuple t  in
                  if uu____4681
                  then
                    let uu____4682 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4682
                  else p_tmFormula t  in
                let uu____4684 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4685 =
                  let uu____4686 = p_lident lid  in
                  let uu____4687 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4686 uu____4687  in
                FStar_Pprint.op_Hat_Hat uu____4684 uu____4685
             in
          if is_atomic
          then
            let uu____4688 =
              let uu____4689 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4689  in
            FStar_Pprint.group uu____4688
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4691 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4698;
                  FStar_Parser_AST.blevel = uu____4699;
                  FStar_Parser_AST.aqual = uu____4700;_},phi)
               ->
               if is_atomic
               then
                 let uu____4704 =
                   let uu____4705 =
                     let uu____4706 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4706 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4705  in
                 FStar_Pprint.group uu____4704
               else
                 (let uu____4708 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4708)
           | uu____4709 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4718 -> false
            | FStar_Parser_AST.App uu____4729 -> false
            | FStar_Parser_AST.Op uu____4736 -> false
            | uu____4743 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4747 =
            let uu____4748 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4749 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4748 uu____4749  in
          let uu____4750 =
            let uu____4751 = p_appTerm t  in
            let uu____4752 =
              let uu____4753 =
                let uu____4754 =
                  let uu____4755 = soft_braces_with_nesting_tight phi1  in
                  let uu____4756 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4755 uu____4756  in
                FStar_Pprint.group uu____4754  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4753
               in
            FStar_Pprint.op_Hat_Hat uu____4751 uu____4752  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4747 uu____4750

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4767 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4767

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4772 = FStar_Ident.text_of_id lid  in str uu____4772)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4775 = FStar_Ident.text_of_lid lid  in str uu____4775)

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
            let uu____4793 =
              let uu____4794 =
                let uu____4795 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4795 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4794  in
            let uu____4796 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4793 uu____4796
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4800 =
              let uu____4801 =
                let uu____4802 =
                  let uu____4803 = p_lident x  in
                  let uu____4804 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4803 uu____4804  in
                let uu____4805 =
                  let uu____4806 = p_noSeqTerm true false e1  in
                  let uu____4807 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4806 uu____4807  in
                op_Hat_Slash_Plus_Hat uu____4802 uu____4805  in
              FStar_Pprint.group uu____4801  in
            let uu____4808 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4800 uu____4808
        | uu____4809 ->
            let uu____4810 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4810

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
            let uu____4821 =
              let uu____4822 = p_tmIff e1  in
              let uu____4823 =
                let uu____4824 =
                  let uu____4825 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4825
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4824  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4822 uu____4823  in
            FStar_Pprint.group uu____4821
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4831 =
              let uu____4832 = p_tmIff e1  in
              let uu____4833 =
                let uu____4834 =
                  let uu____4835 =
                    let uu____4836 = p_typ false false t  in
                    let uu____4837 =
                      let uu____4838 = str "by"  in
                      let uu____4839 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4838 uu____4839  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4836 uu____4837  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4835
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4834  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4832 uu____4833  in
            FStar_Pprint.group uu____4831
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4840;_},e1::e2::e3::[])
            ->
            let uu____4846 =
              let uu____4847 =
                let uu____4848 =
                  let uu____4849 = p_atomicTermNotQUident e1  in
                  let uu____4850 =
                    let uu____4851 =
                      let uu____4852 =
                        let uu____4853 = p_term false false e2  in
                        soft_parens_with_nesting uu____4853  in
                      let uu____4854 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4852 uu____4854  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4851  in
                  FStar_Pprint.op_Hat_Hat uu____4849 uu____4850  in
                FStar_Pprint.group uu____4848  in
              let uu____4855 =
                let uu____4856 = p_noSeqTerm ps pb e3  in jump2 uu____4856
                 in
              FStar_Pprint.op_Hat_Hat uu____4847 uu____4855  in
            FStar_Pprint.group uu____4846
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
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
                        soft_brackets_with_nesting uu____4870  in
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
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4881 =
              let uu____4882 = str "requires"  in
              let uu____4883 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4882 uu____4883  in
            FStar_Pprint.group uu____4881
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4891 =
              let uu____4892 = str "ensures"  in
              let uu____4893 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4892 uu____4893  in
            FStar_Pprint.group uu____4891
        | FStar_Parser_AST.Attributes es ->
            let uu____4897 =
              let uu____4898 = str "attributes"  in
              let uu____4899 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4898 uu____4899  in
            FStar_Pprint.group uu____4897
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4903 =
                let uu____4904 =
                  let uu____4905 = str "if"  in
                  let uu____4906 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4905 uu____4906  in
                let uu____4907 =
                  let uu____4908 = str "then"  in
                  let uu____4909 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4908 uu____4909  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4904 uu____4907  in
              FStar_Pprint.group uu____4903
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4912,uu____4913,e31) when
                     is_unit e31 ->
                     let uu____4915 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4915
                 | uu____4916 -> p_noSeqTerm false false e2  in
               let uu____4917 =
                 let uu____4918 =
                   let uu____4919 = str "if"  in
                   let uu____4920 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4919 uu____4920  in
                 let uu____4921 =
                   let uu____4922 =
                     let uu____4923 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4923 e2_doc  in
                   let uu____4924 =
                     let uu____4925 = str "else"  in
                     let uu____4926 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4925 uu____4926  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4922 uu____4924  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4918 uu____4921  in
               FStar_Pprint.group uu____4917)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4949 =
              let uu____4950 =
                let uu____4951 =
                  let uu____4952 = str "try"  in
                  let uu____4953 = p_noSeqTerm false false e1  in
                  prefix2 uu____4952 uu____4953  in
                let uu____4954 =
                  let uu____4955 = str "with"  in
                  let uu____4956 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4955 uu____4956  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4951 uu____4954  in
              FStar_Pprint.group uu____4950  in
            let uu____4965 = paren_if (ps || pb)  in uu____4965 uu____4949
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4992 =
              let uu____4993 =
                let uu____4994 =
                  let uu____4995 = str "match"  in
                  let uu____4996 = p_noSeqTerm false false e1  in
                  let uu____4997 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4995 uu____4996 uu____4997
                   in
                let uu____4998 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4994 uu____4998  in
              FStar_Pprint.group uu____4993  in
            let uu____5007 = paren_if (ps || pb)  in uu____5007 uu____4992
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5014 =
              let uu____5015 =
                let uu____5016 =
                  let uu____5017 = str "let open"  in
                  let uu____5018 = p_quident uid  in
                  let uu____5019 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5017 uu____5018 uu____5019
                   in
                let uu____5020 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5016 uu____5020  in
              FStar_Pprint.group uu____5015  in
            let uu____5021 = paren_if ps  in uu____5021 uu____5014
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5085 is_last =
              match uu____5085 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5118 =
                          let uu____5119 = str "let"  in
                          let uu____5120 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5119 uu____5120
                           in
                        FStar_Pprint.group uu____5118
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5121 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5126 =
                    if is_last
                    then
                      let uu____5127 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5128 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5127 doc_expr uu____5128
                    else
                      (let uu____5130 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5130)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5126
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5176 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5176
                     else
                       (let uu____5184 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5184)) lbs
               in
            let lbs_doc =
              let uu____5192 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5192  in
            let uu____5193 =
              let uu____5194 =
                let uu____5195 =
                  let uu____5196 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5196
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5195  in
              FStar_Pprint.group uu____5194  in
            let uu____5197 = paren_if ps  in uu____5197 uu____5193
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5204;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5207;
                                                             FStar_Parser_AST.level
                                                               = uu____5208;_})
            when matches_var maybe_x x ->
            let uu____5235 =
              let uu____5236 =
                let uu____5237 = str "function"  in
                let uu____5238 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5237 uu____5238  in
              FStar_Pprint.group uu____5236  in
            let uu____5247 = paren_if (ps || pb)  in uu____5247 uu____5235
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5253 =
              let uu____5254 = str "quote"  in
              let uu____5255 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5254 uu____5255  in
            FStar_Pprint.group uu____5253
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5257 =
              let uu____5258 = str "`"  in
              let uu____5259 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5258 uu____5259  in
            FStar_Pprint.group uu____5257
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5261 =
              let uu____5262 = str "`%"  in
              let uu____5263 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5262 uu____5263  in
            FStar_Pprint.group uu____5261
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5265 =
              let uu____5266 = str "`#"  in
              let uu____5267 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5266 uu____5267  in
            FStar_Pprint.group uu____5265
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5269 =
              let uu____5270 = str "`@"  in
              let uu____5271 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5270 uu____5271  in
            FStar_Pprint.group uu____5269
        | uu____5272 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___113_5273  ->
    match uu___113_5273 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5285 =
          let uu____5286 = str "[@"  in
          let uu____5287 =
            let uu____5288 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5289 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5288 uu____5289  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5286 uu____5287  in
        FStar_Pprint.group uu____5285

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
                 let uu____5315 =
                   let uu____5316 =
                     let uu____5317 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5317 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5316 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5315 term_doc
             | pats ->
                 let uu____5323 =
                   let uu____5324 =
                     let uu____5325 =
                       let uu____5326 =
                         let uu____5327 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5327
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5326 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5328 = p_trigger trigger  in
                     prefix2 uu____5325 uu____5328  in
                   FStar_Pprint.group uu____5324  in
                 prefix2 uu____5323 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5348 =
                   let uu____5349 =
                     let uu____5350 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5350 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5349 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5348 term_doc
             | pats ->
                 let uu____5356 =
                   let uu____5357 =
                     let uu____5358 =
                       let uu____5359 =
                         let uu____5360 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5360
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5359 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5361 = p_trigger trigger  in
                     prefix2 uu____5358 uu____5361  in
                   FStar_Pprint.group uu____5357  in
                 prefix2 uu____5356 term_doc)
        | uu____5362 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5364 -> str "forall"
    | FStar_Parser_AST.QExists uu____5377 -> str "exists"
    | uu____5390 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___114_5391  ->
    match uu___114_5391 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5403 =
          let uu____5404 =
            let uu____5405 =
              let uu____5406 = str "pattern"  in
              let uu____5407 =
                let uu____5408 =
                  let uu____5409 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5409
                   in
                FStar_Pprint.op_Hat_Hat uu____5408 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5406 uu____5407  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5405  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5404  in
        FStar_Pprint.group uu____5403

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5415 = str "\\/"  in
    FStar_Pprint.separate_map uu____5415 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5421 =
      let uu____5422 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5422 p_appTerm pats  in
    FStar_Pprint.group uu____5421

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5432 =
              let uu____5433 =
                let uu____5434 = str "fun"  in
                let uu____5435 =
                  let uu____5436 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5436
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5434 uu____5435  in
              let uu____5437 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5433 uu____5437  in
            let uu____5438 = paren_if ps  in uu____5438 uu____5432
        | uu____5443 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5447  ->
      match uu____5447 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5470 =
                    let uu____5471 =
                      let uu____5472 =
                        let uu____5473 = p_tuplePattern p  in
                        let uu____5474 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5473 uu____5474  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5472
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5471  in
                  FStar_Pprint.group uu____5470
              | FStar_Pervasives_Native.Some f ->
                  let uu____5476 =
                    let uu____5477 =
                      let uu____5478 =
                        let uu____5479 =
                          let uu____5480 =
                            let uu____5481 = p_tuplePattern p  in
                            let uu____5482 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5481
                              uu____5482
                             in
                          FStar_Pprint.group uu____5480  in
                        let uu____5483 =
                          let uu____5484 =
                            let uu____5487 = p_tmFormula f  in
                            [uu____5487; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5484  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5479 uu____5483
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5478
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5477  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5476
               in
            let uu____5488 =
              let uu____5489 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5489  in
            FStar_Pprint.group uu____5488  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5498 =
                      let uu____5499 =
                        let uu____5500 =
                          let uu____5501 =
                            let uu____5502 =
                              let uu____5503 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5503  in
                            FStar_Pprint.separate_map uu____5502
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5501
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5500
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5499  in
                    FStar_Pprint.group uu____5498
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5504 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5506;_},e1::e2::[])
        ->
        let uu____5511 = str "<==>"  in
        let uu____5512 = p_tmImplies e1  in
        let uu____5513 = p_tmIff e2  in
        infix0 uu____5511 uu____5512 uu____5513
    | uu____5514 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5516;_},e1::e2::[])
        ->
        let uu____5521 = str "==>"  in
        let uu____5522 = p_tmArrow p_tmFormula e1  in
        let uu____5523 = p_tmImplies e2  in
        infix0 uu____5521 uu____5522 uu____5523
    | uu____5524 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5532 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5532 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5553 ->
               let uu____5554 =
                 let uu____5555 =
                   let uu____5556 =
                     let uu____5557 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5557
                      in
                   FStar_Pprint.separate uu____5556 terms  in
                 let uu____5558 =
                   let uu____5559 =
                     let uu____5560 =
                       let uu____5561 =
                         let uu____5562 =
                           let uu____5563 =
                             let uu____5564 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5564
                              in
                           FStar_Pprint.separate uu____5563 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5562 last_op  in
                       let uu____5565 =
                         let uu____5566 =
                           let uu____5567 =
                             let uu____5568 =
                               let uu____5569 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5569
                                in
                             FStar_Pprint.separate uu____5568 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5567 last_op  in
                         jump2 uu____5566  in
                       FStar_Pprint.ifflat uu____5561 uu____5565  in
                     FStar_Pprint.group uu____5560  in
                   let uu____5570 = FStar_List.hd last1  in
                   prefix2 uu____5559 uu____5570  in
                 FStar_Pprint.ifflat uu____5555 uu____5558  in
               FStar_Pprint.group uu____5554)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5583 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5588 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5583 uu____5588
      | uu____5591 -> let uu____5592 = p_Tm e  in [uu____5592]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5595 =
        let uu____5596 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5596 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5595  in
    let disj =
      let uu____5598 =
        let uu____5599 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5599 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5598  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5618;_},e1::e2::[])
        ->
        let uu____5623 = p_tmDisjunction e1  in
        let uu____5628 = let uu____5633 = p_tmConjunction e2  in [uu____5633]
           in
        FStar_List.append uu____5623 uu____5628
    | uu____5642 -> let uu____5643 = p_tmConjunction e  in [uu____5643]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5653;_},e1::e2::[])
        ->
        let uu____5658 = p_tmConjunction e1  in
        let uu____5661 = let uu____5664 = p_tmTuple e2  in [uu____5664]  in
        FStar_List.append uu____5658 uu____5661
    | uu____5665 -> let uu____5666 = p_tmTuple e  in [uu____5666]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5683 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5683
          (fun uu____5691  ->
             match uu____5691 with | (e1,uu____5697) -> p_tmEq e1) args
    | uu____5698 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5703 =
             let uu____5704 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5704  in
           FStar_Pprint.group uu____5703)

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
               (let uu____5721 = FStar_Ident.text_of_id op  in
                uu____5721 = "="))
              ||
              (let uu____5723 = FStar_Ident.text_of_id op  in
               uu____5723 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5725 = levels op1  in
            (match uu____5725 with
             | (left1,mine,right1) ->
                 let uu____5735 =
                   let uu____5736 = FStar_All.pipe_left str op1  in
                   let uu____5737 = p_tmEqWith' p_X left1 e1  in
                   let uu____5738 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5736 uu____5737 uu____5738  in
                 paren_if_gt curr mine uu____5735)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5739;_},e1::e2::[])
            ->
            let uu____5744 =
              let uu____5745 = p_tmEqWith p_X e1  in
              let uu____5746 =
                let uu____5747 =
                  let uu____5748 =
                    let uu____5749 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5749  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5748  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5747  in
              FStar_Pprint.op_Hat_Hat uu____5745 uu____5746  in
            FStar_Pprint.group uu____5744
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5750;_},e1::[])
            ->
            let uu____5754 = levels "-"  in
            (match uu____5754 with
             | (left1,mine,right1) ->
                 let uu____5764 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5764)
        | uu____5765 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5809)::(e2,uu____5811)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5831 = is_list e  in Prims.op_Negation uu____5831)
              ->
              let op = "::"  in
              let uu____5833 = levels op  in
              (match uu____5833 with
               | (left1,mine,right1) ->
                   let uu____5843 =
                     let uu____5844 = str op  in
                     let uu____5845 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5846 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5844 uu____5845 uu____5846  in
                   paren_if_gt curr mine uu____5843)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5854 = levels op  in
              (match uu____5854 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5870 = p_binder false b  in
                     let uu____5871 =
                       let uu____5872 =
                         let uu____5873 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5873 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5872
                        in
                     FStar_Pprint.op_Hat_Hat uu____5870 uu____5871  in
                   let uu____5874 =
                     let uu____5875 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5876 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5875 uu____5876  in
                   paren_if_gt curr mine uu____5874)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5877;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5902 = levels op  in
              (match uu____5902 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5912 = str op  in
                     let uu____5913 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5914 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5912 uu____5913 uu____5914
                   else
                     (let uu____5916 =
                        let uu____5917 = str op  in
                        let uu____5918 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5919 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5917 uu____5918 uu____5919  in
                      paren_if_gt curr mine uu____5916))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5926 = levels op1  in
              (match uu____5926 with
               | (left1,mine,right1) ->
                   let uu____5936 =
                     let uu____5937 = str op1  in
                     let uu____5938 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5939 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5937 uu____5938 uu____5939  in
                   paren_if_gt curr mine uu____5936)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5958 =
                let uu____5959 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5960 =
                  let uu____5961 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5961 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5959 uu____5960  in
              braces_with_nesting uu____5958
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5966;_},e1::[])
              ->
              let uu____5970 =
                let uu____5971 = str "~"  in
                let uu____5972 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5971 uu____5972  in
              FStar_Pprint.group uu____5970
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____5974;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____5980 = levels op  in
                   (match uu____5980 with
                    | (left1,mine,right1) ->
                        let uu____5990 =
                          let uu____5991 = str op  in
                          let uu____5992 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____5993 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____5991 uu____5992 uu____5993  in
                        paren_if_gt curr mine uu____5990)
               | uu____5994 -> p_X e)
          | uu____5995 -> p_X e

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
        let uu____6002 =
          let uu____6003 = p_lident lid  in
          let uu____6004 =
            let uu____6005 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6005  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6003 uu____6004  in
        FStar_Pprint.group uu____6002
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6008 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6010 = p_appTerm e  in
    let uu____6011 =
      let uu____6012 =
        let uu____6013 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6013 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6012  in
    FStar_Pprint.op_Hat_Hat uu____6010 uu____6011

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6018 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6018 t phi
      | FStar_Parser_AST.TAnnotated uu____6019 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6024 ->
          let uu____6025 =
            let uu____6026 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6026
             in
          failwith uu____6025
      | FStar_Parser_AST.TVariable uu____6027 ->
          let uu____6028 =
            let uu____6029 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6029
             in
          failwith uu____6028
      | FStar_Parser_AST.NoName uu____6030 ->
          let uu____6031 =
            let uu____6032 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6032
             in
          failwith uu____6031

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6034  ->
      match uu____6034 with
      | (lid,e) ->
          let uu____6041 =
            let uu____6042 = p_qlident lid  in
            let uu____6043 =
              let uu____6044 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6044
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6042 uu____6043  in
          FStar_Pprint.group uu____6041

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6046 when is_general_application e ->
        let uu____6053 = head_and_args e  in
        (match uu____6053 with
         | (head1,args) ->
             let uu____6078 =
               let uu____6089 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6089
               then
                 let uu____6119 =
                   FStar_Util.take
                     (fun uu____6143  ->
                        match uu____6143 with
                        | (uu____6148,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6119 with
                 | (fs_typ_args,args1) ->
                     let uu____6186 =
                       let uu____6187 = p_indexingTerm head1  in
                       let uu____6188 =
                         let uu____6189 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6189 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6187 uu____6188  in
                     (uu____6186, args1)
               else
                 (let uu____6201 = p_indexingTerm head1  in
                  (uu____6201, args))
                in
             (match uu____6078 with
              | (head_doc,args1) ->
                  let uu____6222 =
                    let uu____6223 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6223 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6222))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6243 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6243)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6261 =
               let uu____6262 = p_quident lid  in
               let uu____6263 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6262 uu____6263  in
             FStar_Pprint.group uu____6261
         | hd1::tl1 ->
             let uu____6280 =
               let uu____6281 =
                 let uu____6282 =
                   let uu____6283 = p_quident lid  in
                   let uu____6284 = p_argTerm hd1  in
                   prefix2 uu____6283 uu____6284  in
                 FStar_Pprint.group uu____6282  in
               let uu____6285 =
                 let uu____6286 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6286  in
               FStar_Pprint.op_Hat_Hat uu____6281 uu____6285  in
             FStar_Pprint.group uu____6280)
    | uu____6291 -> p_indexingTerm e

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
         (let uu____6300 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6300 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6302 = str "#"  in
        let uu____6303 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6302 uu____6303
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6306 = str "#["  in
        let uu____6307 =
          let uu____6308 = p_indexingTerm t  in
          let uu____6309 =
            let uu____6310 = str "]"  in
            let uu____6311 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6310 uu____6311  in
          FStar_Pprint.op_Hat_Hat uu____6308 uu____6309  in
        FStar_Pprint.op_Hat_Hat uu____6306 uu____6307
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6313  ->
    match uu____6313 with | (e,uu____6319) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6324;_},e1::e2::[])
          ->
          let uu____6329 =
            let uu____6330 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6331 =
              let uu____6332 =
                let uu____6333 = p_term false false e2  in
                soft_parens_with_nesting uu____6333  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6332  in
            FStar_Pprint.op_Hat_Hat uu____6330 uu____6331  in
          FStar_Pprint.group uu____6329
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6334;_},e1::e2::[])
          ->
          let uu____6339 =
            let uu____6340 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6341 =
              let uu____6342 =
                let uu____6343 = p_term false false e2  in
                soft_brackets_with_nesting uu____6343  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6342  in
            FStar_Pprint.op_Hat_Hat uu____6340 uu____6341  in
          FStar_Pprint.group uu____6339
      | uu____6344 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6349 = p_quident lid  in
        let uu____6350 =
          let uu____6351 =
            let uu____6352 = p_term false false e1  in
            soft_parens_with_nesting uu____6352  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6351  in
        FStar_Pprint.op_Hat_Hat uu____6349 uu____6350
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6358 =
          let uu____6359 = FStar_Ident.text_of_id op  in str uu____6359  in
        let uu____6360 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6358 uu____6360
    | uu____6361 -> p_atomicTermNotQUident e

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
         | uu____6370 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6377 =
          let uu____6378 = FStar_Ident.text_of_id op  in str uu____6378  in
        let uu____6379 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6377 uu____6379
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6383 =
          let uu____6384 =
            let uu____6385 =
              let uu____6386 = FStar_Ident.text_of_id op  in str uu____6386
               in
            let uu____6387 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6385 uu____6387  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6384  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6383
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6402 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6403 =
          let uu____6404 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6405 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6404 p_tmEq uu____6405  in
        let uu____6412 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6402 uu____6403 uu____6412
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6415 =
          let uu____6416 = p_atomicTermNotQUident e1  in
          let uu____6417 =
            let uu____6418 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6418  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6416 uu____6417
           in
        FStar_Pprint.group uu____6415
    | uu____6419 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6424 = p_quident constr_lid  in
        let uu____6425 =
          let uu____6426 =
            let uu____6427 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6427  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6426  in
        FStar_Pprint.op_Hat_Hat uu____6424 uu____6425
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6429 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6429 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6431 = p_term false false e1  in
        soft_parens_with_nesting uu____6431
    | uu____6432 when is_array e ->
        let es = extract_from_list e  in
        let uu____6436 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6437 =
          let uu____6438 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6438
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6441 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6436 uu____6437 uu____6441
    | uu____6442 when is_list e ->
        let uu____6443 =
          let uu____6444 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6445 = extract_from_list e  in
          separate_map_or_flow_last uu____6444
            (fun ps  -> p_noSeqTerm ps false) uu____6445
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6443 FStar_Pprint.rbracket
    | uu____6450 when is_lex_list e ->
        let uu____6451 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6452 =
          let uu____6453 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6454 = extract_from_list e  in
          separate_map_or_flow_last uu____6453
            (fun ps  -> p_noSeqTerm ps false) uu____6454
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6451 uu____6452 FStar_Pprint.rbracket
    | uu____6459 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6463 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6464 =
          let uu____6465 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6465 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6463 uu____6464 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6469 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6470 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6469 uu____6470
    | FStar_Parser_AST.Op (op,args) when
        let uu____6477 = handleable_op op args  in
        Prims.op_Negation uu____6477 ->
        let uu____6478 =
          let uu____6479 =
            let uu____6480 = FStar_Ident.text_of_id op  in
            let uu____6481 =
              let uu____6482 =
                let uu____6483 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6483
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6482  in
            Prims.strcat uu____6480 uu____6481  in
          Prims.strcat "Operation " uu____6479  in
        failwith uu____6478
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6485 = str "u#"  in
        let uu____6486 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6485 uu____6486
    | FStar_Parser_AST.Wild  ->
        let uu____6487 = p_term false false e  in
        soft_parens_with_nesting uu____6487
    | FStar_Parser_AST.Const uu____6488 ->
        let uu____6489 = p_term false false e  in
        soft_parens_with_nesting uu____6489
    | FStar_Parser_AST.Op uu____6490 ->
        let uu____6497 = p_term false false e  in
        soft_parens_with_nesting uu____6497
    | FStar_Parser_AST.Tvar uu____6498 ->
        let uu____6499 = p_term false false e  in
        soft_parens_with_nesting uu____6499
    | FStar_Parser_AST.Var uu____6500 ->
        let uu____6501 = p_term false false e  in
        soft_parens_with_nesting uu____6501
    | FStar_Parser_AST.Name uu____6502 ->
        let uu____6503 = p_term false false e  in
        soft_parens_with_nesting uu____6503
    | FStar_Parser_AST.Construct uu____6504 ->
        let uu____6515 = p_term false false e  in
        soft_parens_with_nesting uu____6515
    | FStar_Parser_AST.Abs uu____6516 ->
        let uu____6523 = p_term false false e  in
        soft_parens_with_nesting uu____6523
    | FStar_Parser_AST.App uu____6524 ->
        let uu____6531 = p_term false false e  in
        soft_parens_with_nesting uu____6531
    | FStar_Parser_AST.Let uu____6532 ->
        let uu____6553 = p_term false false e  in
        soft_parens_with_nesting uu____6553
    | FStar_Parser_AST.LetOpen uu____6554 ->
        let uu____6559 = p_term false false e  in
        soft_parens_with_nesting uu____6559
    | FStar_Parser_AST.Seq uu____6560 ->
        let uu____6565 = p_term false false e  in
        soft_parens_with_nesting uu____6565
    | FStar_Parser_AST.Bind uu____6566 ->
        let uu____6573 = p_term false false e  in
        soft_parens_with_nesting uu____6573
    | FStar_Parser_AST.If uu____6574 ->
        let uu____6581 = p_term false false e  in
        soft_parens_with_nesting uu____6581
    | FStar_Parser_AST.Match uu____6582 ->
        let uu____6597 = p_term false false e  in
        soft_parens_with_nesting uu____6597
    | FStar_Parser_AST.TryWith uu____6598 ->
        let uu____6613 = p_term false false e  in
        soft_parens_with_nesting uu____6613
    | FStar_Parser_AST.Ascribed uu____6614 ->
        let uu____6623 = p_term false false e  in
        soft_parens_with_nesting uu____6623
    | FStar_Parser_AST.Record uu____6624 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Project uu____6638 ->
        let uu____6643 = p_term false false e  in
        soft_parens_with_nesting uu____6643
    | FStar_Parser_AST.Product uu____6644 ->
        let uu____6651 = p_term false false e  in
        soft_parens_with_nesting uu____6651
    | FStar_Parser_AST.Sum uu____6652 ->
        let uu____6659 = p_term false false e  in
        soft_parens_with_nesting uu____6659
    | FStar_Parser_AST.QForall uu____6660 ->
        let uu____6673 = p_term false false e  in
        soft_parens_with_nesting uu____6673
    | FStar_Parser_AST.QExists uu____6674 ->
        let uu____6687 = p_term false false e  in
        soft_parens_with_nesting uu____6687
    | FStar_Parser_AST.Refine uu____6688 ->
        let uu____6693 = p_term false false e  in
        soft_parens_with_nesting uu____6693
    | FStar_Parser_AST.NamedTyp uu____6694 ->
        let uu____6699 = p_term false false e  in
        soft_parens_with_nesting uu____6699
    | FStar_Parser_AST.Requires uu____6700 ->
        let uu____6707 = p_term false false e  in
        soft_parens_with_nesting uu____6707
    | FStar_Parser_AST.Ensures uu____6708 ->
        let uu____6715 = p_term false false e  in
        soft_parens_with_nesting uu____6715
    | FStar_Parser_AST.Attributes uu____6716 ->
        let uu____6719 = p_term false false e  in
        soft_parens_with_nesting uu____6719
    | FStar_Parser_AST.Quote uu____6720 ->
        let uu____6725 = p_term false false e  in
        soft_parens_with_nesting uu____6725
    | FStar_Parser_AST.VQuote uu____6726 ->
        let uu____6727 = p_term false false e  in
        soft_parens_with_nesting uu____6727
    | FStar_Parser_AST.Antiquote uu____6728 ->
        let uu____6733 = p_term false false e  in
        soft_parens_with_nesting uu____6733

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___117_6734  ->
    match uu___117_6734 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6740) ->
        let uu____6741 = str s  in FStar_Pprint.dquotes uu____6741
    | FStar_Const.Const_bytearray (bytes,uu____6743) ->
        let uu____6750 =
          let uu____6751 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6751  in
        let uu____6752 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6750 uu____6752
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___115_6772 =
          match uu___115_6772 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___116_6778 =
          match uu___116_6778 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6789  ->
               match uu____6789 with
               | (s,w) ->
                   let uu____6796 = signedness s  in
                   let uu____6797 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6796 uu____6797)
            sign_width_opt
           in
        let uu____6798 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6798 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6800 = FStar_Range.string_of_range r  in str uu____6800
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6802 = p_quident lid  in
        let uu____6803 =
          let uu____6804 =
            let uu____6805 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6805  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6804  in
        FStar_Pprint.op_Hat_Hat uu____6802 uu____6803

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6807 = str "u#"  in
    let uu____6808 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6807 uu____6808

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6810;_},u1::u2::[])
        ->
        let uu____6815 =
          let uu____6816 = p_universeFrom u1  in
          let uu____6817 =
            let uu____6818 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6818  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6816 uu____6817  in
        FStar_Pprint.group uu____6815
    | FStar_Parser_AST.App uu____6819 ->
        let uu____6826 = head_and_args u  in
        (match uu____6826 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6852 =
                    let uu____6853 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6854 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6862  ->
                           match uu____6862 with
                           | (u1,uu____6868) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6853 uu____6854  in
                  FStar_Pprint.group uu____6852
              | uu____6869 ->
                  let uu____6870 =
                    let uu____6871 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6871
                     in
                  failwith uu____6870))
    | uu____6872 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6895 = FStar_Ident.text_of_id id1  in str uu____6895
    | FStar_Parser_AST.Paren u1 ->
        let uu____6897 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6897
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6898;_},uu____6899::uu____6900::[])
        ->
        let uu____6903 = p_universeFrom u  in
        soft_parens_with_nesting uu____6903
    | FStar_Parser_AST.App uu____6904 ->
        let uu____6911 = p_universeFrom u  in
        soft_parens_with_nesting uu____6911
    | uu____6912 ->
        let uu____6913 =
          let uu____6914 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6914
           in
        failwith uu____6913

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
       | FStar_Parser_AST.Module (uu____6986,decls) ->
           let uu____6992 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6992
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7001,decls,uu____7003) ->
           let uu____7008 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7008
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7061  ->
         match uu____7061 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7105,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7111,decls,uu____7113) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7158 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7171;
                 FStar_Parser_AST.doc = uu____7172;
                 FStar_Parser_AST.quals = uu____7173;
                 FStar_Parser_AST.attrs = uu____7174;_}::uu____7175 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7181 =
                   let uu____7184 =
                     let uu____7187 = FStar_List.tl ds  in d :: uu____7187
                      in
                   d0 :: uu____7184  in
                 (uu____7181, (d0.FStar_Parser_AST.drange))
             | uu____7192 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7158 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7252 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7252 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7348 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7348, comments1))))))
  