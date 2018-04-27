open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____24 'Auu____25 .
    Prims.bool -> ('Auu____24 -> 'Auu____25) -> 'Auu____24 -> 'Auu____25
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
  'Auu____134 'Auu____135 .
    'Auu____134 ->
      ('Auu____135 -> 'Auu____134) ->
        'Auu____135 FStar_Pervasives_Native.option -> 'Auu____134
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
  'Auu____229 .
    FStar_Pprint.document ->
      ('Auu____229 -> FStar_Pprint.document) ->
        'Auu____229 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____254 =
          let uu____255 =
            let uu____256 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____256  in
          FStar_Pprint.separate_map uu____255 f l  in
        FStar_Pprint.group uu____254
  
let precede_break_separate_map :
  'Auu____267 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____267 -> FStar_Pprint.document) ->
          'Auu____267 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____297 =
            let uu____298 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____299 =
              let uu____300 = FStar_List.hd l  in
              FStar_All.pipe_right uu____300 f  in
            FStar_Pprint.precede uu____298 uu____299  in
          let uu____301 =
            let uu____302 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____308 =
                   let uu____309 =
                     let uu____310 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____310  in
                   FStar_Pprint.op_Hat_Hat sep uu____309  in
                 FStar_Pprint.op_Hat_Hat break1 uu____308) uu____302
             in
          FStar_Pprint.op_Hat_Hat uu____297 uu____301
  
let concat_break_map :
  'Auu____317 .
    ('Auu____317 -> FStar_Pprint.document) ->
      'Auu____317 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____337 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____341 = f x  in FStar_Pprint.op_Hat_Hat uu____341 break1)
          l
         in
      FStar_Pprint.group uu____337
  
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
    let uu____382 = str "begin"  in
    let uu____383 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____382 contents uu____383
  
let separate_map_last :
  'Auu____392 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____392 -> FStar_Pprint.document) ->
        'Auu____392 Prims.list -> FStar_Pprint.document
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
  'Auu____444 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____444 -> FStar_Pprint.document) ->
        'Auu____444 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____474 =
          let uu____475 =
            let uu____476 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____476  in
          separate_map_last uu____475 f l  in
        FStar_Pprint.group uu____474
  
let separate_map_or_flow :
  'Auu____485 .
    FStar_Pprint.document ->
      ('Auu____485 -> FStar_Pprint.document) ->
        'Auu____485 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____519 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____519 -> FStar_Pprint.document) ->
        'Auu____519 Prims.list -> FStar_Pprint.document
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
  'Auu____571 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____571 -> FStar_Pprint.document) ->
        'Auu____571 Prims.list -> FStar_Pprint.document
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
              let uu____641 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____641
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____661 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____661 -> FStar_Pprint.document) ->
                  'Auu____661 Prims.list -> FStar_Pprint.document
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
                    (let uu____714 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____714
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____733 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____733 -> FStar_Pprint.document) ->
                  'Auu____733 Prims.list -> FStar_Pprint.document
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
                    (let uu____786 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____786
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____801  ->
    match uu____801 with
    | (comment,keywords) ->
        let uu____826 =
          let uu____827 =
            let uu____830 = str comment  in
            let uu____831 =
              let uu____834 =
                let uu____837 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____846  ->
                       match uu____846 with
                       | (k,v1) ->
                           let uu____853 =
                             let uu____856 = str k  in
                             let uu____857 =
                               let uu____860 =
                                 let uu____863 = str v1  in [uu____863]  in
                               FStar_Pprint.rarrow :: uu____860  in
                             uu____856 :: uu____857  in
                           FStar_Pprint.concat uu____853) keywords
                   in
                [uu____837]  in
              FStar_Pprint.space :: uu____834  in
            uu____830 :: uu____831  in
          FStar_Pprint.concat uu____827  in
        FStar_Pprint.group uu____826
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____869 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____881 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____881
      | uu____882 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____924::(e2,uu____926)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____949 -> false  in
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
    | FStar_Parser_AST.Construct (uu____967,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____978,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____999 = extract_from_list e2  in e1 :: uu____999
    | uu____1002 ->
        let uu____1003 =
          let uu____1004 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1004  in
        failwith uu____1003
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1013;
           FStar_Parser_AST.level = uu____1014;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1016 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1024;
           FStar_Parser_AST.level = uu____1025;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1027;
                                                         FStar_Parser_AST.level
                                                           = uu____1028;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1030;
                                                    FStar_Parser_AST.level =
                                                      uu____1031;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1033;
                FStar_Parser_AST.level = uu____1034;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1036;
           FStar_Parser_AST.level = uu____1037;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1039 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1049 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1050;
           FStar_Parser_AST.range = uu____1051;
           FStar_Parser_AST.level = uu____1052;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1053;
                                                         FStar_Parser_AST.range
                                                           = uu____1054;
                                                         FStar_Parser_AST.level
                                                           = uu____1055;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1057;
                                                    FStar_Parser_AST.level =
                                                      uu____1058;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1059;
                FStar_Parser_AST.range = uu____1060;
                FStar_Parser_AST.level = uu____1061;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1063;
           FStar_Parser_AST.level = uu____1064;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1066 = extract_from_ref_set e1  in
        let uu____1069 = extract_from_ref_set e2  in
        FStar_List.append uu____1066 uu____1069
    | uu____1072 ->
        let uu____1073 =
          let uu____1074 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1074  in
        failwith uu____1073
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1082 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1082
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1088 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1088
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1095 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1095 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1100 = FStar_Ident.text_of_id op  in uu____1100 <> "~"))
  
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
      | uu____1166 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1182 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1188 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1194 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___92_1214  ->
    match uu___92_1214 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___93_1235  ->
      match uu___93_1235 with
      | FStar_Util.Inl c ->
          let uu____1244 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1244 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1255 .
    Prims.string ->
      ('Auu____1255,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1276  ->
      match uu____1276 with
      | (assoc_levels,tokens) ->
          let uu____1304 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1304 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1331 .
    unit ->
      (associativity,('Auu____1331,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1342  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1359 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1359) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1371  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1407 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1407) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1419  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1448 .
    unit ->
      (associativity,('Auu____1448,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1459  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1476 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1476) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1488  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1517 .
    unit ->
      (associativity,('Auu____1517,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1528  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1545 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1545) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1557  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1579 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1579) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1591  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1627 .
    unit ->
      (associativity,('Auu____1627,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1638  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1655 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1655) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1667  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1689 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1689) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1701  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1723 .
    unit ->
      (associativity,('Auu____1723,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1734  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1751 .
    unit ->
      (associativity,('Auu____1751,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1762  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1779 .
    unit ->
      (associativity,('Auu____1779,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1790  -> (Right, [FStar_Util.Inr "::"]) 
let (level_associativity_spec :
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  [opinfix4 ();
  opinfix3 ();
  opinfix2 ();
  opinfix1 ();
  pipe_right ();
  opinfix0d ();
  opinfix0c ();
  opinfix0b ();
  opinfix0a ();
  colon_equals ();
  amp ();
  colon_colon ()] 
let (level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___94_2001 =
    match uu___94_2001 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2041  ->
         match uu____2041 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2125 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2125 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2175) ->
          assoc_levels
      | uu____2219 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____2260 .
    ('Auu____2260,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2325 =
        FStar_List.tryFind
          (fun uu____2365  ->
             match uu____2365 with
             | (uu____2383,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2325 with
      | FStar_Pervasives_Native.Some ((uu____2425,l1,uu____2427),uu____2428)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2483 =
            let uu____2484 =
              let uu____2485 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2485  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2484
             in
          failwith uu____2483
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2521 = assign_levels level_associativity_spec op  in
    match uu____2521 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2546 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____2546) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2560  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2643 =
      let uu____2657 =
        let uu____2673 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2673  in
      FStar_List.tryFind uu____2657 (operatorInfix0ad12 ())  in
    uu____2643 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2776 =
      let uu____2790 =
        let uu____2806 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2806  in
      FStar_List.tryFind uu____2790 opinfix34  in
    uu____2776 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2862 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2862
    then (Prims.parse_int "1")
    else
      (let uu____2864 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2864
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2873 . FStar_Ident.ident -> 'Auu____2873 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2889 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2889 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2891 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2891
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2892 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2892 [".()<-"; ".[]<-"]
      | uu____2893 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2931 .
    ('Auu____2931 -> FStar_Pprint.document) ->
      'Auu____2931 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2972 = FStar_ST.op_Bang comment_stack  in
          match uu____2972 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____3035 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3035
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3076 =
                    let uu____3077 =
                      let uu____3078 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____3078
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____3077  in
                  comments_before_pos uu____3076 print_pos lookahead_pos))
              else
                (let uu____3080 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3080))
           in
        let uu____3081 =
          let uu____3086 =
            let uu____3087 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3087  in
          let uu____3088 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3086 uu____3088  in
        match uu____3081 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3094 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3094
              else comments  in
            let uu____3100 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____3100
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____3121 = FStar_ST.op_Bang comment_stack  in
          match uu____3121 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____3213 =
                    let uu____3214 =
                      let uu____3215 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____3215  in
                    uu____3214 - lbegin  in
                  max k uu____3213  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____3218 =
                    let uu____3219 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____3220 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____3219 uu____3220  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____3218  in
                let uu____3221 =
                  let uu____3222 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____3222  in
                place_comments_until_pos (Prims.parse_int "1") uu____3221
                  pos_end doc2))
          | uu____3223 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____3232 =
                     let uu____3233 = FStar_Range.line_of_pos pos_end  in
                     uu____3233 - lbegin  in
                   max (Prims.parse_int "1") uu____3232  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____3235 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____3235)
  
let separate_map_with_comments :
  'Auu____3248 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3248 -> FStar_Pprint.document) ->
          'Auu____3248 Prims.list ->
            ('Auu____3248 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3305 x =
              match uu____3305 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3319 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3319 doc1
                     in
                  let uu____3320 =
                    let uu____3321 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3321  in
                  let uu____3322 =
                    let uu____3323 =
                      let uu____3324 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3324  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3323  in
                  (uu____3320, uu____3322)
               in
            let uu____3325 =
              let uu____3332 = FStar_List.hd xs  in
              let uu____3333 = FStar_List.tl xs  in (uu____3332, uu____3333)
               in
            match uu____3325 with
            | (x,xs1) ->
                let init1 =
                  let uu____3349 =
                    let uu____3350 =
                      let uu____3351 = extract_range x  in
                      FStar_Range.end_of_range uu____3351  in
                    FStar_Range.line_of_pos uu____3350  in
                  let uu____3352 =
                    let uu____3353 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3353  in
                  (uu____3349, uu____3352)  in
                let uu____3354 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3354
  
let separate_map_with_comments_kw :
  'Auu____3377 'Auu____3378 .
    'Auu____3377 ->
      'Auu____3377 ->
        ('Auu____3377 -> 'Auu____3378 -> FStar_Pprint.document) ->
          'Auu____3378 Prims.list ->
            ('Auu____3378 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3440 x =
              match uu____3440 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3454 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3454 doc1
                     in
                  let uu____3455 =
                    let uu____3456 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3456  in
                  let uu____3457 =
                    let uu____3458 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3458  in
                  (uu____3455, uu____3457)
               in
            let uu____3459 =
              let uu____3466 = FStar_List.hd xs  in
              let uu____3467 = FStar_List.tl xs  in (uu____3466, uu____3467)
               in
            match uu____3459 with
            | (x,xs1) ->
                let init1 =
                  let uu____3483 =
                    let uu____3484 =
                      let uu____3485 = extract_range x  in
                      FStar_Range.end_of_range uu____3485  in
                    FStar_Range.line_of_pos uu____3484  in
                  let uu____3486 = f prefix1 x  in (uu____3483, uu____3486)
                   in
                let uu____3487 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3487
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4191)) ->
          let uu____4194 =
            let uu____4195 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4195 FStar_Util.is_upper  in
          if uu____4194
          then
            let uu____4196 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4196 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4198 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4203 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____4204 =
      let uu____4205 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4206 =
        let uu____4207 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4207  in
      FStar_Pprint.op_Hat_Hat uu____4205 uu____4206  in
    FStar_Pprint.op_Hat_Hat uu____4203 uu____4204

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4209 ->
        let uu____4210 =
          let uu____4211 = str "@ "  in
          let uu____4212 =
            let uu____4213 =
              let uu____4214 =
                let uu____4215 =
                  let uu____4216 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4216  in
                FStar_Pprint.op_Hat_Hat uu____4215 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4214  in
            FStar_Pprint.op_Hat_Hat uu____4213 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4211 uu____4212  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4210

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4219  ->
    match uu____4219 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4255 =
                match uu____4255 with
                | (kwd,arg) ->
                    let uu____4262 = str "@"  in
                    let uu____4263 =
                      let uu____4264 = str kwd  in
                      let uu____4265 =
                        let uu____4266 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4266
                         in
                      FStar_Pprint.op_Hat_Hat uu____4264 uu____4265  in
                    FStar_Pprint.op_Hat_Hat uu____4262 uu____4263
                 in
              let uu____4267 =
                let uu____4268 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____4268 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4267
           in
        let uu____4273 =
          let uu____4274 =
            let uu____4275 =
              let uu____4276 =
                let uu____4277 = str doc1  in
                let uu____4278 =
                  let uu____4279 =
                    let uu____4280 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4280  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4279  in
                FStar_Pprint.op_Hat_Hat uu____4277 uu____4278  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4276  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4275  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4274  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4273

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4284 =
          let uu____4285 = str "val"  in
          let uu____4286 =
            let uu____4287 =
              let uu____4288 = p_lident lid  in
              let uu____4289 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4288 uu____4289  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4287  in
          FStar_Pprint.op_Hat_Hat uu____4285 uu____4286  in
        let uu____4290 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4284 uu____4290
    | FStar_Parser_AST.TopLevelLet (uu____4291,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4316 =
               let uu____4317 = str "let"  in p_letlhs uu____4317 lb  in
             FStar_Pprint.group uu____4316) lbs
    | uu____4318 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___95_4333 =
          match uu___95_4333 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4341 = f x  in
              let uu____4342 =
                let uu____4343 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4343  in
              FStar_Pprint.op_Hat_Hat uu____4341 uu____4342
           in
        let uu____4344 = str "["  in
        let uu____4345 =
          let uu____4346 = p_list' l  in
          let uu____4347 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4346 uu____4347  in
        FStar_Pprint.op_Hat_Hat uu____4344 uu____4345

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4350 =
          let uu____4351 = str "open"  in
          let uu____4352 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4351 uu____4352  in
        FStar_Pprint.group uu____4350
    | FStar_Parser_AST.Include uid ->
        let uu____4354 =
          let uu____4355 = str "include"  in
          let uu____4356 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4355 uu____4356  in
        FStar_Pprint.group uu____4354
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4359 =
          let uu____4360 = str "module"  in
          let uu____4361 =
            let uu____4362 =
              let uu____4363 = p_uident uid1  in
              let uu____4364 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4363 uu____4364  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4362  in
          FStar_Pprint.op_Hat_Hat uu____4360 uu____4361  in
        let uu____4365 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4359 uu____4365
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4367 =
          let uu____4368 = str "module"  in
          let uu____4369 =
            let uu____4370 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4370  in
          FStar_Pprint.op_Hat_Hat uu____4368 uu____4369  in
        FStar_Pprint.group uu____4367
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____4403 = str "effect"  in
          let uu____4404 =
            let uu____4405 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4405  in
          FStar_Pprint.op_Hat_Hat uu____4403 uu____4404  in
        let uu____4406 =
          let uu____4407 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4407 FStar_Pprint.equals
           in
        let uu____4408 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4406 uu____4408
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____4426 =
          let uu____4427 = str "type"  in
          let uu____4428 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____4427 uu____4428  in
        let uu____4441 =
          let uu____4442 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4480 =
                    let uu____4481 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4481 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4480)) uu____4442
           in
        FStar_Pprint.op_Hat_Hat uu____4426 uu____4441
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4497 = str "let"  in
          let uu____4498 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4497 uu____4498  in
        let uu____4499 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4499 p_letbinding lbs
          (fun uu____4507  ->
             match uu____4507 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4516 = str "val"  in
        let uu____4517 =
          let uu____4518 =
            let uu____4519 = p_lident lid  in
            let uu____4520 =
              let uu____4521 =
                let uu____4522 =
                  let uu____4523 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4523  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4522  in
              FStar_Pprint.group uu____4521  in
            FStar_Pprint.op_Hat_Hat uu____4519 uu____4520  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4518  in
        FStar_Pprint.op_Hat_Hat uu____4516 uu____4517
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4527 =
            let uu____4528 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4528 FStar_Util.is_upper  in
          if uu____4527
          then FStar_Pprint.empty
          else
            (let uu____4530 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4530 FStar_Pprint.space)
           in
        let uu____4531 =
          let uu____4532 = p_ident id1  in
          let uu____4533 =
            let uu____4534 =
              let uu____4535 =
                let uu____4536 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4536  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4535  in
            FStar_Pprint.group uu____4534  in
          FStar_Pprint.op_Hat_Hat uu____4532 uu____4533  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4531
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4543 = str "exception"  in
        let uu____4544 =
          let uu____4545 =
            let uu____4546 = p_uident uid  in
            let uu____4547 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4551 =
                     let uu____4552 = str "of"  in
                     let uu____4553 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4552 uu____4553  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4551) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4546 uu____4547  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4545  in
        FStar_Pprint.op_Hat_Hat uu____4543 uu____4544
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4555 = str "new_effect"  in
        let uu____4556 =
          let uu____4557 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4557  in
        FStar_Pprint.op_Hat_Hat uu____4555 uu____4556
    | FStar_Parser_AST.SubEffect se ->
        let uu____4559 = str "sub_effect"  in
        let uu____4560 =
          let uu____4561 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4561  in
        FStar_Pprint.op_Hat_Hat uu____4559 uu____4560
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4564 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4564 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4565 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4566) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4589 = str "%splice"  in
        let uu____4590 =
          let uu____4591 =
            let uu____4592 = str ";"  in p_list p_uident uu____4592 ids  in
          let uu____4593 =
            let uu____4594 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4594  in
          FStar_Pprint.op_Hat_Hat uu____4591 uu____4593  in
        FStar_Pprint.op_Hat_Hat uu____4589 uu____4590

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___96_4595  ->
    match uu___96_4595 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4597 = str "#set-options"  in
        let uu____4598 =
          let uu____4599 =
            let uu____4600 = str s  in FStar_Pprint.dquotes uu____4600  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4599  in
        FStar_Pprint.op_Hat_Hat uu____4597 uu____4598
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4604 = str "#reset-options"  in
        let uu____4605 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4609 =
                 let uu____4610 = str s  in FStar_Pprint.dquotes uu____4610
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4609) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4604 uu____4605
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
    fun uu____4639  ->
      match uu____4639 with
      | (typedecl,fsdoc_opt) ->
          let uu____4652 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4652 with
           | (decl,body) ->
               let uu____4670 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4670)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___97_4672  ->
      match uu___97_4672 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4702 = FStar_Pprint.empty  in
          let uu____4703 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4703, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4724 =
            let uu____4725 = p_typ false false t  in jump2 uu____4725  in
          let uu____4726 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4726, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4780 =
            match uu____4780 with
            | (lid1,t,doc_opt) ->
                let uu____4796 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4796
             in
          let p_fields uu____4812 =
            let uu____4813 =
              let uu____4814 =
                let uu____4815 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4815 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4814  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4813  in
          let uu____4824 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4824, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4885 =
            match uu____4885 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4911 =
                    let uu____4912 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4912  in
                  FStar_Range.extend_to_end_of_line uu____4911  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4938 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4951 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4951,
            ((fun uu____4957  ->
                let uu____4958 = datacon_doc ()  in jump2 uu____4958)))

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
  fun uu____4959  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4959 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4993 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4993  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4995 =
                        let uu____4998 =
                          let uu____5001 = p_fsdoc fsdoc  in
                          let uu____5002 =
                            let uu____5005 = cont lid_doc  in [uu____5005]
                             in
                          uu____5001 :: uu____5002  in
                        kw :: uu____4998  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4995
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____5010 =
                        let uu____5011 =
                          let uu____5012 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5012 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5011
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5010
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5027 =
                          let uu____5028 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5028  in
                        prefix2 uu____5027 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5030  ->
      match uu____5030 with
      | (lid,t,doc_opt) ->
          let uu____5046 =
            let uu____5047 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5048 =
              let uu____5049 = p_lident lid  in
              let uu____5050 =
                let uu____5051 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5051  in
              FStar_Pprint.op_Hat_Hat uu____5049 uu____5050  in
            FStar_Pprint.op_Hat_Hat uu____5047 uu____5048  in
          FStar_Pprint.group uu____5046

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____5052  ->
    match uu____5052 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5080 =
            let uu____5081 =
              let uu____5082 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5082  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5081  in
          FStar_Pprint.group uu____5080  in
        let uu____5083 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5084 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5088 =
                 let uu____5089 =
                   let uu____5090 =
                     let uu____5091 =
                       let uu____5092 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5092
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5091  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5090  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5089  in
               FStar_Pprint.group uu____5088) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5083 uu____5084

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5094  ->
      match uu____5094 with
      | (pat,uu____5100) ->
          let uu____5101 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5120 =
                  let uu____5121 =
                    let uu____5122 =
                      let uu____5123 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5123
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5122  in
                  FStar_Pprint.group uu____5121  in
                (pat1, uu____5120)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5135 =
                  let uu____5136 =
                    let uu____5137 =
                      let uu____5138 =
                        let uu____5139 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5139
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5138
                       in
                    FStar_Pprint.group uu____5137  in
                  let uu____5140 =
                    let uu____5141 =
                      let uu____5142 = str "by"  in
                      let uu____5143 =
                        let uu____5144 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5144
                         in
                      FStar_Pprint.op_Hat_Hat uu____5142 uu____5143  in
                    FStar_Pprint.group uu____5141  in
                  FStar_Pprint.op_Hat_Hat uu____5136 uu____5140  in
                (pat1, uu____5135)
            | uu____5145 -> (pat, FStar_Pprint.empty)  in
          (match uu____5101 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5149);
                       FStar_Parser_AST.prange = uu____5150;_},pats)
                    ->
                    let uu____5160 =
                      let uu____5161 =
                        let uu____5162 =
                          let uu____5163 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5163  in
                        FStar_Pprint.group uu____5162  in
                      let uu____5164 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5161 uu____5164  in
                    prefix2_nonempty uu____5160 ascr_doc
                | uu____5165 ->
                    let uu____5166 =
                      let uu____5167 =
                        let uu____5168 =
                          let uu____5169 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5169  in
                        FStar_Pprint.group uu____5168  in
                      FStar_Pprint.op_Hat_Hat uu____5167 ascr_doc  in
                    FStar_Pprint.group uu____5166))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5171  ->
      match uu____5171 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____5180 =
            let uu____5181 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5181  in
          let uu____5182 =
            let uu____5183 =
              let uu____5184 =
                let uu____5185 =
                  let uu____5186 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5186  in
                FStar_Pprint.group uu____5185  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5184  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____5183  in
          FStar_Pprint.ifflat uu____5180 uu____5182

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___98_5187  ->
    match uu___98_5187 with
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
        let uu____5212 = p_uident uid  in
        let uu____5213 = p_binders true bs  in
        let uu____5214 =
          let uu____5215 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5215  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5212 uu____5213 uu____5214

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
          let uu____5225 =
            let uu____5226 =
              let uu____5227 =
                let uu____5228 = p_uident uid  in
                let uu____5229 = p_binders true bs  in
                let uu____5230 =
                  let uu____5231 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5231  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5228 uu____5229 uu____5230
                 in
              FStar_Pprint.group uu____5227  in
            let uu____5232 =
              let uu____5233 = str "with"  in
              let uu____5234 =
                let uu____5235 =
                  let uu____5236 =
                    let uu____5237 =
                      let uu____5238 =
                        let uu____5239 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5239
                         in
                      separate_map_last uu____5238 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5237  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5236  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5235  in
              FStar_Pprint.op_Hat_Hat uu____5233 uu____5234  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5226 uu____5232  in
          braces_with_nesting uu____5225

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
          let uu____5270 =
            let uu____5271 = p_lident lid  in
            let uu____5272 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5271 uu____5272  in
          let uu____5273 = p_simpleTerm ps false e  in
          prefix2 uu____5270 uu____5273
      | uu____5274 ->
          let uu____5275 =
            let uu____5276 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5276
             in
          failwith uu____5275

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5338 =
        match uu____5338 with
        | (kwd,t) ->
            let uu____5345 =
              let uu____5346 = str kwd  in
              let uu____5347 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5346 uu____5347  in
            let uu____5348 = p_simpleTerm ps false t  in
            prefix2 uu____5345 uu____5348
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5353 =
      let uu____5354 =
        let uu____5355 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5356 =
          let uu____5357 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5357  in
        FStar_Pprint.op_Hat_Hat uu____5355 uu____5356  in
      let uu____5358 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5354 uu____5358  in
    let uu____5359 =
      let uu____5360 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5360  in
    FStar_Pprint.op_Hat_Hat uu____5353 uu____5359

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___99_5361  ->
    match uu___99_5361 with
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
    | uu____5363 ->
        let uu____5364 =
          let uu____5365 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5365  in
        FStar_Pprint.op_Hat_Hat uu____5364 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___100_5368  ->
    match uu___100_5368 with
    | FStar_Parser_AST.Rec  ->
        let uu____5369 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5369
    | FStar_Parser_AST.Mutable  ->
        let uu____5370 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5370
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___101_5371  ->
    match uu___101_5371 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____5376 =
          let uu____5377 =
            let uu____5378 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____5378  in
          FStar_Pprint.separate_map uu____5377 p_tuplePattern pats  in
        FStar_Pprint.group uu____5376
    | uu____5379 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____5386 =
          let uu____5387 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____5387 p_constructorPattern pats  in
        FStar_Pprint.group uu____5386
    | uu____5388 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____5391;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____5396 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____5397 = p_constructorPattern hd1  in
        let uu____5398 = p_constructorPattern tl1  in
        infix0 uu____5396 uu____5397 uu____5398
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____5400;_},pats)
        ->
        let uu____5406 = p_quident uid  in
        let uu____5407 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5406 uu____5407
    | uu____5408 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5424;
               FStar_Parser_AST.blevel = uu____5425;
               FStar_Parser_AST.aqual = uu____5426;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5432 =
               let uu____5433 = p_ident lid  in
               p_refinement aqual uu____5433 t1 phi  in
             soft_parens_with_nesting uu____5432
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5435;
               FStar_Parser_AST.blevel = uu____5436;
               FStar_Parser_AST.aqual = uu____5437;_},phi))
             ->
             let uu____5439 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____5439
         | uu____5440 ->
             let uu____5445 =
               let uu____5446 = p_tuplePattern pat  in
               let uu____5447 =
                 let uu____5448 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5448
                  in
               FStar_Pprint.op_Hat_Hat uu____5446 uu____5447  in
             soft_parens_with_nesting uu____5445)
    | FStar_Parser_AST.PatList pats ->
        let uu____5452 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5452 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5469 =
          match uu____5469 with
          | (lid,pat) ->
              let uu____5476 = p_qlident lid  in
              let uu____5477 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5476 uu____5477
           in
        let uu____5478 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5478
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5488 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5489 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5490 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5488 uu____5489 uu____5490
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5499 =
          let uu____5500 =
            let uu____5501 =
              let uu____5502 = FStar_Ident.text_of_id op  in str uu____5502
               in
            let uu____5503 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5501 uu____5503  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5500  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5499
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5511 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5512 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5511 uu____5512
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5514 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5517;
           FStar_Parser_AST.prange = uu____5518;_},uu____5519)
        ->
        let uu____5524 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5524
    | FStar_Parser_AST.PatTuple (uu____5525,false ) ->
        let uu____5530 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5530
    | uu____5531 ->
        let uu____5532 =
          let uu____5533 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5533  in
        failwith uu____5532

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5537 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5538 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5537 uu____5538
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5545;
                   FStar_Parser_AST.blevel = uu____5546;
                   FStar_Parser_AST.aqual = uu____5547;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5549 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5549 t1 phi
            | uu____5550 ->
                let uu____5551 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5552 =
                  let uu____5553 = p_lident lid  in
                  let uu____5554 =
                    let uu____5555 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____5555
                     in
                  FStar_Pprint.op_Hat_Hat uu____5553 uu____5554  in
                FStar_Pprint.op_Hat_Hat uu____5551 uu____5552
             in
          if is_atomic
          then
            let uu____5556 =
              let uu____5557 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5557  in
            FStar_Pprint.group uu____5556
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5559 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5566;
                  FStar_Parser_AST.blevel = uu____5567;
                  FStar_Parser_AST.aqual = uu____5568;_},phi)
               ->
               if is_atomic
               then
                 let uu____5570 =
                   let uu____5571 =
                     let uu____5572 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5572 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5571  in
                 FStar_Pprint.group uu____5570
               else
                 (let uu____5574 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5574)
           | uu____5575 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____5584 -> false
            | FStar_Parser_AST.App uu____5595 -> false
            | FStar_Parser_AST.Op uu____5602 -> false
            | uu____5609 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____5613 =
            let uu____5614 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____5615 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____5614 uu____5615  in
          let uu____5616 =
            let uu____5617 = p_appTerm t  in
            let uu____5618 =
              let uu____5619 =
                let uu____5620 =
                  let uu____5621 = soft_braces_with_nesting_tight phi1  in
                  let uu____5622 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____5621 uu____5622  in
                FStar_Pprint.group uu____5620  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____5619
               in
            FStar_Pprint.op_Hat_Hat uu____5617 uu____5618  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5613 uu____5616

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____5633 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____5633

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5638 = FStar_Ident.text_of_id lid  in str uu____5638)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5641 = FStar_Ident.text_of_lid lid  in str uu____5641)

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
            let uu____5659 =
              let uu____5660 =
                let uu____5661 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5661 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5660  in
            let uu____5662 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5659 uu____5662
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5666 =
              let uu____5667 =
                let uu____5668 =
                  let uu____5669 = p_lident x  in
                  let uu____5670 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5669 uu____5670  in
                let uu____5671 =
                  let uu____5672 = p_noSeqTerm true false e1  in
                  let uu____5673 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5672 uu____5673  in
                op_Hat_Slash_Plus_Hat uu____5668 uu____5671  in
              FStar_Pprint.group uu____5667  in
            let uu____5674 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5666 uu____5674
        | uu____5675 ->
            let uu____5676 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5676

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
            let uu____5687 =
              let uu____5688 = p_tmIff e1  in
              let uu____5689 =
                let uu____5690 =
                  let uu____5691 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5691
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5690  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5688 uu____5689  in
            FStar_Pprint.group uu____5687
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5697 =
              let uu____5698 = p_tmIff e1  in
              let uu____5699 =
                let uu____5700 =
                  let uu____5701 =
                    let uu____5702 = p_typ false false t  in
                    let uu____5703 =
                      let uu____5704 = str "by"  in
                      let uu____5705 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5704 uu____5705  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5702 uu____5703  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5701
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5700  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5698 uu____5699  in
            FStar_Pprint.group uu____5697
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5706;_},e1::e2::e3::[])
            ->
            let uu____5712 =
              let uu____5713 =
                let uu____5714 =
                  let uu____5715 = p_atomicTermNotQUident e1  in
                  let uu____5716 =
                    let uu____5717 =
                      let uu____5718 =
                        let uu____5719 = p_term false false e2  in
                        soft_parens_with_nesting uu____5719  in
                      let uu____5720 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5718 uu____5720  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5717  in
                  FStar_Pprint.op_Hat_Hat uu____5715 uu____5716  in
                FStar_Pprint.group uu____5714  in
              let uu____5721 =
                let uu____5722 = p_noSeqTerm ps pb e3  in jump2 uu____5722
                 in
              FStar_Pprint.op_Hat_Hat uu____5713 uu____5721  in
            FStar_Pprint.group uu____5712
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5723;_},e1::e2::e3::[])
            ->
            let uu____5729 =
              let uu____5730 =
                let uu____5731 =
                  let uu____5732 = p_atomicTermNotQUident e1  in
                  let uu____5733 =
                    let uu____5734 =
                      let uu____5735 =
                        let uu____5736 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5736  in
                      let uu____5737 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5735 uu____5737  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5734  in
                  FStar_Pprint.op_Hat_Hat uu____5732 uu____5733  in
                FStar_Pprint.group uu____5731  in
              let uu____5738 =
                let uu____5739 = p_noSeqTerm ps pb e3  in jump2 uu____5739
                 in
              FStar_Pprint.op_Hat_Hat uu____5730 uu____5738  in
            FStar_Pprint.group uu____5729
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5747 =
              let uu____5748 = str "requires"  in
              let uu____5749 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5748 uu____5749  in
            FStar_Pprint.group uu____5747
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5757 =
              let uu____5758 = str "ensures"  in
              let uu____5759 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5758 uu____5759  in
            FStar_Pprint.group uu____5757
        | FStar_Parser_AST.Attributes es ->
            let uu____5763 =
              let uu____5764 = str "attributes"  in
              let uu____5765 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5764 uu____5765  in
            FStar_Pprint.group uu____5763
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5769 =
                let uu____5770 =
                  let uu____5771 = str "if"  in
                  let uu____5772 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5771 uu____5772  in
                let uu____5773 =
                  let uu____5774 = str "then"  in
                  let uu____5775 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5774 uu____5775  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5770 uu____5773  in
              FStar_Pprint.group uu____5769
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5778,uu____5779,e31) when
                     is_unit e31 ->
                     let uu____5781 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5781
                 | uu____5782 -> p_noSeqTerm false false e2  in
               let uu____5783 =
                 let uu____5784 =
                   let uu____5785 = str "if"  in
                   let uu____5786 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5785 uu____5786  in
                 let uu____5787 =
                   let uu____5788 =
                     let uu____5789 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5789 e2_doc  in
                   let uu____5790 =
                     let uu____5791 = str "else"  in
                     let uu____5792 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5791 uu____5792  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5788 uu____5790  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5784 uu____5787  in
               FStar_Pprint.group uu____5783)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5815 =
              let uu____5816 =
                let uu____5817 =
                  let uu____5818 = str "try"  in
                  let uu____5819 = p_noSeqTerm false false e1  in
                  prefix2 uu____5818 uu____5819  in
                let uu____5820 =
                  let uu____5821 = str "with"  in
                  let uu____5822 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5821 uu____5822  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5817 uu____5820  in
              FStar_Pprint.group uu____5816  in
            let uu____5831 = paren_if (ps || pb)  in uu____5831 uu____5815
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5858 =
              let uu____5859 =
                let uu____5860 =
                  let uu____5861 = str "match"  in
                  let uu____5862 = p_noSeqTerm false false e1  in
                  let uu____5863 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5861 uu____5862 uu____5863
                   in
                let uu____5864 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5860 uu____5864  in
              FStar_Pprint.group uu____5859  in
            let uu____5873 = paren_if (ps || pb)  in uu____5873 uu____5858
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5880 =
              let uu____5881 =
                let uu____5882 =
                  let uu____5883 = str "let open"  in
                  let uu____5884 = p_quident uid  in
                  let uu____5885 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5883 uu____5884 uu____5885
                   in
                let uu____5886 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5882 uu____5886  in
              FStar_Pprint.group uu____5881  in
            let uu____5887 = paren_if ps  in uu____5887 uu____5880
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5951 is_last =
              match uu____5951 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5984 =
                          let uu____5985 = str "let"  in
                          let uu____5986 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5985 uu____5986
                           in
                        FStar_Pprint.group uu____5984
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5987 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5992 =
                    if is_last
                    then
                      let uu____5993 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5994 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5993 doc_expr uu____5994
                    else
                      (let uu____5996 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5996)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5992
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6042 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6042
                     else
                       (let uu____6050 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6050)) lbs
               in
            let lbs_doc =
              let uu____6058 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6058  in
            let uu____6059 =
              let uu____6060 =
                let uu____6061 =
                  let uu____6062 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6062
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6061  in
              FStar_Pprint.group uu____6060  in
            let uu____6063 = paren_if ps  in uu____6063 uu____6059
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6070;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6073;
                                                             FStar_Parser_AST.level
                                                               = uu____6074;_})
            when matches_var maybe_x x ->
            let uu____6101 =
              let uu____6102 =
                let uu____6103 = str "function"  in
                let uu____6104 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6103 uu____6104  in
              FStar_Pprint.group uu____6102  in
            let uu____6113 = paren_if (ps || pb)  in uu____6113 uu____6101
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____6119 =
              let uu____6120 = str "quote"  in
              let uu____6121 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6120 uu____6121  in
            FStar_Pprint.group uu____6119
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____6123 =
              let uu____6124 = str "`"  in
              let uu____6125 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6124 uu____6125  in
            FStar_Pprint.group uu____6123
        | FStar_Parser_AST.VQuote e1 ->
            let uu____6127 =
              let uu____6128 = str "%`"  in
              let uu____6129 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6128 uu____6129  in
            FStar_Pprint.group uu____6127
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____6131 =
              let uu____6132 = str "`#"  in
              let uu____6133 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6132 uu____6133  in
            FStar_Pprint.group uu____6131
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____6135 =
              let uu____6136 = str "`@"  in
              let uu____6137 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6136 uu____6137  in
            FStar_Pprint.group uu____6135
        | uu____6138 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___102_6139  ->
    match uu___102_6139 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6151 =
          let uu____6152 = str "[@"  in
          let uu____6153 =
            let uu____6154 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____6155 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6154 uu____6155  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6152 uu____6153  in
        FStar_Pprint.group uu____6151

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
                 let uu____6181 =
                   let uu____6182 =
                     let uu____6183 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6183 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6182 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6181 term_doc
             | pats ->
                 let uu____6189 =
                   let uu____6190 =
                     let uu____6191 =
                       let uu____6192 =
                         let uu____6193 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6193
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6192 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6194 = p_trigger trigger  in
                     prefix2 uu____6191 uu____6194  in
                   FStar_Pprint.group uu____6190  in
                 prefix2 uu____6189 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6214 =
                   let uu____6215 =
                     let uu____6216 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6216 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6215 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6214 term_doc
             | pats ->
                 let uu____6222 =
                   let uu____6223 =
                     let uu____6224 =
                       let uu____6225 =
                         let uu____6226 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6226
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6225 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6227 = p_trigger trigger  in
                     prefix2 uu____6224 uu____6227  in
                   FStar_Pprint.group uu____6223  in
                 prefix2 uu____6222 term_doc)
        | uu____6228 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6230 -> str "forall"
    | FStar_Parser_AST.QExists uu____6243 -> str "exists"
    | uu____6256 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___103_6257  ->
    match uu___103_6257 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6269 =
          let uu____6270 =
            let uu____6271 =
              let uu____6272 = str "pattern"  in
              let uu____6273 =
                let uu____6274 =
                  let uu____6275 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____6275
                   in
                FStar_Pprint.op_Hat_Hat uu____6274 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6272 uu____6273  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6271  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6270  in
        FStar_Pprint.group uu____6269

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6281 = str "\\/"  in
    FStar_Pprint.separate_map uu____6281 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6287 =
      let uu____6288 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____6288 p_appTerm pats  in
    FStar_Pprint.group uu____6287

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____6298 =
              let uu____6299 =
                let uu____6300 = str "fun"  in
                let uu____6301 =
                  let uu____6302 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6302
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____6300 uu____6301  in
              let uu____6303 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____6299 uu____6303  in
            let uu____6304 = paren_if ps  in uu____6304 uu____6298
        | uu____6309 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____6313  ->
      match uu____6313 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____6336 =
                    let uu____6337 =
                      let uu____6338 =
                        let uu____6339 = p_tuplePattern p  in
                        let uu____6340 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____6339 uu____6340  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6338
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6337  in
                  FStar_Pprint.group uu____6336
              | FStar_Pervasives_Native.Some f ->
                  let uu____6342 =
                    let uu____6343 =
                      let uu____6344 =
                        let uu____6345 =
                          let uu____6346 =
                            let uu____6347 = p_tuplePattern p  in
                            let uu____6348 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6347
                              uu____6348
                             in
                          FStar_Pprint.group uu____6346  in
                        let uu____6349 =
                          let uu____6350 =
                            let uu____6353 = p_tmFormula f  in
                            [uu____6353; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____6350  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6345 uu____6349
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6344
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6343  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____6342
               in
            let uu____6354 =
              let uu____6355 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____6355  in
            FStar_Pprint.group uu____6354  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____6364 =
                      let uu____6365 =
                        let uu____6366 =
                          let uu____6367 =
                            let uu____6368 =
                              let uu____6369 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____6369  in
                            FStar_Pprint.separate_map uu____6368
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6367
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6366
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6365  in
                    FStar_Pprint.group uu____6364
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6370 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____6372;_},e1::e2::[])
        ->
        let uu____6377 = str "<==>"  in
        let uu____6378 = p_tmImplies e1  in
        let uu____6379 = p_tmIff e2  in
        infix0 uu____6377 uu____6378 uu____6379
    | uu____6380 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____6382;_},e1::e2::[])
        ->
        let uu____6387 = str "==>"  in
        let uu____6388 = p_tmArrow p_tmFormula e1  in
        let uu____6389 = p_tmImplies e2  in
        infix0 uu____6387 uu____6388 uu____6389
    | uu____6390 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____6398 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____6398 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____6419 ->
               let uu____6420 =
                 let uu____6421 =
                   let uu____6422 =
                     let uu____6423 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6423
                      in
                   FStar_Pprint.separate uu____6422 terms  in
                 let uu____6424 =
                   let uu____6425 =
                     let uu____6426 =
                       let uu____6427 =
                         let uu____6428 =
                           let uu____6429 =
                             let uu____6430 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____6430
                              in
                           FStar_Pprint.separate uu____6429 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____6428 last_op  in
                       let uu____6431 =
                         let uu____6432 =
                           let uu____6433 =
                             let uu____6434 =
                               let uu____6435 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6435
                                in
                             FStar_Pprint.separate uu____6434 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____6433 last_op  in
                         jump2 uu____6432  in
                       FStar_Pprint.ifflat uu____6427 uu____6431  in
                     FStar_Pprint.group uu____6426  in
                   let uu____6436 = FStar_List.hd last1  in
                   prefix2 uu____6425 uu____6436  in
                 FStar_Pprint.ifflat uu____6421 uu____6424  in
               FStar_Pprint.group uu____6420)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____6449 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____6454 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____6449 uu____6454
      | uu____6457 -> let uu____6458 = p_Tm e  in [uu____6458]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____6461 =
        let uu____6462 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____6462 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6461  in
    let disj =
      let uu____6464 =
        let uu____6465 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____6465 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6464  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6484;_},e1::e2::[])
        ->
        let uu____6489 = p_tmDisjunction e1  in
        let uu____6494 = let uu____6499 = p_tmConjunction e2  in [uu____6499]
           in
        FStar_List.append uu____6489 uu____6494
    | uu____6508 -> let uu____6509 = p_tmConjunction e  in [uu____6509]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6519;_},e1::e2::[])
        ->
        let uu____6524 = p_tmConjunction e1  in
        let uu____6527 = let uu____6530 = p_tmTuple e2  in [uu____6530]  in
        FStar_List.append uu____6524 uu____6527
    | uu____6531 -> let uu____6532 = p_tmTuple e  in [uu____6532]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____6549 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____6549
          (fun uu____6557  ->
             match uu____6557 with | (e1,uu____6563) -> p_tmEq e1) args
    | uu____6564 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____6569 =
             let uu____6570 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6570  in
           FStar_Pprint.group uu____6569)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals (); pipe_right ()]
             (operatorInfix0ad12 ()))
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
               (let uu____6633 = FStar_Ident.text_of_id op  in
                uu____6633 = "="))
              ||
              (let uu____6635 = FStar_Ident.text_of_id op  in
               uu____6635 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6637 = levels op1  in
            (match uu____6637 with
             | (left1,mine,right1) ->
                 let uu____6647 =
                   let uu____6648 = FStar_All.pipe_left str op1  in
                   let uu____6649 = p_tmEqWith' p_X left1 e1  in
                   let uu____6650 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6648 uu____6649 uu____6650  in
                 paren_if_gt curr mine uu____6647)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6651;_},e1::e2::[])
            ->
            let uu____6656 =
              let uu____6657 = p_tmEqWith p_X e1  in
              let uu____6658 =
                let uu____6659 =
                  let uu____6660 =
                    let uu____6661 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6661  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6660  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6659  in
              FStar_Pprint.op_Hat_Hat uu____6657 uu____6658  in
            FStar_Pprint.group uu____6656
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6662;_},e1::[])
            ->
            let uu____6666 = levels "-"  in
            (match uu____6666 with
             | (left1,mine,right1) ->
                 let uu____6676 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6676)
        | uu____6677 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]
         in
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
              (lid,(e1,uu____6749)::(e2,uu____6751)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6771 = is_list e  in Prims.op_Negation uu____6771)
              ->
              let op = "::"  in
              let uu____6773 = levels op  in
              (match uu____6773 with
               | (left1,mine,right1) ->
                   let uu____6783 =
                     let uu____6784 = str op  in
                     let uu____6785 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6786 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6784 uu____6785 uu____6786  in
                   paren_if_gt curr mine uu____6783)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6794 = levels op  in
              (match uu____6794 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6810 = p_binder false b  in
                     let uu____6811 =
                       let uu____6812 =
                         let uu____6813 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6813 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6812
                        in
                     FStar_Pprint.op_Hat_Hat uu____6810 uu____6811  in
                   let uu____6814 =
                     let uu____6815 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6816 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6815 uu____6816  in
                   paren_if_gt curr mine uu____6814)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6817;_},e1::e2::[])
              ->
              let op = "*"  in
              let uu____6823 = levels op  in
              (match uu____6823 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6833 = str op  in
                     let uu____6834 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6835 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6833 uu____6834 uu____6835
                   else
                     (let uu____6836 =
                        let uu____6837 = str op  in
                        let uu____6838 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6839 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6837 uu____6838 uu____6839  in
                      paren_if_gt curr mine uu____6836))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6846 = levels op1  in
              (match uu____6846 with
               | (left1,mine,right1) ->
                   let uu____6856 =
                     let uu____6857 = str op1  in
                     let uu____6858 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6859 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6857 uu____6858 uu____6859  in
                   paren_if_gt curr mine uu____6856)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6878 =
                let uu____6879 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6880 =
                  let uu____6881 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6881 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6879 uu____6880  in
              braces_with_nesting uu____6878
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6886;_},e1::[])
              ->
              let uu____6890 =
                let uu____6891 = str "~"  in
                let uu____6892 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6891 uu____6892  in
              FStar_Pprint.group uu____6890
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6894;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6900 = levels op  in
                   (match uu____6900 with
                    | (left1,mine,right1) ->
                        let uu____6910 =
                          let uu____6911 = str op  in
                          let uu____6912 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6913 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6911 uu____6912 uu____6913  in
                        paren_if_gt curr mine uu____6910)
               | uu____6914 -> p_X e)
          | uu____6915 -> p_X e

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
        let uu____6922 =
          let uu____6923 = p_lident lid  in
          let uu____6924 =
            let uu____6925 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6925  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6923 uu____6924  in
        FStar_Pprint.group uu____6922
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6928 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6930 = p_appTerm e  in
    let uu____6931 =
      let uu____6932 =
        let uu____6933 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6933 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6932  in
    FStar_Pprint.op_Hat_Hat uu____6930 uu____6931

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6938 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6938 t phi
      | FStar_Parser_AST.TAnnotated uu____6939 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6944 ->
          let uu____6945 =
            let uu____6946 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6946
             in
          failwith uu____6945
      | FStar_Parser_AST.TVariable uu____6947 ->
          let uu____6948 =
            let uu____6949 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6949
             in
          failwith uu____6948
      | FStar_Parser_AST.NoName uu____6950 ->
          let uu____6951 =
            let uu____6952 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6952
             in
          failwith uu____6951

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6954  ->
      match uu____6954 with
      | (lid,e) ->
          let uu____6961 =
            let uu____6962 = p_qlident lid  in
            let uu____6963 =
              let uu____6964 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6964
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6962 uu____6963  in
          FStar_Pprint.group uu____6961

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6966 when is_general_application e ->
        let uu____6973 = head_and_args e  in
        (match uu____6973 with
         | (head1,args) ->
             let uu____6998 =
               let uu____7009 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____7009
               then
                 let uu____7043 =
                   FStar_Util.take
                     (fun uu____7067  ->
                        match uu____7067 with
                        | (uu____7072,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____7043 with
                 | (fs_typ_args,args1) ->
                     let uu____7110 =
                       let uu____7111 = p_indexingTerm head1  in
                       let uu____7112 =
                         let uu____7113 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____7113 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____7111 uu____7112  in
                     (uu____7110, args1)
               else
                 (let uu____7125 = p_indexingTerm head1  in
                  (uu____7125, args))
                in
             (match uu____6998 with
              | (head_doc,args1) ->
                  let uu____7146 =
                    let uu____7147 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____7147 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____7146))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____7167 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____7167)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____7185 =
               let uu____7186 = p_quident lid  in
               let uu____7187 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____7186 uu____7187  in
             FStar_Pprint.group uu____7185
         | hd1::tl1 ->
             let uu____7204 =
               let uu____7205 =
                 let uu____7206 =
                   let uu____7207 = p_quident lid  in
                   let uu____7208 = p_argTerm hd1  in
                   prefix2 uu____7207 uu____7208  in
                 FStar_Pprint.group uu____7206  in
               let uu____7209 =
                 let uu____7210 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____7210  in
               FStar_Pprint.op_Hat_Hat uu____7205 uu____7209  in
             FStar_Pprint.group uu____7204)
    | uu____7215 -> p_indexingTerm e

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
         (let uu____7224 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____7224 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____7226 = str "#"  in
        let uu____7227 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____7226 uu____7227
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____7229  ->
    match uu____7229 with | (e,uu____7235) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____7240;_},e1::e2::[])
          ->
          let uu____7245 =
            let uu____7246 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7247 =
              let uu____7248 =
                let uu____7249 = p_term false false e2  in
                soft_parens_with_nesting uu____7249  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7248  in
            FStar_Pprint.op_Hat_Hat uu____7246 uu____7247  in
          FStar_Pprint.group uu____7245
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____7250;_},e1::e2::[])
          ->
          let uu____7255 =
            let uu____7256 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7257 =
              let uu____7258 =
                let uu____7259 = p_term false false e2  in
                soft_brackets_with_nesting uu____7259  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7258  in
            FStar_Pprint.op_Hat_Hat uu____7256 uu____7257  in
          FStar_Pprint.group uu____7255
      | uu____7260 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____7265 = p_quident lid  in
        let uu____7266 =
          let uu____7267 =
            let uu____7268 = p_term false false e1  in
            soft_parens_with_nesting uu____7268  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7267  in
        FStar_Pprint.op_Hat_Hat uu____7265 uu____7266
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7274 =
          let uu____7275 = FStar_Ident.text_of_id op  in str uu____7275  in
        let uu____7276 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____7274 uu____7276
    | uu____7277 -> p_atomicTermNotQUident e

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
         | uu____7284 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7291 =
          let uu____7292 = FStar_Ident.text_of_id op  in str uu____7292  in
        let uu____7293 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____7291 uu____7293
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____7297 =
          let uu____7298 =
            let uu____7299 =
              let uu____7300 = FStar_Ident.text_of_id op  in str uu____7300
               in
            let uu____7301 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____7299 uu____7301  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7298  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7297
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____7316 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____7317 =
          let uu____7318 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____7319 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____7318 p_tmEq uu____7319  in
        let uu____7326 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7316 uu____7317 uu____7326
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____7329 =
          let uu____7330 = p_atomicTermNotQUident e1  in
          let uu____7331 =
            let uu____7332 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7332  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____7330 uu____7331
           in
        FStar_Pprint.group uu____7329
    | uu____7333 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____7338 = p_quident constr_lid  in
        let uu____7339 =
          let uu____7340 =
            let uu____7341 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7341  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7340  in
        FStar_Pprint.op_Hat_Hat uu____7338 uu____7339
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____7343 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____7343 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____7345 = p_term false false e1  in
        soft_parens_with_nesting uu____7345
    | uu____7346 when is_array e ->
        let es = extract_from_list e  in
        let uu____7350 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____7351 =
          let uu____7352 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____7352
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____7355 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7350 uu____7351 uu____7355
    | uu____7356 when is_list e ->
        let uu____7357 =
          let uu____7358 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7359 = extract_from_list e  in
          separate_map_or_flow_last uu____7358
            (fun ps  -> p_noSeqTerm ps false) uu____7359
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____7357 FStar_Pprint.rbracket
    | uu____7364 when is_lex_list e ->
        let uu____7365 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____7366 =
          let uu____7367 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7368 = extract_from_list e  in
          separate_map_or_flow_last uu____7367
            (fun ps  -> p_noSeqTerm ps false) uu____7368
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7365 uu____7366 FStar_Pprint.rbracket
    | uu____7373 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____7377 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____7378 =
          let uu____7379 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____7379 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7377 uu____7378 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____7383 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____7384 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____7383 uu____7384
    | FStar_Parser_AST.Op (op,args) when
        let uu____7391 = handleable_op op args  in
        Prims.op_Negation uu____7391 ->
        let uu____7392 =
          let uu____7393 =
            let uu____7394 = FStar_Ident.text_of_id op  in
            let uu____7395 =
              let uu____7396 =
                let uu____7397 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____7397
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____7396  in
            Prims.strcat uu____7394 uu____7395  in
          Prims.strcat "Operation " uu____7393  in
        failwith uu____7392
    | FStar_Parser_AST.Uvar uu____7398 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____7399 = p_term false false e  in
        soft_parens_with_nesting uu____7399
    | FStar_Parser_AST.Const uu____7400 ->
        let uu____7401 = p_term false false e  in
        soft_parens_with_nesting uu____7401
    | FStar_Parser_AST.Op uu____7402 ->
        let uu____7409 = p_term false false e  in
        soft_parens_with_nesting uu____7409
    | FStar_Parser_AST.Tvar uu____7410 ->
        let uu____7411 = p_term false false e  in
        soft_parens_with_nesting uu____7411
    | FStar_Parser_AST.Var uu____7412 ->
        let uu____7413 = p_term false false e  in
        soft_parens_with_nesting uu____7413
    | FStar_Parser_AST.Name uu____7414 ->
        let uu____7415 = p_term false false e  in
        soft_parens_with_nesting uu____7415
    | FStar_Parser_AST.Construct uu____7416 ->
        let uu____7427 = p_term false false e  in
        soft_parens_with_nesting uu____7427
    | FStar_Parser_AST.Abs uu____7428 ->
        let uu____7435 = p_term false false e  in
        soft_parens_with_nesting uu____7435
    | FStar_Parser_AST.App uu____7436 ->
        let uu____7443 = p_term false false e  in
        soft_parens_with_nesting uu____7443
    | FStar_Parser_AST.Let uu____7444 ->
        let uu____7465 = p_term false false e  in
        soft_parens_with_nesting uu____7465
    | FStar_Parser_AST.LetOpen uu____7466 ->
        let uu____7471 = p_term false false e  in
        soft_parens_with_nesting uu____7471
    | FStar_Parser_AST.Seq uu____7472 ->
        let uu____7477 = p_term false false e  in
        soft_parens_with_nesting uu____7477
    | FStar_Parser_AST.Bind uu____7478 ->
        let uu____7485 = p_term false false e  in
        soft_parens_with_nesting uu____7485
    | FStar_Parser_AST.If uu____7486 ->
        let uu____7493 = p_term false false e  in
        soft_parens_with_nesting uu____7493
    | FStar_Parser_AST.Match uu____7494 ->
        let uu____7509 = p_term false false e  in
        soft_parens_with_nesting uu____7509
    | FStar_Parser_AST.TryWith uu____7510 ->
        let uu____7525 = p_term false false e  in
        soft_parens_with_nesting uu____7525
    | FStar_Parser_AST.Ascribed uu____7526 ->
        let uu____7535 = p_term false false e  in
        soft_parens_with_nesting uu____7535
    | FStar_Parser_AST.Record uu____7536 ->
        let uu____7549 = p_term false false e  in
        soft_parens_with_nesting uu____7549
    | FStar_Parser_AST.Project uu____7550 ->
        let uu____7555 = p_term false false e  in
        soft_parens_with_nesting uu____7555
    | FStar_Parser_AST.Product uu____7556 ->
        let uu____7563 = p_term false false e  in
        soft_parens_with_nesting uu____7563
    | FStar_Parser_AST.Sum uu____7564 ->
        let uu____7571 = p_term false false e  in
        soft_parens_with_nesting uu____7571
    | FStar_Parser_AST.QForall uu____7572 ->
        let uu____7585 = p_term false false e  in
        soft_parens_with_nesting uu____7585
    | FStar_Parser_AST.QExists uu____7586 ->
        let uu____7599 = p_term false false e  in
        soft_parens_with_nesting uu____7599
    | FStar_Parser_AST.Refine uu____7600 ->
        let uu____7605 = p_term false false e  in
        soft_parens_with_nesting uu____7605
    | FStar_Parser_AST.NamedTyp uu____7606 ->
        let uu____7611 = p_term false false e  in
        soft_parens_with_nesting uu____7611
    | FStar_Parser_AST.Requires uu____7612 ->
        let uu____7619 = p_term false false e  in
        soft_parens_with_nesting uu____7619
    | FStar_Parser_AST.Ensures uu____7620 ->
        let uu____7627 = p_term false false e  in
        soft_parens_with_nesting uu____7627
    | FStar_Parser_AST.Attributes uu____7628 ->
        let uu____7631 = p_term false false e  in
        soft_parens_with_nesting uu____7631
    | FStar_Parser_AST.Quote uu____7632 ->
        let uu____7637 = p_term false false e  in
        soft_parens_with_nesting uu____7637
    | FStar_Parser_AST.VQuote uu____7638 ->
        let uu____7639 = p_term false false e  in
        soft_parens_with_nesting uu____7639
    | FStar_Parser_AST.Antiquote uu____7640 ->
        let uu____7645 = p_term false false e  in
        soft_parens_with_nesting uu____7645

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___106_7646  ->
    match uu___106_7646 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____7651) ->
        let uu____7652 = str s  in FStar_Pprint.dquotes uu____7652
    | FStar_Const.Const_bytearray (bytes,uu____7654) ->
        let uu____7659 =
          let uu____7660 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____7660  in
        let uu____7661 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____7659 uu____7661
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_7681 =
          match uu___104_7681 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___105_7687 =
          match uu___105_7687 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7698  ->
               match uu____7698 with
               | (s,w) ->
                   let uu____7705 = signedness s  in
                   let uu____7706 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7705 uu____7706)
            sign_width_opt
           in
        let uu____7707 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7707 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7709 = FStar_Range.string_of_range r  in str uu____7709
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7711 = p_quident lid  in
        let uu____7712 =
          let uu____7713 =
            let uu____7714 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7714  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7713  in
        FStar_Pprint.op_Hat_Hat uu____7711 uu____7712

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7716 = str "u#"  in
    let uu____7717 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7716 uu____7717

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7719;_},u1::u2::[])
        ->
        let uu____7724 =
          let uu____7725 = p_universeFrom u1  in
          let uu____7726 =
            let uu____7727 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7727  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7725 uu____7726  in
        FStar_Pprint.group uu____7724
    | FStar_Parser_AST.App uu____7728 ->
        let uu____7735 = head_and_args u  in
        (match uu____7735 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7761 =
                    let uu____7762 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7763 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7771  ->
                           match uu____7771 with
                           | (u1,uu____7777) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7762 uu____7763  in
                  FStar_Pprint.group uu____7761
              | uu____7778 ->
                  let uu____7779 =
                    let uu____7780 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7780
                     in
                  failwith uu____7779))
    | uu____7781 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7804 = FStar_Ident.text_of_id id1  in str uu____7804
    | FStar_Parser_AST.Paren u1 ->
        let uu____7806 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7806
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7807;_},uu____7808::uu____7809::[])
        ->
        let uu____7812 = p_universeFrom u  in
        soft_parens_with_nesting uu____7812
    | FStar_Parser_AST.App uu____7813 ->
        let uu____7820 = p_universeFrom u  in
        soft_parens_with_nesting uu____7820
    | uu____7821 ->
        let uu____7822 =
          let uu____7823 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7823
           in
        failwith uu____7822

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_term false false e 
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
       | FStar_Parser_AST.Module (uu____7879,decls) ->
           let uu____7885 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7885
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7894,decls,uu____7896) ->
           let uu____7901 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7901
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7958  ->
         match uu____7958 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____8002,decls) -> decls
        | FStar_Parser_AST.Interface (uu____8008,decls,uu____8010) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____8059 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____8072;
                 FStar_Parser_AST.doc = uu____8073;
                 FStar_Parser_AST.quals = uu____8074;
                 FStar_Parser_AST.attrs = uu____8075;_}::uu____8076 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____8082 =
                   let uu____8085 =
                     let uu____8088 = FStar_List.tl ds  in d :: uu____8088
                      in
                   d0 :: uu____8085  in
                 (uu____8082, (d0.FStar_Parser_AST.drange))
             | uu____8093 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____8059 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____8157 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____8157 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____8265 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____8265, comments1))))))
  