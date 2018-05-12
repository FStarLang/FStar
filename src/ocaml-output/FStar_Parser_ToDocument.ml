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
  'Auu____147 'Auu____148 .
    'Auu____147 ->
      ('Auu____148 -> 'Auu____147) ->
        'Auu____148 FStar_Pervasives_Native.option -> 'Auu____147
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
  'Auu____242 .
    FStar_Pprint.document ->
      ('Auu____242 -> FStar_Pprint.document) ->
        'Auu____242 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____267 =
          let uu____268 =
            let uu____269 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____269  in
          FStar_Pprint.separate_map uu____268 f l  in
        FStar_Pprint.group uu____267
  
let precede_break_separate_map :
  'Auu____280 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____280 -> FStar_Pprint.document) ->
          'Auu____280 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____310 =
            let uu____311 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____312 =
              let uu____313 = FStar_List.hd l  in
              FStar_All.pipe_right uu____313 f  in
            FStar_Pprint.precede uu____311 uu____312  in
          let uu____314 =
            let uu____315 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____321 =
                   let uu____322 =
                     let uu____323 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____323  in
                   FStar_Pprint.op_Hat_Hat sep uu____322  in
                 FStar_Pprint.op_Hat_Hat break1 uu____321) uu____315
             in
          FStar_Pprint.op_Hat_Hat uu____310 uu____314
  
let concat_break_map :
  'Auu____330 .
    ('Auu____330 -> FStar_Pprint.document) ->
      'Auu____330 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____350 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____354 = f x  in FStar_Pprint.op_Hat_Hat uu____354 break1)
          l
         in
      FStar_Pprint.group uu____350
  
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
    let uu____395 = str "begin"  in
    let uu____396 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____395 contents uu____396
  
let separate_map_last :
  'Auu____405 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____405 -> FStar_Pprint.document) ->
        'Auu____405 Prims.list -> FStar_Pprint.document
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
  'Auu____457 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____457 -> FStar_Pprint.document) ->
        'Auu____457 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____487 =
          let uu____488 =
            let uu____489 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____489  in
          separate_map_last uu____488 f l  in
        FStar_Pprint.group uu____487
  
let separate_map_or_flow :
  'Auu____498 .
    FStar_Pprint.document ->
      ('Auu____498 -> FStar_Pprint.document) ->
        'Auu____498 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____532 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____532 -> FStar_Pprint.document) ->
        'Auu____532 Prims.list -> FStar_Pprint.document
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
  'Auu____584 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____584 -> FStar_Pprint.document) ->
        'Auu____584 Prims.list -> FStar_Pprint.document
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
              let uu____654 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____654
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____674 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____674 -> FStar_Pprint.document) ->
                  'Auu____674 Prims.list -> FStar_Pprint.document
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
                    (let uu____727 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____727
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____746 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____746 -> FStar_Pprint.document) ->
                  'Auu____746 Prims.list -> FStar_Pprint.document
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
                    (let uu____799 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____799
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____814  ->
    match uu____814 with
    | (comment,keywords) ->
        let uu____839 =
          let uu____840 =
            let uu____843 = str comment  in
            let uu____844 =
              let uu____847 =
                let uu____850 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____859  ->
                       match uu____859 with
                       | (k,v1) ->
                           let uu____866 =
                             let uu____869 = str k  in
                             let uu____870 =
                               let uu____873 =
                                 let uu____876 = str v1  in [uu____876]  in
                               FStar_Pprint.rarrow :: uu____873  in
                             uu____869 :: uu____870  in
                           FStar_Pprint.concat uu____866) keywords
                   in
                [uu____850]  in
              FStar_Pprint.space :: uu____847  in
            uu____843 :: uu____844  in
          FStar_Pprint.concat uu____840  in
        FStar_Pprint.group uu____839
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____882 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____894 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____894
      | uu____895 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____937::(e2,uu____939)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____962 -> false  in
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
    | FStar_Parser_AST.Construct (uu____980,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____991,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____1012 = extract_from_list e2  in e1 :: uu____1012
    | uu____1015 ->
        let uu____1016 =
          let uu____1017 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1017  in
        failwith uu____1016
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1026;
           FStar_Parser_AST.level = uu____1027;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1029 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1037;
           FStar_Parser_AST.level = uu____1038;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1040;
                                                         FStar_Parser_AST.level
                                                           = uu____1041;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1043;
                                                    FStar_Parser_AST.level =
                                                      uu____1044;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1046;
                FStar_Parser_AST.level = uu____1047;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1049;
           FStar_Parser_AST.level = uu____1050;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1052 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1062 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1063;
           FStar_Parser_AST.range = uu____1064;
           FStar_Parser_AST.level = uu____1065;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1066;
                                                         FStar_Parser_AST.range
                                                           = uu____1067;
                                                         FStar_Parser_AST.level
                                                           = uu____1068;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1070;
                                                    FStar_Parser_AST.level =
                                                      uu____1071;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1072;
                FStar_Parser_AST.range = uu____1073;
                FStar_Parser_AST.level = uu____1074;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1076;
           FStar_Parser_AST.level = uu____1077;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1079 = extract_from_ref_set e1  in
        let uu____1082 = extract_from_ref_set e2  in
        FStar_List.append uu____1079 uu____1082
    | uu____1085 ->
        let uu____1086 =
          let uu____1087 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1087  in
        failwith uu____1086
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1095 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1095
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1101 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1101
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1109 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1109 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1117 = FStar_Ident.text_of_id op  in uu____1117 <> "~"))
  
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
      | uu____1183 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1199 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1205 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1211 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___80_1232  ->
    match uu___80_1232 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___81_1257  ->
      match uu___81_1257 with
      | FStar_Util.Inl c ->
          let uu____1266 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1266 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1277 .
    Prims.string ->
      ('Auu____1277,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1298  ->
      match uu____1298 with
      | (assoc_levels,tokens) ->
          let uu____1326 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1326 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___82_1444 =
    match uu___82_1444 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1474  ->
         match uu____1474 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1533 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1533 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1573) ->
          assoc_levels
      | uu____1602 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1638 .
    ('Auu____1638,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1683 =
        FStar_List.tryFind
          (fun uu____1713  ->
             match uu____1713 with
             | (uu____1726,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1683 with
      | FStar_Pervasives_Native.Some ((uu____1748,l1,uu____1750),uu____1751)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1786 =
            let uu____1787 =
              let uu____1788 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1788  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1787
             in
          failwith uu____1786
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1810 = assign_levels level_associativity_spec op  in
    match uu____1810 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1840 =
      let uu____1843 =
        let uu____1848 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1848  in
      FStar_List.tryFind uu____1843 operatorInfix0ad12  in
    uu____1840 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1906 =
      let uu____1920 =
        let uu____1936 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1936  in
      FStar_List.tryFind uu____1920 opinfix34  in
    uu____1906 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1992 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1992
    then (Prims.parse_int "1")
    else
      (let uu____1994 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1994
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2003 . FStar_Ident.ident -> 'Auu____2003 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2019 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2019 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2021 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2021
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2022 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2022 [".()<-"; ".[]<-"]
      | uu____2023 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2061 .
    ('Auu____2061 -> FStar_Pprint.document) ->
      'Auu____2061 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2102 = FStar_ST.op_Bang comment_stack  in
          match uu____2102 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2165 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2165
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2206 =
                    let uu____2207 =
                      let uu____2208 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2208
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2207  in
                  comments_before_pos uu____2206 print_pos lookahead_pos))
              else
                (let uu____2210 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2210))
           in
        let uu____2211 =
          let uu____2216 =
            let uu____2217 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2217  in
          let uu____2218 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2216 uu____2218  in
        match uu____2211 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2224 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2224
              else comments  in
            let uu____2230 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2230
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2251 = FStar_ST.op_Bang comment_stack  in
          match uu____2251 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2343 =
                    let uu____2344 =
                      let uu____2345 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2345  in
                    uu____2344 - lbegin  in
                  max k uu____2343  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2348 =
                    let uu____2349 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2350 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2349 uu____2350  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2348  in
                let uu____2351 =
                  let uu____2352 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2352  in
                place_comments_until_pos (Prims.parse_int "1") uu____2351
                  pos_end doc2))
          | uu____2353 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2362 =
                     let uu____2363 = FStar_Range.line_of_pos pos_end  in
                     uu____2363 - lbegin  in
                   max (Prims.parse_int "1") uu____2362  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2365 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2365)
  
let separate_map_with_comments :
  'Auu____2378 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2378 -> FStar_Pprint.document) ->
          'Auu____2378 Prims.list ->
            ('Auu____2378 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2435 x =
              match uu____2435 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2449 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2449 doc1
                     in
                  let uu____2450 =
                    let uu____2451 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2451  in
                  let uu____2452 =
                    let uu____2453 =
                      let uu____2454 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2454  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2453  in
                  (uu____2450, uu____2452)
               in
            let uu____2455 =
              let uu____2462 = FStar_List.hd xs  in
              let uu____2463 = FStar_List.tl xs  in (uu____2462, uu____2463)
               in
            match uu____2455 with
            | (x,xs1) ->
                let init1 =
                  let uu____2479 =
                    let uu____2480 =
                      let uu____2481 = extract_range x  in
                      FStar_Range.end_of_range uu____2481  in
                    FStar_Range.line_of_pos uu____2480  in
                  let uu____2482 =
                    let uu____2483 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2483  in
                  (uu____2479, uu____2482)  in
                let uu____2484 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2484
  
let separate_map_with_comments_kw :
  'Auu____2507 'Auu____2508 .
    'Auu____2507 ->
      'Auu____2507 ->
        ('Auu____2507 -> 'Auu____2508 -> FStar_Pprint.document) ->
          'Auu____2508 Prims.list ->
            ('Auu____2508 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2570 x =
              match uu____2570 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2584 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2584 doc1
                     in
                  let uu____2585 =
                    let uu____2586 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2586  in
                  let uu____2587 =
                    let uu____2588 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2588  in
                  (uu____2585, uu____2587)
               in
            let uu____2589 =
              let uu____2596 = FStar_List.hd xs  in
              let uu____2597 = FStar_List.tl xs  in (uu____2596, uu____2597)
               in
            match uu____2589 with
            | (x,xs1) ->
                let init1 =
                  let uu____2613 =
                    let uu____2614 =
                      let uu____2615 = extract_range x  in
                      FStar_Range.end_of_range uu____2615  in
                    FStar_Range.line_of_pos uu____2614  in
                  let uu____2616 = f prefix1 x  in (uu____2613, uu____2616)
                   in
                let uu____2617 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2617
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3327)) ->
          let uu____3330 =
            let uu____3331 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3331 FStar_Util.is_upper  in
          if uu____3330
          then
            let uu____3334 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3334 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3336 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3343 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3344 =
      let uu____3345 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3346 =
        let uu____3347 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3347  in
      FStar_Pprint.op_Hat_Hat uu____3345 uu____3346  in
    FStar_Pprint.op_Hat_Hat uu____3343 uu____3344

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3349 ->
        let uu____3350 =
          let uu____3351 = str "@ "  in
          let uu____3352 =
            let uu____3353 =
              let uu____3354 =
                let uu____3355 =
                  let uu____3356 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3356  in
                FStar_Pprint.op_Hat_Hat uu____3355 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3354  in
            FStar_Pprint.op_Hat_Hat uu____3353 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3351 uu____3352  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3350

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3359  ->
    match uu____3359 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3395 =
                match uu____3395 with
                | (kwd,arg) ->
                    let uu____3402 = str "@"  in
                    let uu____3403 =
                      let uu____3404 = str kwd  in
                      let uu____3405 =
                        let uu____3406 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3406
                         in
                      FStar_Pprint.op_Hat_Hat uu____3404 uu____3405  in
                    FStar_Pprint.op_Hat_Hat uu____3402 uu____3403
                 in
              let uu____3407 =
                let uu____3408 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3408 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3407
           in
        let uu____3413 =
          let uu____3414 =
            let uu____3415 =
              let uu____3416 =
                let uu____3417 = str doc1  in
                let uu____3418 =
                  let uu____3419 =
                    let uu____3420 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3420  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3419  in
                FStar_Pprint.op_Hat_Hat uu____3417 uu____3418  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3416  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3415  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3414  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3413

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3424 =
          let uu____3425 = str "val"  in
          let uu____3426 =
            let uu____3427 =
              let uu____3428 = p_lident lid  in
              let uu____3429 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3428 uu____3429  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3427  in
          FStar_Pprint.op_Hat_Hat uu____3425 uu____3426  in
        let uu____3430 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3424 uu____3430
    | FStar_Parser_AST.TopLevelLet (uu____3431,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3456 =
               let uu____3457 = str "let"  in p_letlhs uu____3457 lb  in
             FStar_Pprint.group uu____3456) lbs
    | uu____3458 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___83_3473 =
          match uu___83_3473 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3481 = f x  in
              let uu____3482 =
                let uu____3483 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3483  in
              FStar_Pprint.op_Hat_Hat uu____3481 uu____3482
           in
        let uu____3484 = str "["  in
        let uu____3485 =
          let uu____3486 = p_list' l  in
          let uu____3487 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3486 uu____3487  in
        FStar_Pprint.op_Hat_Hat uu____3484 uu____3485

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3490 =
          let uu____3491 = str "open"  in
          let uu____3492 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3491 uu____3492  in
        FStar_Pprint.group uu____3490
    | FStar_Parser_AST.Include uid ->
        let uu____3494 =
          let uu____3495 = str "include"  in
          let uu____3496 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3495 uu____3496  in
        FStar_Pprint.group uu____3494
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3499 =
          let uu____3500 = str "module"  in
          let uu____3501 =
            let uu____3502 =
              let uu____3503 = p_uident uid1  in
              let uu____3504 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3503 uu____3504  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3502  in
          FStar_Pprint.op_Hat_Hat uu____3500 uu____3501  in
        let uu____3505 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3499 uu____3505
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3507 =
          let uu____3508 = str "module"  in
          let uu____3509 =
            let uu____3510 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3510  in
          FStar_Pprint.op_Hat_Hat uu____3508 uu____3509  in
        FStar_Pprint.group uu____3507
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3543 = str "effect"  in
          let uu____3544 =
            let uu____3545 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3545  in
          FStar_Pprint.op_Hat_Hat uu____3543 uu____3544  in
        let uu____3546 =
          let uu____3547 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3547 FStar_Pprint.equals
           in
        let uu____3548 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3546 uu____3548
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3566 =
          let uu____3567 = str "type"  in
          let uu____3568 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3567 uu____3568  in
        let uu____3581 =
          let uu____3582 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3620 =
                    let uu____3621 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3621 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3620)) uu____3582
           in
        FStar_Pprint.op_Hat_Hat uu____3566 uu____3581
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3637 = str "let"  in
          let uu____3638 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3637 uu____3638  in
        let uu____3639 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3639 p_letbinding lbs
          (fun uu____3647  ->
             match uu____3647 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3656 = str "val"  in
        let uu____3657 =
          let uu____3658 =
            let uu____3659 = p_lident lid  in
            let uu____3660 =
              let uu____3661 =
                let uu____3662 =
                  let uu____3663 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3663  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3662  in
              FStar_Pprint.group uu____3661  in
            FStar_Pprint.op_Hat_Hat uu____3659 uu____3660  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3658  in
        FStar_Pprint.op_Hat_Hat uu____3656 uu____3657
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3667 =
            let uu____3668 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3668 FStar_Util.is_upper  in
          if uu____3667
          then FStar_Pprint.empty
          else
            (let uu____3672 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3672 FStar_Pprint.space)
           in
        let uu____3673 =
          let uu____3674 = p_ident id1  in
          let uu____3675 =
            let uu____3676 =
              let uu____3677 =
                let uu____3678 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3678  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3677  in
            FStar_Pprint.group uu____3676  in
          FStar_Pprint.op_Hat_Hat uu____3674 uu____3675  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3673
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3685 = str "exception"  in
        let uu____3686 =
          let uu____3687 =
            let uu____3688 = p_uident uid  in
            let uu____3689 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3693 =
                     let uu____3694 = str "of"  in
                     let uu____3695 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3694 uu____3695  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3693) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3688 uu____3689  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3687  in
        FStar_Pprint.op_Hat_Hat uu____3685 uu____3686
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3697 = str "new_effect"  in
        let uu____3698 =
          let uu____3699 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3699  in
        FStar_Pprint.op_Hat_Hat uu____3697 uu____3698
    | FStar_Parser_AST.SubEffect se ->
        let uu____3701 = str "sub_effect"  in
        let uu____3702 =
          let uu____3703 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3703  in
        FStar_Pprint.op_Hat_Hat uu____3701 uu____3702
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3706 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3706 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3707 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3708) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3731 = str "%splice"  in
        let uu____3732 =
          let uu____3733 =
            let uu____3734 = str ";"  in p_list p_uident uu____3734 ids  in
          let uu____3735 =
            let uu____3736 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3736  in
          FStar_Pprint.op_Hat_Hat uu____3733 uu____3735  in
        FStar_Pprint.op_Hat_Hat uu____3731 uu____3732

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___84_3737  ->
    match uu___84_3737 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3739 = str "#set-options"  in
        let uu____3740 =
          let uu____3741 =
            let uu____3742 = str s  in FStar_Pprint.dquotes uu____3742  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3741  in
        FStar_Pprint.op_Hat_Hat uu____3739 uu____3740
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3746 = str "#reset-options"  in
        let uu____3747 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3751 =
                 let uu____3752 = str s  in FStar_Pprint.dquotes uu____3752
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3751) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3746 uu____3747
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
    fun uu____3781  ->
      match uu____3781 with
      | (typedecl,fsdoc_opt) ->
          let uu____3794 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3794 with
           | (decl,body) ->
               let uu____3812 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3812)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___85_3814  ->
      match uu___85_3814 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3844 = FStar_Pprint.empty  in
          let uu____3845 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3845, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3866 =
            let uu____3867 = p_typ false false t  in jump2 uu____3867  in
          let uu____3868 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3868, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3922 =
            match uu____3922 with
            | (lid1,t,doc_opt) ->
                let uu____3938 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3938
             in
          let p_fields uu____3954 =
            let uu____3955 =
              let uu____3956 =
                let uu____3957 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3957 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3956  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3955  in
          let uu____3966 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3966, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4027 =
            match uu____4027 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4053 =
                    let uu____4054 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4054  in
                  FStar_Range.extend_to_end_of_line uu____4053  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4080 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4093 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4093,
            ((fun uu____4099  ->
                let uu____4100 = datacon_doc ()  in jump2 uu____4100)))

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
  fun uu____4101  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4101 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4135 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4135  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4137 =
                        let uu____4140 =
                          let uu____4143 = p_fsdoc fsdoc  in
                          let uu____4144 =
                            let uu____4147 = cont lid_doc  in [uu____4147]
                             in
                          uu____4143 :: uu____4144  in
                        kw :: uu____4140  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4137
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4152 =
                        let uu____4153 =
                          let uu____4154 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4154 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4153
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4152
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4169 =
                          let uu____4170 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4170  in
                        prefix2 uu____4169 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4172  ->
      match uu____4172 with
      | (lid,t,doc_opt) ->
          let uu____4188 =
            let uu____4189 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4190 =
              let uu____4191 = p_lident lid  in
              let uu____4192 =
                let uu____4193 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4193  in
              FStar_Pprint.op_Hat_Hat uu____4191 uu____4192  in
            FStar_Pprint.op_Hat_Hat uu____4189 uu____4190  in
          FStar_Pprint.group uu____4188

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4194  ->
    match uu____4194 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4222 =
            let uu____4223 =
              let uu____4224 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4224  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4223  in
          FStar_Pprint.group uu____4222  in
        let uu____4225 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4226 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4230 =
                 let uu____4231 =
                   let uu____4232 =
                     let uu____4233 =
                       let uu____4234 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4234
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4233  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4232  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4231  in
               FStar_Pprint.group uu____4230) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4225 uu____4226

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4236  ->
      match uu____4236 with
      | (pat,uu____4242) ->
          let uu____4243 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4262 =
                  let uu____4263 =
                    let uu____4264 =
                      let uu____4265 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4265
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4264  in
                  FStar_Pprint.group uu____4263  in
                (pat1, uu____4262)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4277 =
                  let uu____4278 =
                    let uu____4279 =
                      let uu____4280 =
                        let uu____4281 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4281
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4280
                       in
                    FStar_Pprint.group uu____4279  in
                  let uu____4282 =
                    let uu____4283 =
                      let uu____4284 = str "by"  in
                      let uu____4285 =
                        let uu____4286 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4286
                         in
                      FStar_Pprint.op_Hat_Hat uu____4284 uu____4285  in
                    FStar_Pprint.group uu____4283  in
                  FStar_Pprint.op_Hat_Hat uu____4278 uu____4282  in
                (pat1, uu____4277)
            | uu____4287 -> (pat, FStar_Pprint.empty)  in
          (match uu____4243 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4291);
                       FStar_Parser_AST.prange = uu____4292;_},pats)
                    ->
                    let uu____4302 =
                      let uu____4303 =
                        let uu____4304 =
                          let uu____4305 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4305  in
                        FStar_Pprint.group uu____4304  in
                      let uu____4306 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4303 uu____4306  in
                    prefix2_nonempty uu____4302 ascr_doc
                | uu____4307 ->
                    let uu____4308 =
                      let uu____4309 =
                        let uu____4310 =
                          let uu____4311 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4311  in
                        FStar_Pprint.group uu____4310  in
                      FStar_Pprint.op_Hat_Hat uu____4309 ascr_doc  in
                    FStar_Pprint.group uu____4308))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4313  ->
      match uu____4313 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4322 =
            let uu____4323 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4323  in
          let uu____4324 =
            let uu____4325 =
              let uu____4326 =
                let uu____4327 =
                  let uu____4328 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4328  in
                FStar_Pprint.group uu____4327  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4326  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4325  in
          FStar_Pprint.ifflat uu____4322 uu____4324

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___86_4329  ->
    match uu___86_4329 with
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
        let uu____4354 = p_uident uid  in
        let uu____4355 = p_binders true bs  in
        let uu____4356 =
          let uu____4357 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4357  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4354 uu____4355 uu____4356

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
          let uu____4367 =
            let uu____4368 =
              let uu____4369 =
                let uu____4370 = p_uident uid  in
                let uu____4371 = p_binders true bs  in
                let uu____4372 =
                  let uu____4373 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4373  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4370 uu____4371 uu____4372
                 in
              FStar_Pprint.group uu____4369  in
            let uu____4374 =
              let uu____4375 = str "with"  in
              let uu____4376 =
                let uu____4377 =
                  let uu____4378 =
                    let uu____4379 =
                      let uu____4380 =
                        let uu____4381 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4381
                         in
                      separate_map_last uu____4380 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4379  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4378  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4377  in
              FStar_Pprint.op_Hat_Hat uu____4375 uu____4376  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4368 uu____4374  in
          braces_with_nesting uu____4367

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
          let uu____4412 =
            let uu____4413 = p_lident lid  in
            let uu____4414 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4413 uu____4414  in
          let uu____4415 = p_simpleTerm ps false e  in
          prefix2 uu____4412 uu____4415
      | uu____4416 ->
          let uu____4417 =
            let uu____4418 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4418
             in
          failwith uu____4417

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4480 =
        match uu____4480 with
        | (kwd,t) ->
            let uu____4487 =
              let uu____4488 = str kwd  in
              let uu____4489 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4488 uu____4489  in
            let uu____4490 = p_simpleTerm ps false t  in
            prefix2 uu____4487 uu____4490
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4495 =
      let uu____4496 =
        let uu____4497 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4498 =
          let uu____4499 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4499  in
        FStar_Pprint.op_Hat_Hat uu____4497 uu____4498  in
      let uu____4500 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4496 uu____4500  in
    let uu____4501 =
      let uu____4502 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4502  in
    FStar_Pprint.op_Hat_Hat uu____4495 uu____4501

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___87_4503  ->
    match uu___87_4503 with
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
    | uu____4505 ->
        let uu____4506 =
          let uu____4507 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4507  in
        FStar_Pprint.op_Hat_Hat uu____4506 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___88_4510  ->
    match uu___88_4510 with
    | FStar_Parser_AST.Rec  ->
        let uu____4511 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4511
    | FStar_Parser_AST.Mutable  ->
        let uu____4512 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4512
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___89_4513  ->
    match uu___89_4513 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4518 =
          let uu____4519 =
            let uu____4520 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4520  in
          FStar_Pprint.separate_map uu____4519 p_tuplePattern pats  in
        FStar_Pprint.group uu____4518
    | uu____4521 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4528 =
          let uu____4529 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4529 p_constructorPattern pats  in
        FStar_Pprint.group uu____4528
    | uu____4530 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4533;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4538 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4539 = p_constructorPattern hd1  in
        let uu____4540 = p_constructorPattern tl1  in
        infix0 uu____4538 uu____4539 uu____4540
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4542;_},pats)
        ->
        let uu____4548 = p_quident uid  in
        let uu____4549 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4548 uu____4549
    | uu____4550 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4566;
               FStar_Parser_AST.blevel = uu____4567;
               FStar_Parser_AST.aqual = uu____4568;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4574 =
               let uu____4575 = p_ident lid  in
               p_refinement aqual uu____4575 t1 phi  in
             soft_parens_with_nesting uu____4574
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4577;
               FStar_Parser_AST.blevel = uu____4578;
               FStar_Parser_AST.aqual = uu____4579;_},phi))
             ->
             let uu____4581 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4581
         | uu____4582 ->
             let uu____4587 =
               let uu____4588 = p_tuplePattern pat  in
               let uu____4589 =
                 let uu____4590 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4590
                  in
               FStar_Pprint.op_Hat_Hat uu____4588 uu____4589  in
             soft_parens_with_nesting uu____4587)
    | FStar_Parser_AST.PatList pats ->
        let uu____4594 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4594 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4611 =
          match uu____4611 with
          | (lid,pat) ->
              let uu____4618 = p_qlident lid  in
              let uu____4619 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4618 uu____4619
           in
        let uu____4620 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4620
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4630 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4631 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4632 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4630 uu____4631 uu____4632
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4641 =
          let uu____4642 =
            let uu____4643 =
              let uu____4644 = FStar_Ident.text_of_id op  in str uu____4644
               in
            let uu____4645 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4643 uu____4645  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4642  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4641
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4653 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4654 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4653 uu____4654
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4656 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4659;
           FStar_Parser_AST.prange = uu____4660;_},uu____4661)
        ->
        let uu____4666 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4666
    | FStar_Parser_AST.PatTuple (uu____4667,false ) ->
        let uu____4672 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4672
    | uu____4673 ->
        let uu____4674 =
          let uu____4675 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4675  in
        failwith uu____4674

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4677;_},uu____4678)
        -> true
    | uu____4683 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4687 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4688 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4687 uu____4688
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4695;
                   FStar_Parser_AST.blevel = uu____4696;
                   FStar_Parser_AST.aqual = uu____4697;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4699 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4699 t1 phi
            | uu____4700 ->
                let t' =
                  let uu____4702 = is_typ_tuple t  in
                  if uu____4702
                  then
                    let uu____4703 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4703
                  else p_tmFormula t  in
                let uu____4705 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4706 =
                  let uu____4707 = p_lident lid  in
                  let uu____4708 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4707 uu____4708  in
                FStar_Pprint.op_Hat_Hat uu____4705 uu____4706
             in
          if is_atomic
          then
            let uu____4709 =
              let uu____4710 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4710  in
            FStar_Pprint.group uu____4709
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4712 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4719;
                  FStar_Parser_AST.blevel = uu____4720;
                  FStar_Parser_AST.aqual = uu____4721;_},phi)
               ->
               if is_atomic
               then
                 let uu____4723 =
                   let uu____4724 =
                     let uu____4725 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4725 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4724  in
                 FStar_Pprint.group uu____4723
               else
                 (let uu____4727 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4727)
           | uu____4728 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4737 -> false
            | FStar_Parser_AST.App uu____4748 -> false
            | FStar_Parser_AST.Op uu____4755 -> false
            | uu____4762 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4766 =
            let uu____4767 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4768 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4767 uu____4768  in
          let uu____4769 =
            let uu____4770 = p_appTerm t  in
            let uu____4771 =
              let uu____4772 =
                let uu____4773 =
                  let uu____4774 = soft_braces_with_nesting_tight phi1  in
                  let uu____4775 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4774 uu____4775  in
                FStar_Pprint.group uu____4773  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4772
               in
            FStar_Pprint.op_Hat_Hat uu____4770 uu____4771  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4766 uu____4769

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4786 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4786

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4791 = FStar_Ident.text_of_id lid  in str uu____4791)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4794 = FStar_Ident.text_of_lid lid  in str uu____4794)

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
  = fun b  -> if b then soft_parens_with_nesting else (let id1 x = x  in id1)

and (p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____4817 =
              let uu____4818 =
                let uu____4819 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4819 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4818  in
            let uu____4820 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4817 uu____4820
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4824 =
              let uu____4825 =
                let uu____4826 =
                  let uu____4827 = p_lident x  in
                  let uu____4828 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4827 uu____4828  in
                let uu____4829 =
                  let uu____4830 = p_noSeqTerm true false e1  in
                  let uu____4831 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4830 uu____4831  in
                op_Hat_Slash_Plus_Hat uu____4826 uu____4829  in
              FStar_Pprint.group uu____4825  in
            let uu____4832 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4824 uu____4832
        | uu____4833 ->
            let uu____4834 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4834

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
            let uu____4845 =
              let uu____4846 = p_tmIff e1  in
              let uu____4847 =
                let uu____4848 =
                  let uu____4849 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4849
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4848  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4846 uu____4847  in
            FStar_Pprint.group uu____4845
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4855 =
              let uu____4856 = p_tmIff e1  in
              let uu____4857 =
                let uu____4858 =
                  let uu____4859 =
                    let uu____4860 = p_typ false false t  in
                    let uu____4861 =
                      let uu____4862 = str "by"  in
                      let uu____4863 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4862 uu____4863  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4860 uu____4861  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4859
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4858  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4856 uu____4857  in
            FStar_Pprint.group uu____4855
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4864;_},e1::e2::e3::[])
            ->
            let uu____4870 =
              let uu____4871 =
                let uu____4872 =
                  let uu____4873 = p_atomicTermNotQUident e1  in
                  let uu____4874 =
                    let uu____4875 =
                      let uu____4876 =
                        let uu____4877 = p_term false false e2  in
                        soft_parens_with_nesting uu____4877  in
                      let uu____4878 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4876 uu____4878  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4875  in
                  FStar_Pprint.op_Hat_Hat uu____4873 uu____4874  in
                FStar_Pprint.group uu____4872  in
              let uu____4879 =
                let uu____4880 = p_noSeqTerm ps pb e3  in jump2 uu____4880
                 in
              FStar_Pprint.op_Hat_Hat uu____4871 uu____4879  in
            FStar_Pprint.group uu____4870
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4881;_},e1::e2::e3::[])
            ->
            let uu____4887 =
              let uu____4888 =
                let uu____4889 =
                  let uu____4890 = p_atomicTermNotQUident e1  in
                  let uu____4891 =
                    let uu____4892 =
                      let uu____4893 =
                        let uu____4894 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4894  in
                      let uu____4895 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4893 uu____4895  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4892  in
                  FStar_Pprint.op_Hat_Hat uu____4890 uu____4891  in
                FStar_Pprint.group uu____4889  in
              let uu____4896 =
                let uu____4897 = p_noSeqTerm ps pb e3  in jump2 uu____4897
                 in
              FStar_Pprint.op_Hat_Hat uu____4888 uu____4896  in
            FStar_Pprint.group uu____4887
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4905 =
              let uu____4906 = str "requires"  in
              let uu____4907 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4906 uu____4907  in
            FStar_Pprint.group uu____4905
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4915 =
              let uu____4916 = str "ensures"  in
              let uu____4917 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4916 uu____4917  in
            FStar_Pprint.group uu____4915
        | FStar_Parser_AST.Attributes es ->
            let uu____4921 =
              let uu____4922 = str "attributes"  in
              let uu____4923 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4922 uu____4923  in
            FStar_Pprint.group uu____4921
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4927 =
                let uu____4928 =
                  let uu____4929 = str "if"  in
                  let uu____4930 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4929 uu____4930  in
                let uu____4931 =
                  let uu____4932 = str "then"  in
                  let uu____4933 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4932 uu____4933  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4928 uu____4931  in
              FStar_Pprint.group uu____4927
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4936,uu____4937,e31) when
                     is_unit e31 ->
                     let uu____4939 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4939
                 | uu____4940 -> p_noSeqTerm false false e2  in
               let uu____4941 =
                 let uu____4942 =
                   let uu____4943 = str "if"  in
                   let uu____4944 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4943 uu____4944  in
                 let uu____4945 =
                   let uu____4946 =
                     let uu____4947 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4947 e2_doc  in
                   let uu____4948 =
                     let uu____4949 = str "else"  in
                     let uu____4950 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4949 uu____4950  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4946 uu____4948  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4942 uu____4945  in
               FStar_Pprint.group uu____4941)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4973 =
              let uu____4974 =
                let uu____4975 =
                  let uu____4976 = str "try"  in
                  let uu____4977 = p_noSeqTerm false false e1  in
                  prefix2 uu____4976 uu____4977  in
                let uu____4978 =
                  let uu____4979 = str "with"  in
                  let uu____4980 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4979 uu____4980  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4975 uu____4978  in
              FStar_Pprint.group uu____4974  in
            let uu____4989 = paren_if (ps || pb)  in uu____4989 uu____4973
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5016 =
              let uu____5017 =
                let uu____5018 =
                  let uu____5019 = str "match"  in
                  let uu____5020 = p_noSeqTerm false false e1  in
                  let uu____5021 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5019 uu____5020 uu____5021
                   in
                let uu____5022 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5022  in
              FStar_Pprint.group uu____5017  in
            let uu____5031 = paren_if (ps || pb)  in uu____5031 uu____5016
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5038 =
              let uu____5039 =
                let uu____5040 =
                  let uu____5041 = str "let open"  in
                  let uu____5042 = p_quident uid  in
                  let uu____5043 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5041 uu____5042 uu____5043
                   in
                let uu____5044 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5040 uu____5044  in
              FStar_Pprint.group uu____5039  in
            let uu____5045 = paren_if ps  in uu____5045 uu____5038
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5109 is_last =
              match uu____5109 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5142 =
                          let uu____5143 = str "let"  in
                          let uu____5144 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5143 uu____5144
                           in
                        FStar_Pprint.group uu____5142
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5145 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5150 =
                    if is_last
                    then
                      let uu____5151 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5152 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5151 doc_expr uu____5152
                    else
                      (let uu____5154 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5154)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5150
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5200 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5200
                     else
                       (let uu____5208 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5208)) lbs
               in
            let lbs_doc =
              let uu____5216 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5216  in
            let uu____5217 =
              let uu____5218 =
                let uu____5219 =
                  let uu____5220 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5220
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5219  in
              FStar_Pprint.group uu____5218  in
            let uu____5221 = paren_if ps  in uu____5221 uu____5217
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5228;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5231;
                                                             FStar_Parser_AST.level
                                                               = uu____5232;_})
            when matches_var maybe_x x ->
            let uu____5259 =
              let uu____5260 =
                let uu____5261 = str "function"  in
                let uu____5262 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5261 uu____5262  in
              FStar_Pprint.group uu____5260  in
            let uu____5271 = paren_if (ps || pb)  in uu____5271 uu____5259
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5277 =
              let uu____5278 = str "quote"  in
              let uu____5279 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5278 uu____5279  in
            FStar_Pprint.group uu____5277
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5281 =
              let uu____5282 = str "`"  in
              let uu____5283 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5282 uu____5283  in
            FStar_Pprint.group uu____5281
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5285 =
              let uu____5286 = str "%`"  in
              let uu____5287 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5286 uu____5287  in
            FStar_Pprint.group uu____5285
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5289 =
              let uu____5290 = str "`#"  in
              let uu____5291 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5290 uu____5291  in
            FStar_Pprint.group uu____5289
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5293 =
              let uu____5294 = str "`@"  in
              let uu____5295 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5294 uu____5295  in
            FStar_Pprint.group uu____5293
        | uu____5296 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___90_5297  ->
    match uu___90_5297 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5309 =
          let uu____5310 = str "[@"  in
          let uu____5311 =
            let uu____5312 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5313 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5312 uu____5313  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5310 uu____5311  in
        FStar_Pprint.group uu____5309

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
                 let uu____5339 =
                   let uu____5340 =
                     let uu____5341 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5341 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5340 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5339 term_doc
             | pats ->
                 let uu____5347 =
                   let uu____5348 =
                     let uu____5349 =
                       let uu____5350 =
                         let uu____5351 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5351
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5350 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5352 = p_trigger trigger  in
                     prefix2 uu____5349 uu____5352  in
                   FStar_Pprint.group uu____5348  in
                 prefix2 uu____5347 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5372 =
                   let uu____5373 =
                     let uu____5374 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5374 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5373 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5372 term_doc
             | pats ->
                 let uu____5380 =
                   let uu____5381 =
                     let uu____5382 =
                       let uu____5383 =
                         let uu____5384 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5384
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5383 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5385 = p_trigger trigger  in
                     prefix2 uu____5382 uu____5385  in
                   FStar_Pprint.group uu____5381  in
                 prefix2 uu____5380 term_doc)
        | uu____5386 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5388 -> str "forall"
    | FStar_Parser_AST.QExists uu____5401 -> str "exists"
    | uu____5414 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___91_5415  ->
    match uu___91_5415 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5427 =
          let uu____5428 =
            let uu____5429 =
              let uu____5430 = str "pattern"  in
              let uu____5431 =
                let uu____5432 =
                  let uu____5433 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5433
                   in
                FStar_Pprint.op_Hat_Hat uu____5432 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5430 uu____5431  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5429  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5428  in
        FStar_Pprint.group uu____5427

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5439 = str "\\/"  in
    FStar_Pprint.separate_map uu____5439 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5445 =
      let uu____5446 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5446 p_appTerm pats  in
    FStar_Pprint.group uu____5445

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5456 =
              let uu____5457 =
                let uu____5458 = str "fun"  in
                let uu____5459 =
                  let uu____5460 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5460
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5458 uu____5459  in
              let uu____5461 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5457 uu____5461  in
            let uu____5462 = paren_if ps  in uu____5462 uu____5456
        | uu____5467 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5471  ->
      match uu____5471 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5494 =
                    let uu____5495 =
                      let uu____5496 =
                        let uu____5497 = p_tuplePattern p  in
                        let uu____5498 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5497 uu____5498  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5496
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5495  in
                  FStar_Pprint.group uu____5494
              | FStar_Pervasives_Native.Some f ->
                  let uu____5500 =
                    let uu____5501 =
                      let uu____5502 =
                        let uu____5503 =
                          let uu____5504 =
                            let uu____5505 = p_tuplePattern p  in
                            let uu____5506 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5505
                              uu____5506
                             in
                          FStar_Pprint.group uu____5504  in
                        let uu____5507 =
                          let uu____5508 =
                            let uu____5511 = p_tmFormula f  in
                            [uu____5511; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5508  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5503 uu____5507
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5502
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5501  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5500
               in
            let uu____5512 =
              let uu____5513 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5513  in
            FStar_Pprint.group uu____5512  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5522 =
                      let uu____5523 =
                        let uu____5524 =
                          let uu____5525 =
                            let uu____5526 =
                              let uu____5527 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5527  in
                            FStar_Pprint.separate_map uu____5526
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5525
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5524
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5523  in
                    FStar_Pprint.group uu____5522
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5528 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5530;_},e1::e2::[])
        ->
        let uu____5535 = str "<==>"  in
        let uu____5536 = p_tmImplies e1  in
        let uu____5537 = p_tmIff e2  in
        infix0 uu____5535 uu____5536 uu____5537
    | uu____5538 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5540;_},e1::e2::[])
        ->
        let uu____5545 = str "==>"  in
        let uu____5546 = p_tmArrow p_tmFormula e1  in
        let uu____5547 = p_tmImplies e2  in
        infix0 uu____5545 uu____5546 uu____5547
    | uu____5548 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5556 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5556 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5577 ->
               let uu____5578 =
                 let uu____5579 =
                   let uu____5580 =
                     let uu____5581 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5581
                      in
                   FStar_Pprint.separate uu____5580 terms  in
                 let uu____5582 =
                   let uu____5583 =
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
                       let uu____5589 =
                         let uu____5590 =
                           let uu____5591 =
                             let uu____5592 =
                               let uu____5593 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5593
                                in
                             FStar_Pprint.separate uu____5592 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5591 last_op  in
                         jump2 uu____5590  in
                       FStar_Pprint.ifflat uu____5585 uu____5589  in
                     FStar_Pprint.group uu____5584  in
                   let uu____5594 = FStar_List.hd last1  in
                   prefix2 uu____5583 uu____5594  in
                 FStar_Pprint.ifflat uu____5579 uu____5582  in
               FStar_Pprint.group uu____5578)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5607 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5612 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5607 uu____5612
      | uu____5615 -> let uu____5616 = p_Tm e  in [uu____5616]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5619 =
        let uu____5620 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5620 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5619  in
    let disj =
      let uu____5622 =
        let uu____5623 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5623 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5622  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5642;_},e1::e2::[])
        ->
        let uu____5647 = p_tmDisjunction e1  in
        let uu____5652 = let uu____5657 = p_tmConjunction e2  in [uu____5657]
           in
        FStar_List.append uu____5647 uu____5652
    | uu____5666 -> let uu____5667 = p_tmConjunction e  in [uu____5667]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5677;_},e1::e2::[])
        ->
        let uu____5682 = p_tmConjunction e1  in
        let uu____5685 = let uu____5688 = p_tmTuple e2  in [uu____5688]  in
        FStar_List.append uu____5682 uu____5685
    | uu____5689 -> let uu____5690 = p_tmTuple e  in [uu____5690]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5707 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5707
          (fun uu____5715  ->
             match uu____5715 with | (e1,uu____5721) -> p_tmEq e1) args
    | uu____5722 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5727 =
             let uu____5728 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5728  in
           FStar_Pprint.group uu____5727)

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
               (let uu____5745 = FStar_Ident.text_of_id op  in
                uu____5745 = "="))
              ||
              (let uu____5747 = FStar_Ident.text_of_id op  in
               uu____5747 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5749 = levels op1  in
            (match uu____5749 with
             | (left1,mine,right1) ->
                 let uu____5759 =
                   let uu____5760 = FStar_All.pipe_left str op1  in
                   let uu____5761 = p_tmEqWith' p_X left1 e1  in
                   let uu____5762 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5760 uu____5761 uu____5762  in
                 paren_if_gt curr mine uu____5759)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5763;_},e1::e2::[])
            ->
            let uu____5768 =
              let uu____5769 = p_tmEqWith p_X e1  in
              let uu____5770 =
                let uu____5771 =
                  let uu____5772 =
                    let uu____5773 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5773  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5772  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5771  in
              FStar_Pprint.op_Hat_Hat uu____5769 uu____5770  in
            FStar_Pprint.group uu____5768
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5774;_},e1::[])
            ->
            let uu____5778 = levels "-"  in
            (match uu____5778 with
             | (left1,mine,right1) ->
                 let uu____5788 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5788)
        | uu____5789 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5833)::(e2,uu____5835)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5855 = is_list e  in Prims.op_Negation uu____5855)
              ->
              let op = "::"  in
              let uu____5857 = levels op  in
              (match uu____5857 with
               | (left1,mine,right1) ->
                   let uu____5867 =
                     let uu____5868 = str op  in
                     let uu____5869 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5870 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5868 uu____5869 uu____5870  in
                   paren_if_gt curr mine uu____5867)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5878 = levels op  in
              (match uu____5878 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5894 = p_binder false b  in
                     let uu____5895 =
                       let uu____5896 =
                         let uu____5897 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5897 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5896
                        in
                     FStar_Pprint.op_Hat_Hat uu____5894 uu____5895  in
                   let uu____5898 =
                     let uu____5899 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5900 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5899 uu____5900  in
                   paren_if_gt curr mine uu____5898)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5901;_},e1::e2::[])
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
                 let uu____6151 =
                   FStar_Util.take
                     (fun uu____6175  ->
                        match uu____6175 with
                        | (uu____6180,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6151 with
                 | (fs_typ_args,args1) ->
                     let uu____6218 =
                       let uu____6219 = p_indexingTerm head1  in
                       let uu____6220 =
                         let uu____6221 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6221 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6219 uu____6220  in
                     (uu____6218, args1)
               else
                 (let uu____6233 = p_indexingTerm head1  in
                  (uu____6233, args))
                in
             (match uu____6106 with
              | (head_doc,args1) ->
                  let uu____6254 =
                    let uu____6255 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6255 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6254))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6275 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6275)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6293 =
               let uu____6294 = p_quident lid  in
               let uu____6295 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6294 uu____6295  in
             FStar_Pprint.group uu____6293
         | hd1::tl1 ->
             let uu____6312 =
               let uu____6313 =
                 let uu____6314 =
                   let uu____6315 = p_quident lid  in
                   let uu____6316 = p_argTerm hd1  in
                   prefix2 uu____6315 uu____6316  in
                 FStar_Pprint.group uu____6314  in
               let uu____6317 =
                 let uu____6318 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6318  in
               FStar_Pprint.op_Hat_Hat uu____6313 uu____6317  in
             FStar_Pprint.group uu____6312)
    | uu____6323 -> p_indexingTerm e

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
         (let uu____6332 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6332 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6334 = str "#"  in
        let uu____6335 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6334 uu____6335
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6337  ->
    match uu____6337 with | (e,uu____6343) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6348;_},e1::e2::[])
          ->
          let uu____6353 =
            let uu____6354 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6355 =
              let uu____6356 =
                let uu____6357 = p_term false false e2  in
                soft_parens_with_nesting uu____6357  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6356  in
            FStar_Pprint.op_Hat_Hat uu____6354 uu____6355  in
          FStar_Pprint.group uu____6353
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6358;_},e1::e2::[])
          ->
          let uu____6363 =
            let uu____6364 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6365 =
              let uu____6366 =
                let uu____6367 = p_term false false e2  in
                soft_brackets_with_nesting uu____6367  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6366  in
            FStar_Pprint.op_Hat_Hat uu____6364 uu____6365  in
          FStar_Pprint.group uu____6363
      | uu____6368 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6373 = p_quident lid  in
        let uu____6374 =
          let uu____6375 =
            let uu____6376 = p_term false false e1  in
            soft_parens_with_nesting uu____6376  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6375  in
        FStar_Pprint.op_Hat_Hat uu____6373 uu____6374
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6382 =
          let uu____6383 = FStar_Ident.text_of_id op  in str uu____6383  in
        let uu____6384 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6382 uu____6384
    | uu____6385 -> p_atomicTermNotQUident e

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
         | uu____6394 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6401 =
          let uu____6402 = FStar_Ident.text_of_id op  in str uu____6402  in
        let uu____6403 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6401 uu____6403
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6407 =
          let uu____6408 =
            let uu____6409 =
              let uu____6410 = FStar_Ident.text_of_id op  in str uu____6410
               in
            let uu____6411 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6409 uu____6411  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6408  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6407
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6426 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6427 =
          let uu____6428 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6429 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6428 p_tmEq uu____6429  in
        let uu____6436 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6426 uu____6427 uu____6436
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6439 =
          let uu____6440 = p_atomicTermNotQUident e1  in
          let uu____6441 =
            let uu____6442 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6442  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6440 uu____6441
           in
        FStar_Pprint.group uu____6439
    | uu____6443 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6448 = p_quident constr_lid  in
        let uu____6449 =
          let uu____6450 =
            let uu____6451 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6451  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6450  in
        FStar_Pprint.op_Hat_Hat uu____6448 uu____6449
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6453 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6453 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6455 = p_term false false e1  in
        soft_parens_with_nesting uu____6455
    | uu____6456 when is_array e ->
        let es = extract_from_list e  in
        let uu____6460 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6461 =
          let uu____6462 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6462
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6465 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6460 uu____6461 uu____6465
    | uu____6466 when is_list e ->
        let uu____6467 =
          let uu____6468 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6469 = extract_from_list e  in
          separate_map_or_flow_last uu____6468
            (fun ps  -> p_noSeqTerm ps false) uu____6469
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6467 FStar_Pprint.rbracket
    | uu____6474 when is_lex_list e ->
        let uu____6475 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6476 =
          let uu____6477 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6478 = extract_from_list e  in
          separate_map_or_flow_last uu____6477
            (fun ps  -> p_noSeqTerm ps false) uu____6478
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6475 uu____6476 FStar_Pprint.rbracket
    | uu____6483 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6487 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6488 =
          let uu____6489 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6489 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6487 uu____6488 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6493 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6494 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6493 uu____6494
    | FStar_Parser_AST.Op (op,args) when
        let uu____6501 = handleable_op op args  in
        Prims.op_Negation uu____6501 ->
        let uu____6502 =
          let uu____6503 =
            let uu____6504 = FStar_Ident.text_of_id op  in
            let uu____6505 =
              let uu____6506 =
                let uu____6507 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6507
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6506  in
            Prims.strcat uu____6504 uu____6505  in
          Prims.strcat "Operation " uu____6503  in
        failwith uu____6502
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6509 = str "u#"  in
        let uu____6510 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6509 uu____6510
    | FStar_Parser_AST.Wild  ->
        let uu____6511 = p_term false false e  in
        soft_parens_with_nesting uu____6511
    | FStar_Parser_AST.Const uu____6512 ->
        let uu____6513 = p_term false false e  in
        soft_parens_with_nesting uu____6513
    | FStar_Parser_AST.Op uu____6514 ->
        let uu____6521 = p_term false false e  in
        soft_parens_with_nesting uu____6521
    | FStar_Parser_AST.Tvar uu____6522 ->
        let uu____6523 = p_term false false e  in
        soft_parens_with_nesting uu____6523
    | FStar_Parser_AST.Var uu____6524 ->
        let uu____6525 = p_term false false e  in
        soft_parens_with_nesting uu____6525
    | FStar_Parser_AST.Name uu____6526 ->
        let uu____6527 = p_term false false e  in
        soft_parens_with_nesting uu____6527
    | FStar_Parser_AST.Construct uu____6528 ->
        let uu____6539 = p_term false false e  in
        soft_parens_with_nesting uu____6539
    | FStar_Parser_AST.Abs uu____6540 ->
        let uu____6547 = p_term false false e  in
        soft_parens_with_nesting uu____6547
    | FStar_Parser_AST.App uu____6548 ->
        let uu____6555 = p_term false false e  in
        soft_parens_with_nesting uu____6555
    | FStar_Parser_AST.Let uu____6556 ->
        let uu____6577 = p_term false false e  in
        soft_parens_with_nesting uu____6577
    | FStar_Parser_AST.LetOpen uu____6578 ->
        let uu____6583 = p_term false false e  in
        soft_parens_with_nesting uu____6583
    | FStar_Parser_AST.Seq uu____6584 ->
        let uu____6589 = p_term false false e  in
        soft_parens_with_nesting uu____6589
    | FStar_Parser_AST.Bind uu____6590 ->
        let uu____6597 = p_term false false e  in
        soft_parens_with_nesting uu____6597
    | FStar_Parser_AST.If uu____6598 ->
        let uu____6605 = p_term false false e  in
        soft_parens_with_nesting uu____6605
    | FStar_Parser_AST.Match uu____6606 ->
        let uu____6621 = p_term false false e  in
        soft_parens_with_nesting uu____6621
    | FStar_Parser_AST.TryWith uu____6622 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Ascribed uu____6638 ->
        let uu____6647 = p_term false false e  in
        soft_parens_with_nesting uu____6647
    | FStar_Parser_AST.Record uu____6648 ->
        let uu____6661 = p_term false false e  in
        soft_parens_with_nesting uu____6661
    | FStar_Parser_AST.Project uu____6662 ->
        let uu____6667 = p_term false false e  in
        soft_parens_with_nesting uu____6667
    | FStar_Parser_AST.Product uu____6668 ->
        let uu____6675 = p_term false false e  in
        soft_parens_with_nesting uu____6675
    | FStar_Parser_AST.Sum uu____6676 ->
        let uu____6683 = p_term false false e  in
        soft_parens_with_nesting uu____6683
    | FStar_Parser_AST.QForall uu____6684 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.QExists uu____6698 ->
        let uu____6711 = p_term false false e  in
        soft_parens_with_nesting uu____6711
    | FStar_Parser_AST.Refine uu____6712 ->
        let uu____6717 = p_term false false e  in
        soft_parens_with_nesting uu____6717
    | FStar_Parser_AST.NamedTyp uu____6718 ->
        let uu____6723 = p_term false false e  in
        soft_parens_with_nesting uu____6723
    | FStar_Parser_AST.Requires uu____6724 ->
        let uu____6731 = p_term false false e  in
        soft_parens_with_nesting uu____6731
    | FStar_Parser_AST.Ensures uu____6732 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.Attributes uu____6740 ->
        let uu____6743 = p_term false false e  in
        soft_parens_with_nesting uu____6743
    | FStar_Parser_AST.Quote uu____6744 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.VQuote uu____6750 ->
        let uu____6751 = p_term false false e  in
        soft_parens_with_nesting uu____6751
    | FStar_Parser_AST.Antiquote uu____6752 ->
        let uu____6757 = p_term false false e  in
        soft_parens_with_nesting uu____6757

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___94_6758  ->
    match uu___94_6758 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6764) ->
        let uu____6765 = str s  in FStar_Pprint.dquotes uu____6765
    | FStar_Const.Const_bytearray (bytes,uu____6767) ->
        let uu____6772 =
          let uu____6773 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6773  in
        let uu____6774 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6772 uu____6774
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___92_6794 =
          match uu___92_6794 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___93_6800 =
          match uu___93_6800 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6811  ->
               match uu____6811 with
               | (s,w) ->
                   let uu____6818 = signedness s  in
                   let uu____6819 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6818 uu____6819)
            sign_width_opt
           in
        let uu____6820 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6820 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6822 = FStar_Range.string_of_range r  in str uu____6822
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6824 = p_quident lid  in
        let uu____6825 =
          let uu____6826 =
            let uu____6827 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6827  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6826  in
        FStar_Pprint.op_Hat_Hat uu____6824 uu____6825

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6829 = str "u#"  in
    let uu____6830 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6829 uu____6830

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6832;_},u1::u2::[])
        ->
        let uu____6837 =
          let uu____6838 = p_universeFrom u1  in
          let uu____6839 =
            let uu____6840 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6840  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6838 uu____6839  in
        FStar_Pprint.group uu____6837
    | FStar_Parser_AST.App uu____6841 ->
        let uu____6848 = head_and_args u  in
        (match uu____6848 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6874 =
                    let uu____6875 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6876 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6884  ->
                           match uu____6884 with
                           | (u1,uu____6890) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6875 uu____6876  in
                  FStar_Pprint.group uu____6874
              | uu____6891 ->
                  let uu____6892 =
                    let uu____6893 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6893
                     in
                  failwith uu____6892))
    | uu____6894 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6917 = FStar_Ident.text_of_id id1  in str uu____6917
    | FStar_Parser_AST.Paren u1 ->
        let uu____6919 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6919
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6920;_},uu____6921::uu____6922::[])
        ->
        let uu____6925 = p_universeFrom u  in
        soft_parens_with_nesting uu____6925
    | FStar_Parser_AST.App uu____6926 ->
        let uu____6933 = p_universeFrom u  in
        soft_parens_with_nesting uu____6933
    | uu____6934 ->
        let uu____6935 =
          let uu____6936 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6936
           in
        failwith uu____6935

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
       | FStar_Parser_AST.Module (uu____7016,decls) ->
           let uu____7022 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7022
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7031,decls,uu____7033) ->
           let uu____7038 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7038
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7095  ->
         match uu____7095 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7139,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7145,decls,uu____7147) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7196 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7209;
                 FStar_Parser_AST.doc = uu____7210;
                 FStar_Parser_AST.quals = uu____7211;
                 FStar_Parser_AST.attrs = uu____7212;_}::uu____7213 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7219 =
                   let uu____7222 =
                     let uu____7225 = FStar_List.tl ds  in d :: uu____7225
                      in
                   d0 :: uu____7222  in
                 (uu____7219, (d0.FStar_Parser_AST.drange))
             | uu____7230 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7196 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7294 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7294 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7402 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7402, comments1))))))
  