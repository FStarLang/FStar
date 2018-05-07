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
      let uu____1108 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1108 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1113 = FStar_Ident.text_of_id op  in uu____1113 <> "~"))
  
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
      | uu____1179 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1195 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1201 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1207 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___80_1227  ->
    match uu___80_1227 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___81_1248  ->
      match uu___81_1248 with
      | FStar_Util.Inl c ->
          let uu____1257 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1257 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1268 .
    Prims.string ->
      ('Auu____1268,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1289  ->
      match uu____1289 with
      | (assoc_levels,tokens) ->
          let uu____1317 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1317 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1344 .
    unit ->
      (associativity,('Auu____1344,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1355  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1372 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1372) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1384  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1420 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1420) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1432  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1461 .
    unit ->
      (associativity,('Auu____1461,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1472  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1489 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1489) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1501  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1530 .
    unit ->
      (associativity,('Auu____1530,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1541  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1558 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1558) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1570  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1592 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1592) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1604  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1640 .
    unit ->
      (associativity,('Auu____1640,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1651  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1668 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1668) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1680  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1702 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1702) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1714  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1736 .
    unit ->
      (associativity,('Auu____1736,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1747  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1764 .
    unit ->
      (associativity,('Auu____1764,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1775  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1792 .
    unit ->
      (associativity,('Auu____1792,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1803  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___82_2014 =
    match uu___82_2014 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____2054  ->
         match uu____2054 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2138 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2138 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2188) ->
          assoc_levels
      | uu____2232 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____2273 .
    ('Auu____2273,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2338 =
        FStar_List.tryFind
          (fun uu____2378  ->
             match uu____2378 with
             | (uu____2396,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2338 with
      | FStar_Pervasives_Native.Some ((uu____2438,l1,uu____2440),uu____2441)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2496 =
            let uu____2497 =
              let uu____2498 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2498  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2497
             in
          failwith uu____2496
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2534 = assign_levels level_associativity_spec op  in
    match uu____2534 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2559 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____2559) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2573  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2656 =
      let uu____2670 =
        let uu____2686 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2686  in
      FStar_List.tryFind uu____2670 (operatorInfix0ad12 ())  in
    uu____2656 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2789 =
      let uu____2803 =
        let uu____2819 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2819  in
      FStar_List.tryFind uu____2803 opinfix34  in
    uu____2789 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2875 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2875
    then (Prims.parse_int "1")
    else
      (let uu____2877 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2877
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2886 . FStar_Ident.ident -> 'Auu____2886 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2902 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2902 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2904 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2904
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2905 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2905 [".()<-"; ".[]<-"]
      | uu____2906 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2944 .
    ('Auu____2944 -> FStar_Pprint.document) ->
      'Auu____2944 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2985 = FStar_ST.op_Bang comment_stack  in
          match uu____2985 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____3048 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____3048
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3089 =
                    let uu____3090 =
                      let uu____3091 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____3091
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____3090  in
                  comments_before_pos uu____3089 print_pos lookahead_pos))
              else
                (let uu____3093 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3093))
           in
        let uu____3094 =
          let uu____3099 =
            let uu____3100 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3100  in
          let uu____3101 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3099 uu____3101  in
        match uu____3094 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3107 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3107
              else comments  in
            let uu____3113 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____3113
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____3134 = FStar_ST.op_Bang comment_stack  in
          match uu____3134 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____3226 =
                    let uu____3227 =
                      let uu____3228 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____3228  in
                    uu____3227 - lbegin  in
                  max k uu____3226  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____3231 =
                    let uu____3232 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____3233 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____3232 uu____3233  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____3231  in
                let uu____3234 =
                  let uu____3235 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____3235  in
                place_comments_until_pos (Prims.parse_int "1") uu____3234
                  pos_end doc2))
          | uu____3236 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____3245 =
                     let uu____3246 = FStar_Range.line_of_pos pos_end  in
                     uu____3246 - lbegin  in
                   max (Prims.parse_int "1") uu____3245  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____3248 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____3248)
  
let separate_map_with_comments :
  'Auu____3261 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3261 -> FStar_Pprint.document) ->
          'Auu____3261 Prims.list ->
            ('Auu____3261 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3318 x =
              match uu____3318 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3332 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3332 doc1
                     in
                  let uu____3333 =
                    let uu____3334 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3334  in
                  let uu____3335 =
                    let uu____3336 =
                      let uu____3337 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3337  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3336  in
                  (uu____3333, uu____3335)
               in
            let uu____3338 =
              let uu____3345 = FStar_List.hd xs  in
              let uu____3346 = FStar_List.tl xs  in (uu____3345, uu____3346)
               in
            match uu____3338 with
            | (x,xs1) ->
                let init1 =
                  let uu____3362 =
                    let uu____3363 =
                      let uu____3364 = extract_range x  in
                      FStar_Range.end_of_range uu____3364  in
                    FStar_Range.line_of_pos uu____3363  in
                  let uu____3365 =
                    let uu____3366 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3366  in
                  (uu____3362, uu____3365)  in
                let uu____3367 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3367
  
let separate_map_with_comments_kw :
  'Auu____3390 'Auu____3391 .
    'Auu____3390 ->
      'Auu____3390 ->
        ('Auu____3390 -> 'Auu____3391 -> FStar_Pprint.document) ->
          'Auu____3391 Prims.list ->
            ('Auu____3391 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3453 x =
              match uu____3453 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3467 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3467 doc1
                     in
                  let uu____3468 =
                    let uu____3469 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3469  in
                  let uu____3470 =
                    let uu____3471 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3471  in
                  (uu____3468, uu____3470)
               in
            let uu____3472 =
              let uu____3479 = FStar_List.hd xs  in
              let uu____3480 = FStar_List.tl xs  in (uu____3479, uu____3480)
               in
            match uu____3472 with
            | (x,xs1) ->
                let init1 =
                  let uu____3496 =
                    let uu____3497 =
                      let uu____3498 = extract_range x  in
                      FStar_Range.end_of_range uu____3498  in
                    FStar_Range.line_of_pos uu____3497  in
                  let uu____3499 = f prefix1 x  in (uu____3496, uu____3499)
                   in
                let uu____3500 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3500
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____4208)) ->
          let uu____4211 =
            let uu____4212 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4212 FStar_Util.is_upper  in
          if uu____4211
          then
            let uu____4213 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4213 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4215 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4220 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____4221 =
      let uu____4222 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4223 =
        let uu____4224 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4224  in
      FStar_Pprint.op_Hat_Hat uu____4222 uu____4223  in
    FStar_Pprint.op_Hat_Hat uu____4220 uu____4221

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4226 ->
        let uu____4227 =
          let uu____4228 = str "@ "  in
          let uu____4229 =
            let uu____4230 =
              let uu____4231 =
                let uu____4232 =
                  let uu____4233 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4233  in
                FStar_Pprint.op_Hat_Hat uu____4232 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4231  in
            FStar_Pprint.op_Hat_Hat uu____4230 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4228 uu____4229  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4227

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4236  ->
    match uu____4236 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4272 =
                match uu____4272 with
                | (kwd,arg) ->
                    let uu____4279 = str "@"  in
                    let uu____4280 =
                      let uu____4281 = str kwd  in
                      let uu____4282 =
                        let uu____4283 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4283
                         in
                      FStar_Pprint.op_Hat_Hat uu____4281 uu____4282  in
                    FStar_Pprint.op_Hat_Hat uu____4279 uu____4280
                 in
              let uu____4284 =
                let uu____4285 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____4285 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4284
           in
        let uu____4290 =
          let uu____4291 =
            let uu____4292 =
              let uu____4293 =
                let uu____4294 = str doc1  in
                let uu____4295 =
                  let uu____4296 =
                    let uu____4297 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4297  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4296  in
                FStar_Pprint.op_Hat_Hat uu____4294 uu____4295  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4293  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4292  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4291  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4290

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4301 =
          let uu____4302 = str "val"  in
          let uu____4303 =
            let uu____4304 =
              let uu____4305 = p_lident lid  in
              let uu____4306 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4305 uu____4306  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4304  in
          FStar_Pprint.op_Hat_Hat uu____4302 uu____4303  in
        let uu____4307 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4301 uu____4307
    | FStar_Parser_AST.TopLevelLet (uu____4308,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4333 =
               let uu____4334 = str "let"  in p_letlhs uu____4334 lb  in
             FStar_Pprint.group uu____4333) lbs
    | uu____4335 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___83_4350 =
          match uu___83_4350 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4358 = f x  in
              let uu____4359 =
                let uu____4360 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4360  in
              FStar_Pprint.op_Hat_Hat uu____4358 uu____4359
           in
        let uu____4361 = str "["  in
        let uu____4362 =
          let uu____4363 = p_list' l  in
          let uu____4364 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4363 uu____4364  in
        FStar_Pprint.op_Hat_Hat uu____4361 uu____4362

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4367 =
          let uu____4368 = str "open"  in
          let uu____4369 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4368 uu____4369  in
        FStar_Pprint.group uu____4367
    | FStar_Parser_AST.Include uid ->
        let uu____4371 =
          let uu____4372 = str "include"  in
          let uu____4373 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4372 uu____4373  in
        FStar_Pprint.group uu____4371
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4376 =
          let uu____4377 = str "module"  in
          let uu____4378 =
            let uu____4379 =
              let uu____4380 = p_uident uid1  in
              let uu____4381 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4380 uu____4381  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4379  in
          FStar_Pprint.op_Hat_Hat uu____4377 uu____4378  in
        let uu____4382 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4376 uu____4382
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4384 =
          let uu____4385 = str "module"  in
          let uu____4386 =
            let uu____4387 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4387  in
          FStar_Pprint.op_Hat_Hat uu____4385 uu____4386  in
        FStar_Pprint.group uu____4384
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____4420 = str "effect"  in
          let uu____4421 =
            let uu____4422 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4422  in
          FStar_Pprint.op_Hat_Hat uu____4420 uu____4421  in
        let uu____4423 =
          let uu____4424 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4424 FStar_Pprint.equals
           in
        let uu____4425 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4423 uu____4425
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____4443 =
          let uu____4444 = str "type"  in
          let uu____4445 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____4444 uu____4445  in
        let uu____4458 =
          let uu____4459 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4497 =
                    let uu____4498 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4498 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4497)) uu____4459
           in
        FStar_Pprint.op_Hat_Hat uu____4443 uu____4458
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4514 = str "let"  in
          let uu____4515 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4514 uu____4515  in
        let uu____4516 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4516 p_letbinding lbs
          (fun uu____4524  ->
             match uu____4524 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4533 = str "val"  in
        let uu____4534 =
          let uu____4535 =
            let uu____4536 = p_lident lid  in
            let uu____4537 =
              let uu____4538 =
                let uu____4539 =
                  let uu____4540 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4540  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4539  in
              FStar_Pprint.group uu____4538  in
            FStar_Pprint.op_Hat_Hat uu____4536 uu____4537  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4535  in
        FStar_Pprint.op_Hat_Hat uu____4533 uu____4534
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4544 =
            let uu____4545 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4545 FStar_Util.is_upper  in
          if uu____4544
          then FStar_Pprint.empty
          else
            (let uu____4547 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4547 FStar_Pprint.space)
           in
        let uu____4548 =
          let uu____4549 = p_ident id1  in
          let uu____4550 =
            let uu____4551 =
              let uu____4552 =
                let uu____4553 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4553  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4552  in
            FStar_Pprint.group uu____4551  in
          FStar_Pprint.op_Hat_Hat uu____4549 uu____4550  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4548
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4560 = str "exception"  in
        let uu____4561 =
          let uu____4562 =
            let uu____4563 = p_uident uid  in
            let uu____4564 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4568 =
                     let uu____4569 = str "of"  in
                     let uu____4570 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4569 uu____4570  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4568) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4563 uu____4564  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4562  in
        FStar_Pprint.op_Hat_Hat uu____4560 uu____4561
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4572 = str "new_effect"  in
        let uu____4573 =
          let uu____4574 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4574  in
        FStar_Pprint.op_Hat_Hat uu____4572 uu____4573
    | FStar_Parser_AST.SubEffect se ->
        let uu____4576 = str "sub_effect"  in
        let uu____4577 =
          let uu____4578 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4578  in
        FStar_Pprint.op_Hat_Hat uu____4576 uu____4577
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4581 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4581 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4582 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4583) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4606 = str "%splice"  in
        let uu____4607 =
          let uu____4608 =
            let uu____4609 = str ";"  in p_list p_uident uu____4609 ids  in
          let uu____4610 =
            let uu____4611 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4611  in
          FStar_Pprint.op_Hat_Hat uu____4608 uu____4610  in
        FStar_Pprint.op_Hat_Hat uu____4606 uu____4607

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___84_4612  ->
    match uu___84_4612 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4614 = str "#set-options"  in
        let uu____4615 =
          let uu____4616 =
            let uu____4617 = str s  in FStar_Pprint.dquotes uu____4617  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4616  in
        FStar_Pprint.op_Hat_Hat uu____4614 uu____4615
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4621 = str "#reset-options"  in
        let uu____4622 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4626 =
                 let uu____4627 = str s  in FStar_Pprint.dquotes uu____4627
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4626) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4621 uu____4622
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
    fun uu____4656  ->
      match uu____4656 with
      | (typedecl,fsdoc_opt) ->
          let uu____4669 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4669 with
           | (decl,body) ->
               let uu____4687 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4687)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___85_4689  ->
      match uu___85_4689 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4719 = FStar_Pprint.empty  in
          let uu____4720 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4720, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4741 =
            let uu____4742 = p_typ false false t  in jump2 uu____4742  in
          let uu____4743 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4743, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4797 =
            match uu____4797 with
            | (lid1,t,doc_opt) ->
                let uu____4813 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4813
             in
          let p_fields uu____4829 =
            let uu____4830 =
              let uu____4831 =
                let uu____4832 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4832 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4831  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4830  in
          let uu____4841 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4841, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4902 =
            match uu____4902 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4928 =
                    let uu____4929 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4929  in
                  FStar_Range.extend_to_end_of_line uu____4928  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4955 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4968 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4968,
            ((fun uu____4974  ->
                let uu____4975 = datacon_doc ()  in jump2 uu____4975)))

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
  fun uu____4976  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4976 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____5010 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____5010  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____5012 =
                        let uu____5015 =
                          let uu____5018 = p_fsdoc fsdoc  in
                          let uu____5019 =
                            let uu____5022 = cont lid_doc  in [uu____5022]
                             in
                          uu____5018 :: uu____5019  in
                        kw :: uu____5015  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____5012
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____5027 =
                        let uu____5028 =
                          let uu____5029 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5029 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5028
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5027
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5044 =
                          let uu____5045 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5045  in
                        prefix2 uu____5044 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5047  ->
      match uu____5047 with
      | (lid,t,doc_opt) ->
          let uu____5063 =
            let uu____5064 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5065 =
              let uu____5066 = p_lident lid  in
              let uu____5067 =
                let uu____5068 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5068  in
              FStar_Pprint.op_Hat_Hat uu____5066 uu____5067  in
            FStar_Pprint.op_Hat_Hat uu____5064 uu____5065  in
          FStar_Pprint.group uu____5063

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____5069  ->
    match uu____5069 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5097 =
            let uu____5098 =
              let uu____5099 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5099  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5098  in
          FStar_Pprint.group uu____5097  in
        let uu____5100 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5101 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5105 =
                 let uu____5106 =
                   let uu____5107 =
                     let uu____5108 =
                       let uu____5109 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5109
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5108  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5107  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5106  in
               FStar_Pprint.group uu____5105) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5100 uu____5101

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5111  ->
      match uu____5111 with
      | (pat,uu____5117) ->
          let uu____5118 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5137 =
                  let uu____5138 =
                    let uu____5139 =
                      let uu____5140 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5140
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5139  in
                  FStar_Pprint.group uu____5138  in
                (pat1, uu____5137)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5152 =
                  let uu____5153 =
                    let uu____5154 =
                      let uu____5155 =
                        let uu____5156 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5156
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5155
                       in
                    FStar_Pprint.group uu____5154  in
                  let uu____5157 =
                    let uu____5158 =
                      let uu____5159 = str "by"  in
                      let uu____5160 =
                        let uu____5161 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5161
                         in
                      FStar_Pprint.op_Hat_Hat uu____5159 uu____5160  in
                    FStar_Pprint.group uu____5158  in
                  FStar_Pprint.op_Hat_Hat uu____5153 uu____5157  in
                (pat1, uu____5152)
            | uu____5162 -> (pat, FStar_Pprint.empty)  in
          (match uu____5118 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5166);
                       FStar_Parser_AST.prange = uu____5167;_},pats)
                    ->
                    let uu____5177 =
                      let uu____5178 =
                        let uu____5179 =
                          let uu____5180 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5180  in
                        FStar_Pprint.group uu____5179  in
                      let uu____5181 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5178 uu____5181  in
                    prefix2_nonempty uu____5177 ascr_doc
                | uu____5182 ->
                    let uu____5183 =
                      let uu____5184 =
                        let uu____5185 =
                          let uu____5186 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5186  in
                        FStar_Pprint.group uu____5185  in
                      FStar_Pprint.op_Hat_Hat uu____5184 ascr_doc  in
                    FStar_Pprint.group uu____5183))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5188  ->
      match uu____5188 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____5197 =
            let uu____5198 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5198  in
          let uu____5199 =
            let uu____5200 =
              let uu____5201 =
                let uu____5202 =
                  let uu____5203 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5203  in
                FStar_Pprint.group uu____5202  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5201  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____5200  in
          FStar_Pprint.ifflat uu____5197 uu____5199

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___86_5204  ->
    match uu___86_5204 with
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
        let uu____5229 = p_uident uid  in
        let uu____5230 = p_binders true bs  in
        let uu____5231 =
          let uu____5232 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5232  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5229 uu____5230 uu____5231

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
          let uu____5242 =
            let uu____5243 =
              let uu____5244 =
                let uu____5245 = p_uident uid  in
                let uu____5246 = p_binders true bs  in
                let uu____5247 =
                  let uu____5248 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5248  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5245 uu____5246 uu____5247
                 in
              FStar_Pprint.group uu____5244  in
            let uu____5249 =
              let uu____5250 = str "with"  in
              let uu____5251 =
                let uu____5252 =
                  let uu____5253 =
                    let uu____5254 =
                      let uu____5255 =
                        let uu____5256 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5256
                         in
                      separate_map_last uu____5255 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5254  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5253  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5252  in
              FStar_Pprint.op_Hat_Hat uu____5250 uu____5251  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5243 uu____5249  in
          braces_with_nesting uu____5242

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
          let uu____5287 =
            let uu____5288 = p_lident lid  in
            let uu____5289 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5288 uu____5289  in
          let uu____5290 = p_simpleTerm ps false e  in
          prefix2 uu____5287 uu____5290
      | uu____5291 ->
          let uu____5292 =
            let uu____5293 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5293
             in
          failwith uu____5292

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5355 =
        match uu____5355 with
        | (kwd,t) ->
            let uu____5362 =
              let uu____5363 = str kwd  in
              let uu____5364 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5363 uu____5364  in
            let uu____5365 = p_simpleTerm ps false t  in
            prefix2 uu____5362 uu____5365
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5370 =
      let uu____5371 =
        let uu____5372 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5373 =
          let uu____5374 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5374  in
        FStar_Pprint.op_Hat_Hat uu____5372 uu____5373  in
      let uu____5375 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5371 uu____5375  in
    let uu____5376 =
      let uu____5377 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5377  in
    FStar_Pprint.op_Hat_Hat uu____5370 uu____5376

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___87_5378  ->
    match uu___87_5378 with
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
    | uu____5380 ->
        let uu____5381 =
          let uu____5382 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5382  in
        FStar_Pprint.op_Hat_Hat uu____5381 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___88_5385  ->
    match uu___88_5385 with
    | FStar_Parser_AST.Rec  ->
        let uu____5386 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5386
    | FStar_Parser_AST.Mutable  ->
        let uu____5387 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5387
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___89_5388  ->
    match uu___89_5388 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____5393 =
          let uu____5394 =
            let uu____5395 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____5395  in
          FStar_Pprint.separate_map uu____5394 p_tuplePattern pats  in
        FStar_Pprint.group uu____5393
    | uu____5396 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____5403 =
          let uu____5404 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____5404 p_constructorPattern pats  in
        FStar_Pprint.group uu____5403
    | uu____5405 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____5408;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____5413 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____5414 = p_constructorPattern hd1  in
        let uu____5415 = p_constructorPattern tl1  in
        infix0 uu____5413 uu____5414 uu____5415
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____5417;_},pats)
        ->
        let uu____5423 = p_quident uid  in
        let uu____5424 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5423 uu____5424
    | uu____5425 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5441;
               FStar_Parser_AST.blevel = uu____5442;
               FStar_Parser_AST.aqual = uu____5443;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5449 =
               let uu____5450 = p_ident lid  in
               p_refinement aqual uu____5450 t1 phi  in
             soft_parens_with_nesting uu____5449
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5452;
               FStar_Parser_AST.blevel = uu____5453;
               FStar_Parser_AST.aqual = uu____5454;_},phi))
             ->
             let uu____5456 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____5456
         | uu____5457 ->
             let uu____5462 =
               let uu____5463 = p_tuplePattern pat  in
               let uu____5464 =
                 let uu____5465 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5465
                  in
               FStar_Pprint.op_Hat_Hat uu____5463 uu____5464  in
             soft_parens_with_nesting uu____5462)
    | FStar_Parser_AST.PatList pats ->
        let uu____5469 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5469 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5486 =
          match uu____5486 with
          | (lid,pat) ->
              let uu____5493 = p_qlident lid  in
              let uu____5494 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5493 uu____5494
           in
        let uu____5495 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5495
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5505 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5506 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5507 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5505 uu____5506 uu____5507
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5516 =
          let uu____5517 =
            let uu____5518 =
              let uu____5519 = FStar_Ident.text_of_id op  in str uu____5519
               in
            let uu____5520 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5518 uu____5520  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5517  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5516
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5528 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5529 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5528 uu____5529
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5531 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5534;
           FStar_Parser_AST.prange = uu____5535;_},uu____5536)
        ->
        let uu____5541 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5541
    | FStar_Parser_AST.PatTuple (uu____5542,false ) ->
        let uu____5547 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5547
    | uu____5548 ->
        let uu____5549 =
          let uu____5550 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5550  in
        failwith uu____5549

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5552;_},uu____5553)
        -> true
    | uu____5558 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5562 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5563 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5562 uu____5563
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5570;
                   FStar_Parser_AST.blevel = uu____5571;
                   FStar_Parser_AST.aqual = uu____5572;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5574 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5574 t1 phi
            | uu____5575 ->
                let t' =
                  let uu____5577 = is_typ_tuple t  in
                  if uu____5577
                  then
                    let uu____5578 = p_tmFormula t  in
                    soft_parens_with_nesting uu____5578
                  else p_tmFormula t  in
                let uu____5580 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5581 =
                  let uu____5582 = p_lident lid  in
                  let uu____5583 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____5582 uu____5583  in
                FStar_Pprint.op_Hat_Hat uu____5580 uu____5581
             in
          if is_atomic
          then
            let uu____5584 =
              let uu____5585 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5585  in
            FStar_Pprint.group uu____5584
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5587 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5594;
                  FStar_Parser_AST.blevel = uu____5595;
                  FStar_Parser_AST.aqual = uu____5596;_},phi)
               ->
               if is_atomic
               then
                 let uu____5598 =
                   let uu____5599 =
                     let uu____5600 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5600 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5599  in
                 FStar_Pprint.group uu____5598
               else
                 (let uu____5602 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5602)
           | uu____5603 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____5612 -> false
            | FStar_Parser_AST.App uu____5623 -> false
            | FStar_Parser_AST.Op uu____5630 -> false
            | uu____5637 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____5641 =
            let uu____5642 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____5643 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____5642 uu____5643  in
          let uu____5644 =
            let uu____5645 = p_appTerm t  in
            let uu____5646 =
              let uu____5647 =
                let uu____5648 =
                  let uu____5649 = soft_braces_with_nesting_tight phi1  in
                  let uu____5650 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____5649 uu____5650  in
                FStar_Pprint.group uu____5648  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____5647
               in
            FStar_Pprint.op_Hat_Hat uu____5645 uu____5646  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5641 uu____5644

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____5661 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____5661

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5666 = FStar_Ident.text_of_id lid  in str uu____5666)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5669 = FStar_Ident.text_of_lid lid  in str uu____5669)

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
            let uu____5687 =
              let uu____5688 =
                let uu____5689 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5689 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5688  in
            let uu____5690 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5687 uu____5690
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5694 =
              let uu____5695 =
                let uu____5696 =
                  let uu____5697 = p_lident x  in
                  let uu____5698 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5697 uu____5698  in
                let uu____5699 =
                  let uu____5700 = p_noSeqTerm true false e1  in
                  let uu____5701 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5700 uu____5701  in
                op_Hat_Slash_Plus_Hat uu____5696 uu____5699  in
              FStar_Pprint.group uu____5695  in
            let uu____5702 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5694 uu____5702
        | uu____5703 ->
            let uu____5704 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5704

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
            let uu____5715 =
              let uu____5716 = p_tmIff e1  in
              let uu____5717 =
                let uu____5718 =
                  let uu____5719 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5719
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5718  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5716 uu____5717  in
            FStar_Pprint.group uu____5715
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5725 =
              let uu____5726 = p_tmIff e1  in
              let uu____5727 =
                let uu____5728 =
                  let uu____5729 =
                    let uu____5730 = p_typ false false t  in
                    let uu____5731 =
                      let uu____5732 = str "by"  in
                      let uu____5733 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5732 uu____5733  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5730 uu____5731  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5729
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5728  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5726 uu____5727  in
            FStar_Pprint.group uu____5725
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5734;_},e1::e2::e3::[])
            ->
            let uu____5740 =
              let uu____5741 =
                let uu____5742 =
                  let uu____5743 = p_atomicTermNotQUident e1  in
                  let uu____5744 =
                    let uu____5745 =
                      let uu____5746 =
                        let uu____5747 = p_term false false e2  in
                        soft_parens_with_nesting uu____5747  in
                      let uu____5748 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5746 uu____5748  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5745  in
                  FStar_Pprint.op_Hat_Hat uu____5743 uu____5744  in
                FStar_Pprint.group uu____5742  in
              let uu____5749 =
                let uu____5750 = p_noSeqTerm ps pb e3  in jump2 uu____5750
                 in
              FStar_Pprint.op_Hat_Hat uu____5741 uu____5749  in
            FStar_Pprint.group uu____5740
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5751;_},e1::e2::e3::[])
            ->
            let uu____5757 =
              let uu____5758 =
                let uu____5759 =
                  let uu____5760 = p_atomicTermNotQUident e1  in
                  let uu____5761 =
                    let uu____5762 =
                      let uu____5763 =
                        let uu____5764 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5764  in
                      let uu____5765 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5763 uu____5765  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5762  in
                  FStar_Pprint.op_Hat_Hat uu____5760 uu____5761  in
                FStar_Pprint.group uu____5759  in
              let uu____5766 =
                let uu____5767 = p_noSeqTerm ps pb e3  in jump2 uu____5767
                 in
              FStar_Pprint.op_Hat_Hat uu____5758 uu____5766  in
            FStar_Pprint.group uu____5757
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5775 =
              let uu____5776 = str "requires"  in
              let uu____5777 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5776 uu____5777  in
            FStar_Pprint.group uu____5775
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5785 =
              let uu____5786 = str "ensures"  in
              let uu____5787 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5786 uu____5787  in
            FStar_Pprint.group uu____5785
        | FStar_Parser_AST.Attributes es ->
            let uu____5791 =
              let uu____5792 = str "attributes"  in
              let uu____5793 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5792 uu____5793  in
            FStar_Pprint.group uu____5791
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5797 =
                let uu____5798 =
                  let uu____5799 = str "if"  in
                  let uu____5800 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5799 uu____5800  in
                let uu____5801 =
                  let uu____5802 = str "then"  in
                  let uu____5803 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5802 uu____5803  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5798 uu____5801  in
              FStar_Pprint.group uu____5797
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5806,uu____5807,e31) when
                     is_unit e31 ->
                     let uu____5809 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5809
                 | uu____5810 -> p_noSeqTerm false false e2  in
               let uu____5811 =
                 let uu____5812 =
                   let uu____5813 = str "if"  in
                   let uu____5814 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5813 uu____5814  in
                 let uu____5815 =
                   let uu____5816 =
                     let uu____5817 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5817 e2_doc  in
                   let uu____5818 =
                     let uu____5819 = str "else"  in
                     let uu____5820 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5819 uu____5820  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5816 uu____5818  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5812 uu____5815  in
               FStar_Pprint.group uu____5811)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5843 =
              let uu____5844 =
                let uu____5845 =
                  let uu____5846 = str "try"  in
                  let uu____5847 = p_noSeqTerm false false e1  in
                  prefix2 uu____5846 uu____5847  in
                let uu____5848 =
                  let uu____5849 = str "with"  in
                  let uu____5850 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5849 uu____5850  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5845 uu____5848  in
              FStar_Pprint.group uu____5844  in
            let uu____5859 = paren_if (ps || pb)  in uu____5859 uu____5843
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5886 =
              let uu____5887 =
                let uu____5888 =
                  let uu____5889 = str "match"  in
                  let uu____5890 = p_noSeqTerm false false e1  in
                  let uu____5891 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5889 uu____5890 uu____5891
                   in
                let uu____5892 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5888 uu____5892  in
              FStar_Pprint.group uu____5887  in
            let uu____5901 = paren_if (ps || pb)  in uu____5901 uu____5886
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5908 =
              let uu____5909 =
                let uu____5910 =
                  let uu____5911 = str "let open"  in
                  let uu____5912 = p_quident uid  in
                  let uu____5913 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5911 uu____5912 uu____5913
                   in
                let uu____5914 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5910 uu____5914  in
              FStar_Pprint.group uu____5909  in
            let uu____5915 = paren_if ps  in uu____5915 uu____5908
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5979 is_last =
              match uu____5979 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____6012 =
                          let uu____6013 = str "let"  in
                          let uu____6014 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6013 uu____6014
                           in
                        FStar_Pprint.group uu____6012
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____6015 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____6020 =
                    if is_last
                    then
                      let uu____6021 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____6022 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____6021 doc_expr uu____6022
                    else
                      (let uu____6024 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____6024)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____6020
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6070 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6070
                     else
                       (let uu____6078 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6078)) lbs
               in
            let lbs_doc =
              let uu____6086 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6086  in
            let uu____6087 =
              let uu____6088 =
                let uu____6089 =
                  let uu____6090 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6090
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6089  in
              FStar_Pprint.group uu____6088  in
            let uu____6091 = paren_if ps  in uu____6091 uu____6087
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6098;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6101;
                                                             FStar_Parser_AST.level
                                                               = uu____6102;_})
            when matches_var maybe_x x ->
            let uu____6129 =
              let uu____6130 =
                let uu____6131 = str "function"  in
                let uu____6132 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6131 uu____6132  in
              FStar_Pprint.group uu____6130  in
            let uu____6141 = paren_if (ps || pb)  in uu____6141 uu____6129
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____6147 =
              let uu____6148 = str "quote"  in
              let uu____6149 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6148 uu____6149  in
            FStar_Pprint.group uu____6147
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____6151 =
              let uu____6152 = str "`"  in
              let uu____6153 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6152 uu____6153  in
            FStar_Pprint.group uu____6151
        | FStar_Parser_AST.VQuote e1 ->
            let uu____6155 =
              let uu____6156 = str "%`"  in
              let uu____6157 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6156 uu____6157  in
            FStar_Pprint.group uu____6155
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____6159 =
              let uu____6160 = str "`#"  in
              let uu____6161 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6160 uu____6161  in
            FStar_Pprint.group uu____6159
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____6163 =
              let uu____6164 = str "`@"  in
              let uu____6165 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6164 uu____6165  in
            FStar_Pprint.group uu____6163
        | uu____6166 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___90_6167  ->
    match uu___90_6167 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6179 =
          let uu____6180 = str "[@"  in
          let uu____6181 =
            let uu____6182 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____6183 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6182 uu____6183  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6180 uu____6181  in
        FStar_Pprint.group uu____6179

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
                 let uu____6209 =
                   let uu____6210 =
                     let uu____6211 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6211 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6210 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6209 term_doc
             | pats ->
                 let uu____6217 =
                   let uu____6218 =
                     let uu____6219 =
                       let uu____6220 =
                         let uu____6221 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6221
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6220 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6222 = p_trigger trigger  in
                     prefix2 uu____6219 uu____6222  in
                   FStar_Pprint.group uu____6218  in
                 prefix2 uu____6217 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6242 =
                   let uu____6243 =
                     let uu____6244 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6244 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6243 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6242 term_doc
             | pats ->
                 let uu____6250 =
                   let uu____6251 =
                     let uu____6252 =
                       let uu____6253 =
                         let uu____6254 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6254
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6253 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6255 = p_trigger trigger  in
                     prefix2 uu____6252 uu____6255  in
                   FStar_Pprint.group uu____6251  in
                 prefix2 uu____6250 term_doc)
        | uu____6256 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6258 -> str "forall"
    | FStar_Parser_AST.QExists uu____6271 -> str "exists"
    | uu____6284 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___91_6285  ->
    match uu___91_6285 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6297 =
          let uu____6298 =
            let uu____6299 =
              let uu____6300 = str "pattern"  in
              let uu____6301 =
                let uu____6302 =
                  let uu____6303 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____6303
                   in
                FStar_Pprint.op_Hat_Hat uu____6302 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6300 uu____6301  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6299  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6298  in
        FStar_Pprint.group uu____6297

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6309 = str "\\/"  in
    FStar_Pprint.separate_map uu____6309 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6315 =
      let uu____6316 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____6316 p_appTerm pats  in
    FStar_Pprint.group uu____6315

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____6326 =
              let uu____6327 =
                let uu____6328 = str "fun"  in
                let uu____6329 =
                  let uu____6330 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6330
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____6328 uu____6329  in
              let uu____6331 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____6327 uu____6331  in
            let uu____6332 = paren_if ps  in uu____6332 uu____6326
        | uu____6337 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____6341  ->
      match uu____6341 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____6364 =
                    let uu____6365 =
                      let uu____6366 =
                        let uu____6367 = p_tuplePattern p  in
                        let uu____6368 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____6367 uu____6368  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6366
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6365  in
                  FStar_Pprint.group uu____6364
              | FStar_Pervasives_Native.Some f ->
                  let uu____6370 =
                    let uu____6371 =
                      let uu____6372 =
                        let uu____6373 =
                          let uu____6374 =
                            let uu____6375 = p_tuplePattern p  in
                            let uu____6376 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6375
                              uu____6376
                             in
                          FStar_Pprint.group uu____6374  in
                        let uu____6377 =
                          let uu____6378 =
                            let uu____6381 = p_tmFormula f  in
                            [uu____6381; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____6378  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6373 uu____6377
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6372
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6371  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____6370
               in
            let uu____6382 =
              let uu____6383 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____6383  in
            FStar_Pprint.group uu____6382  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____6392 =
                      let uu____6393 =
                        let uu____6394 =
                          let uu____6395 =
                            let uu____6396 =
                              let uu____6397 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____6397  in
                            FStar_Pprint.separate_map uu____6396
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6395
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6394
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6393  in
                    FStar_Pprint.group uu____6392
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6398 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____6400;_},e1::e2::[])
        ->
        let uu____6405 = str "<==>"  in
        let uu____6406 = p_tmImplies e1  in
        let uu____6407 = p_tmIff e2  in
        infix0 uu____6405 uu____6406 uu____6407
    | uu____6408 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____6410;_},e1::e2::[])
        ->
        let uu____6415 = str "==>"  in
        let uu____6416 = p_tmArrow p_tmFormula e1  in
        let uu____6417 = p_tmImplies e2  in
        infix0 uu____6415 uu____6416 uu____6417
    | uu____6418 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____6426 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____6426 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____6447 ->
               let uu____6448 =
                 let uu____6449 =
                   let uu____6450 =
                     let uu____6451 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6451
                      in
                   FStar_Pprint.separate uu____6450 terms  in
                 let uu____6452 =
                   let uu____6453 =
                     let uu____6454 =
                       let uu____6455 =
                         let uu____6456 =
                           let uu____6457 =
                             let uu____6458 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____6458
                              in
                           FStar_Pprint.separate uu____6457 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____6456 last_op  in
                       let uu____6459 =
                         let uu____6460 =
                           let uu____6461 =
                             let uu____6462 =
                               let uu____6463 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6463
                                in
                             FStar_Pprint.separate uu____6462 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____6461 last_op  in
                         jump2 uu____6460  in
                       FStar_Pprint.ifflat uu____6455 uu____6459  in
                     FStar_Pprint.group uu____6454  in
                   let uu____6464 = FStar_List.hd last1  in
                   prefix2 uu____6453 uu____6464  in
                 FStar_Pprint.ifflat uu____6449 uu____6452  in
               FStar_Pprint.group uu____6448)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____6477 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____6482 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____6477 uu____6482
      | uu____6485 -> let uu____6486 = p_Tm e  in [uu____6486]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____6489 =
        let uu____6490 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____6490 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6489  in
    let disj =
      let uu____6492 =
        let uu____6493 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____6493 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6492  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6512;_},e1::e2::[])
        ->
        let uu____6517 = p_tmDisjunction e1  in
        let uu____6522 = let uu____6527 = p_tmConjunction e2  in [uu____6527]
           in
        FStar_List.append uu____6517 uu____6522
    | uu____6536 -> let uu____6537 = p_tmConjunction e  in [uu____6537]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6547;_},e1::e2::[])
        ->
        let uu____6552 = p_tmConjunction e1  in
        let uu____6555 = let uu____6558 = p_tmTuple e2  in [uu____6558]  in
        FStar_List.append uu____6552 uu____6555
    | uu____6559 -> let uu____6560 = p_tmTuple e  in [uu____6560]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____6577 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____6577
          (fun uu____6585  ->
             match uu____6585 with | (e1,uu____6591) -> p_tmEq e1) args
    | uu____6592 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____6597 =
             let uu____6598 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6598  in
           FStar_Pprint.group uu____6597)

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
               (let uu____6661 = FStar_Ident.text_of_id op  in
                uu____6661 = "="))
              ||
              (let uu____6663 = FStar_Ident.text_of_id op  in
               uu____6663 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6665 = levels op1  in
            (match uu____6665 with
             | (left1,mine,right1) ->
                 let uu____6675 =
                   let uu____6676 = FStar_All.pipe_left str op1  in
                   let uu____6677 = p_tmEqWith' p_X left1 e1  in
                   let uu____6678 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6676 uu____6677 uu____6678  in
                 paren_if_gt curr mine uu____6675)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6679;_},e1::e2::[])
            ->
            let uu____6684 =
              let uu____6685 = p_tmEqWith p_X e1  in
              let uu____6686 =
                let uu____6687 =
                  let uu____6688 =
                    let uu____6689 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6689  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6688  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6687  in
              FStar_Pprint.op_Hat_Hat uu____6685 uu____6686  in
            FStar_Pprint.group uu____6684
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6690;_},e1::[])
            ->
            let uu____6694 = levels "-"  in
            (match uu____6694 with
             | (left1,mine,right1) ->
                 let uu____6704 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6704)
        | uu____6705 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____6777)::(e2,uu____6779)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6799 = is_list e  in Prims.op_Negation uu____6799)
              ->
              let op = "::"  in
              let uu____6801 = levels op  in
              (match uu____6801 with
               | (left1,mine,right1) ->
                   let uu____6811 =
                     let uu____6812 = str op  in
                     let uu____6813 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6814 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6812 uu____6813 uu____6814  in
                   paren_if_gt curr mine uu____6811)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6822 = levels op  in
              (match uu____6822 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6838 = p_binder false b  in
                     let uu____6839 =
                       let uu____6840 =
                         let uu____6841 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6841 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6840
                        in
                     FStar_Pprint.op_Hat_Hat uu____6838 uu____6839  in
                   let uu____6842 =
                     let uu____6843 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6844 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6843 uu____6844  in
                   paren_if_gt curr mine uu____6842)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6845;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6874 = levels op  in
              (match uu____6874 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6884 = str op  in
                     let uu____6885 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6886 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6884 uu____6885 uu____6886
                   else
                     (let uu____6888 =
                        let uu____6889 = str op  in
                        let uu____6890 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6891 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6889 uu____6890 uu____6891  in
                      paren_if_gt curr mine uu____6888))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6898 = levels op1  in
              (match uu____6898 with
               | (left1,mine,right1) ->
                   let uu____6908 =
                     let uu____6909 = str op1  in
                     let uu____6910 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6911 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6909 uu____6910 uu____6911  in
                   paren_if_gt curr mine uu____6908)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6930 =
                let uu____6931 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6932 =
                  let uu____6933 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6933 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6931 uu____6932  in
              braces_with_nesting uu____6930
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6938;_},e1::[])
              ->
              let uu____6942 =
                let uu____6943 = str "~"  in
                let uu____6944 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6943 uu____6944  in
              FStar_Pprint.group uu____6942
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6946;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6952 = levels op  in
                   (match uu____6952 with
                    | (left1,mine,right1) ->
                        let uu____6962 =
                          let uu____6963 = str op  in
                          let uu____6964 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6965 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6963 uu____6964 uu____6965  in
                        paren_if_gt curr mine uu____6962)
               | uu____6966 -> p_X e)
          | uu____6967 -> p_X e

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
        let uu____6974 =
          let uu____6975 = p_lident lid  in
          let uu____6976 =
            let uu____6977 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6977  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6975 uu____6976  in
        FStar_Pprint.group uu____6974
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6980 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6982 = p_appTerm e  in
    let uu____6983 =
      let uu____6984 =
        let uu____6985 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6985 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6984  in
    FStar_Pprint.op_Hat_Hat uu____6982 uu____6983

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6990 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6990 t phi
      | FStar_Parser_AST.TAnnotated uu____6991 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6996 ->
          let uu____6997 =
            let uu____6998 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6998
             in
          failwith uu____6997
      | FStar_Parser_AST.TVariable uu____6999 ->
          let uu____7000 =
            let uu____7001 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7001
             in
          failwith uu____7000
      | FStar_Parser_AST.NoName uu____7002 ->
          let uu____7003 =
            let uu____7004 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____7004
             in
          failwith uu____7003

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____7006  ->
      match uu____7006 with
      | (lid,e) ->
          let uu____7013 =
            let uu____7014 = p_qlident lid  in
            let uu____7015 =
              let uu____7016 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____7016
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____7014 uu____7015  in
          FStar_Pprint.group uu____7013

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____7018 when is_general_application e ->
        let uu____7025 = head_and_args e  in
        (match uu____7025 with
         | (head1,args) ->
             let uu____7050 =
               let uu____7061 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____7061
               then
                 let uu____7095 =
                   FStar_Util.take
                     (fun uu____7119  ->
                        match uu____7119 with
                        | (uu____7124,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____7095 with
                 | (fs_typ_args,args1) ->
                     let uu____7162 =
                       let uu____7163 = p_indexingTerm head1  in
                       let uu____7164 =
                         let uu____7165 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____7165 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____7163 uu____7164  in
                     (uu____7162, args1)
               else
                 (let uu____7177 = p_indexingTerm head1  in
                  (uu____7177, args))
                in
             (match uu____7050 with
              | (head_doc,args1) ->
                  let uu____7198 =
                    let uu____7199 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____7199 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____7198))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____7219 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____7219)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____7237 =
               let uu____7238 = p_quident lid  in
               let uu____7239 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____7238 uu____7239  in
             FStar_Pprint.group uu____7237
         | hd1::tl1 ->
             let uu____7256 =
               let uu____7257 =
                 let uu____7258 =
                   let uu____7259 = p_quident lid  in
                   let uu____7260 = p_argTerm hd1  in
                   prefix2 uu____7259 uu____7260  in
                 FStar_Pprint.group uu____7258  in
               let uu____7261 =
                 let uu____7262 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____7262  in
               FStar_Pprint.op_Hat_Hat uu____7257 uu____7261  in
             FStar_Pprint.group uu____7256)
    | uu____7267 -> p_indexingTerm e

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
         (let uu____7276 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____7276 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____7278 = str "#"  in
        let uu____7279 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____7278 uu____7279
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____7281  ->
    match uu____7281 with | (e,uu____7287) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____7292;_},e1::e2::[])
          ->
          let uu____7297 =
            let uu____7298 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7299 =
              let uu____7300 =
                let uu____7301 = p_term false false e2  in
                soft_parens_with_nesting uu____7301  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7300  in
            FStar_Pprint.op_Hat_Hat uu____7298 uu____7299  in
          FStar_Pprint.group uu____7297
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____7302;_},e1::e2::[])
          ->
          let uu____7307 =
            let uu____7308 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7309 =
              let uu____7310 =
                let uu____7311 = p_term false false e2  in
                soft_brackets_with_nesting uu____7311  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7310  in
            FStar_Pprint.op_Hat_Hat uu____7308 uu____7309  in
          FStar_Pprint.group uu____7307
      | uu____7312 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____7317 = p_quident lid  in
        let uu____7318 =
          let uu____7319 =
            let uu____7320 = p_term false false e1  in
            soft_parens_with_nesting uu____7320  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7319  in
        FStar_Pprint.op_Hat_Hat uu____7317 uu____7318
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7326 =
          let uu____7327 = FStar_Ident.text_of_id op  in str uu____7327  in
        let uu____7328 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____7326 uu____7328
    | uu____7329 -> p_atomicTermNotQUident e

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
         | uu____7336 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7343 =
          let uu____7344 = FStar_Ident.text_of_id op  in str uu____7344  in
        let uu____7345 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____7343 uu____7345
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____7349 =
          let uu____7350 =
            let uu____7351 =
              let uu____7352 = FStar_Ident.text_of_id op  in str uu____7352
               in
            let uu____7353 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____7351 uu____7353  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7350  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7349
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____7368 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____7369 =
          let uu____7370 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____7371 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____7370 p_tmEq uu____7371  in
        let uu____7378 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7368 uu____7369 uu____7378
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____7381 =
          let uu____7382 = p_atomicTermNotQUident e1  in
          let uu____7383 =
            let uu____7384 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7384  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____7382 uu____7383
           in
        FStar_Pprint.group uu____7381
    | uu____7385 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____7390 = p_quident constr_lid  in
        let uu____7391 =
          let uu____7392 =
            let uu____7393 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7393  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7392  in
        FStar_Pprint.op_Hat_Hat uu____7390 uu____7391
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____7395 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____7395 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____7397 = p_term false false e1  in
        soft_parens_with_nesting uu____7397
    | uu____7398 when is_array e ->
        let es = extract_from_list e  in
        let uu____7402 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____7403 =
          let uu____7404 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____7404
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____7407 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7402 uu____7403 uu____7407
    | uu____7408 when is_list e ->
        let uu____7409 =
          let uu____7410 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7411 = extract_from_list e  in
          separate_map_or_flow_last uu____7410
            (fun ps  -> p_noSeqTerm ps false) uu____7411
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____7409 FStar_Pprint.rbracket
    | uu____7416 when is_lex_list e ->
        let uu____7417 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____7418 =
          let uu____7419 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7420 = extract_from_list e  in
          separate_map_or_flow_last uu____7419
            (fun ps  -> p_noSeqTerm ps false) uu____7420
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7417 uu____7418 FStar_Pprint.rbracket
    | uu____7425 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____7429 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____7430 =
          let uu____7431 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____7431 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7429 uu____7430 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____7435 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____7436 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____7435 uu____7436
    | FStar_Parser_AST.Op (op,args) when
        let uu____7443 = handleable_op op args  in
        Prims.op_Negation uu____7443 ->
        let uu____7444 =
          let uu____7445 =
            let uu____7446 = FStar_Ident.text_of_id op  in
            let uu____7447 =
              let uu____7448 =
                let uu____7449 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____7449
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____7448  in
            Prims.strcat uu____7446 uu____7447  in
          Prims.strcat "Operation " uu____7445  in
        failwith uu____7444
    | FStar_Parser_AST.Uvar uu____7450 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____7451 = p_term false false e  in
        soft_parens_with_nesting uu____7451
    | FStar_Parser_AST.Const uu____7452 ->
        let uu____7453 = p_term false false e  in
        soft_parens_with_nesting uu____7453
    | FStar_Parser_AST.Op uu____7454 ->
        let uu____7461 = p_term false false e  in
        soft_parens_with_nesting uu____7461
    | FStar_Parser_AST.Tvar uu____7462 ->
        let uu____7463 = p_term false false e  in
        soft_parens_with_nesting uu____7463
    | FStar_Parser_AST.Var uu____7464 ->
        let uu____7465 = p_term false false e  in
        soft_parens_with_nesting uu____7465
    | FStar_Parser_AST.Name uu____7466 ->
        let uu____7467 = p_term false false e  in
        soft_parens_with_nesting uu____7467
    | FStar_Parser_AST.Construct uu____7468 ->
        let uu____7479 = p_term false false e  in
        soft_parens_with_nesting uu____7479
    | FStar_Parser_AST.Abs uu____7480 ->
        let uu____7487 = p_term false false e  in
        soft_parens_with_nesting uu____7487
    | FStar_Parser_AST.App uu____7488 ->
        let uu____7495 = p_term false false e  in
        soft_parens_with_nesting uu____7495
    | FStar_Parser_AST.Let uu____7496 ->
        let uu____7517 = p_term false false e  in
        soft_parens_with_nesting uu____7517
    | FStar_Parser_AST.LetOpen uu____7518 ->
        let uu____7523 = p_term false false e  in
        soft_parens_with_nesting uu____7523
    | FStar_Parser_AST.Seq uu____7524 ->
        let uu____7529 = p_term false false e  in
        soft_parens_with_nesting uu____7529
    | FStar_Parser_AST.Bind uu____7530 ->
        let uu____7537 = p_term false false e  in
        soft_parens_with_nesting uu____7537
    | FStar_Parser_AST.If uu____7538 ->
        let uu____7545 = p_term false false e  in
        soft_parens_with_nesting uu____7545
    | FStar_Parser_AST.Match uu____7546 ->
        let uu____7561 = p_term false false e  in
        soft_parens_with_nesting uu____7561
    | FStar_Parser_AST.TryWith uu____7562 ->
        let uu____7577 = p_term false false e  in
        soft_parens_with_nesting uu____7577
    | FStar_Parser_AST.Ascribed uu____7578 ->
        let uu____7587 = p_term false false e  in
        soft_parens_with_nesting uu____7587
    | FStar_Parser_AST.Record uu____7588 ->
        let uu____7601 = p_term false false e  in
        soft_parens_with_nesting uu____7601
    | FStar_Parser_AST.Project uu____7602 ->
        let uu____7607 = p_term false false e  in
        soft_parens_with_nesting uu____7607
    | FStar_Parser_AST.Product uu____7608 ->
        let uu____7615 = p_term false false e  in
        soft_parens_with_nesting uu____7615
    | FStar_Parser_AST.Sum uu____7616 ->
        let uu____7623 = p_term false false e  in
        soft_parens_with_nesting uu____7623
    | FStar_Parser_AST.QForall uu____7624 ->
        let uu____7637 = p_term false false e  in
        soft_parens_with_nesting uu____7637
    | FStar_Parser_AST.QExists uu____7638 ->
        let uu____7651 = p_term false false e  in
        soft_parens_with_nesting uu____7651
    | FStar_Parser_AST.Refine uu____7652 ->
        let uu____7657 = p_term false false e  in
        soft_parens_with_nesting uu____7657
    | FStar_Parser_AST.NamedTyp uu____7658 ->
        let uu____7663 = p_term false false e  in
        soft_parens_with_nesting uu____7663
    | FStar_Parser_AST.Requires uu____7664 ->
        let uu____7671 = p_term false false e  in
        soft_parens_with_nesting uu____7671
    | FStar_Parser_AST.Ensures uu____7672 ->
        let uu____7679 = p_term false false e  in
        soft_parens_with_nesting uu____7679
    | FStar_Parser_AST.Attributes uu____7680 ->
        let uu____7683 = p_term false false e  in
        soft_parens_with_nesting uu____7683
    | FStar_Parser_AST.Quote uu____7684 ->
        let uu____7689 = p_term false false e  in
        soft_parens_with_nesting uu____7689
    | FStar_Parser_AST.VQuote uu____7690 ->
        let uu____7691 = p_term false false e  in
        soft_parens_with_nesting uu____7691
    | FStar_Parser_AST.Antiquote uu____7692 ->
        let uu____7697 = p_term false false e  in
        soft_parens_with_nesting uu____7697

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___94_7698  ->
    match uu___94_7698 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____7703) ->
        let uu____7704 = str s  in FStar_Pprint.dquotes uu____7704
    | FStar_Const.Const_bytearray (bytes,uu____7706) ->
        let uu____7711 =
          let uu____7712 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____7712  in
        let uu____7713 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____7711 uu____7713
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___92_7733 =
          match uu___92_7733 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___93_7739 =
          match uu___93_7739 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7750  ->
               match uu____7750 with
               | (s,w) ->
                   let uu____7757 = signedness s  in
                   let uu____7758 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7757 uu____7758)
            sign_width_opt
           in
        let uu____7759 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7759 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7761 = FStar_Range.string_of_range r  in str uu____7761
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7763 = p_quident lid  in
        let uu____7764 =
          let uu____7765 =
            let uu____7766 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7766  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7765  in
        FStar_Pprint.op_Hat_Hat uu____7763 uu____7764

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7768 = str "u#"  in
    let uu____7769 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7768 uu____7769

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7771;_},u1::u2::[])
        ->
        let uu____7776 =
          let uu____7777 = p_universeFrom u1  in
          let uu____7778 =
            let uu____7779 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7779  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7777 uu____7778  in
        FStar_Pprint.group uu____7776
    | FStar_Parser_AST.App uu____7780 ->
        let uu____7787 = head_and_args u  in
        (match uu____7787 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7813 =
                    let uu____7814 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7815 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7823  ->
                           match uu____7823 with
                           | (u1,uu____7829) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7814 uu____7815  in
                  FStar_Pprint.group uu____7813
              | uu____7830 ->
                  let uu____7831 =
                    let uu____7832 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7832
                     in
                  failwith uu____7831))
    | uu____7833 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7856 = FStar_Ident.text_of_id id1  in str uu____7856
    | FStar_Parser_AST.Paren u1 ->
        let uu____7858 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7858
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7859;_},uu____7860::uu____7861::[])
        ->
        let uu____7864 = p_universeFrom u  in
        soft_parens_with_nesting uu____7864
    | FStar_Parser_AST.App uu____7865 ->
        let uu____7872 = p_universeFrom u  in
        soft_parens_with_nesting uu____7872
    | uu____7873 ->
        let uu____7874 =
          let uu____7875 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7875
           in
        failwith uu____7874

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
       | FStar_Parser_AST.Module (uu____7955,decls) ->
           let uu____7961 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7961
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7970,decls,uu____7972) ->
           let uu____7977 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7977
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____8034  ->
         match uu____8034 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____8078,decls) -> decls
        | FStar_Parser_AST.Interface (uu____8084,decls,uu____8086) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____8135 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____8148;
                 FStar_Parser_AST.doc = uu____8149;
                 FStar_Parser_AST.quals = uu____8150;
                 FStar_Parser_AST.attrs = uu____8151;_}::uu____8152 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____8158 =
                   let uu____8161 =
                     let uu____8164 = FStar_List.tl ds  in d :: uu____8164
                      in
                   d0 :: uu____8161  in
                 (uu____8158, (d0.FStar_Parser_AST.drange))
             | uu____8169 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____8135 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____8233 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____8233 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____8341 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____8341, comments1))))))
  