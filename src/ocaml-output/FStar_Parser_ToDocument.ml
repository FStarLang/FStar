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
         (let uu____1116 = FStar_Ident.text_of_id op  in uu____1116 <> "~"))
  
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
      | uu____1182 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1198 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1204 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1210 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___80_1230  ->
    match uu___80_1230 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___81_1251  ->
      match uu___81_1251 with
      | FStar_Util.Inl c ->
          let uu____1260 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1260 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1271 .
    Prims.string ->
      ('Auu____1271,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1292  ->
      match uu____1292 with
      | (assoc_levels,tokens) ->
          let uu____1320 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1320 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___82_1438 =
    match uu___82_1438 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1468  ->
         match uu____1468 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1527 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1527 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1567) ->
          assoc_levels
      | uu____1596 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1632 .
    ('Auu____1632,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1677 =
        FStar_List.tryFind
          (fun uu____1707  ->
             match uu____1707 with
             | (uu____1720,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1677 with
      | FStar_Pervasives_Native.Some ((uu____1742,l1,uu____1744),uu____1745)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1780 =
            let uu____1781 =
              let uu____1782 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1782  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1781
             in
          failwith uu____1780
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1804 = assign_levels level_associativity_spec op  in
    match uu____1804 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1834 =
      let uu____1837 =
        let uu____1842 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1842  in
      FStar_List.tryFind uu____1837 operatorInfix0ad12  in
    uu____1834 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1900 =
      let uu____1914 =
        let uu____1930 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1930  in
      FStar_List.tryFind uu____1914 opinfix34  in
    uu____1900 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1986 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1986
    then (Prims.parse_int "1")
    else
      (let uu____1988 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1988
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____1997 . FStar_Ident.ident -> 'Auu____1997 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2013 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2013 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2015 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2015
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2016 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2016 [".()<-"; ".[]<-"]
      | uu____2017 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2055 .
    ('Auu____2055 -> FStar_Pprint.document) ->
      'Auu____2055 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2096 = FStar_ST.op_Bang comment_stack  in
          match uu____2096 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2159 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2159
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2200 =
                    let uu____2201 =
                      let uu____2202 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2202
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2201  in
                  comments_before_pos uu____2200 print_pos lookahead_pos))
              else
                (let uu____2204 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2204))
           in
        let uu____2205 =
          let uu____2210 =
            let uu____2211 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2211  in
          let uu____2212 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2210 uu____2212  in
        match uu____2205 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2218 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2218
              else comments  in
            let uu____2224 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2224
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2245 = FStar_ST.op_Bang comment_stack  in
          match uu____2245 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2337 =
                    let uu____2338 =
                      let uu____2339 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2339  in
                    uu____2338 - lbegin  in
                  max k uu____2337  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2342 =
                    let uu____2343 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2344 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2343 uu____2344  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2342  in
                let uu____2345 =
                  let uu____2346 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2346  in
                place_comments_until_pos (Prims.parse_int "1") uu____2345
                  pos_end doc2))
          | uu____2347 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2356 =
                     let uu____2357 = FStar_Range.line_of_pos pos_end  in
                     uu____2357 - lbegin  in
                   max (Prims.parse_int "1") uu____2356  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2359 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2359)
  
let separate_map_with_comments :
  'Auu____2372 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2372 -> FStar_Pprint.document) ->
          'Auu____2372 Prims.list ->
            ('Auu____2372 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2429 x =
              match uu____2429 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2443 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2443 doc1
                     in
                  let uu____2444 =
                    let uu____2445 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2445  in
                  let uu____2446 =
                    let uu____2447 =
                      let uu____2448 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2448  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2447  in
                  (uu____2444, uu____2446)
               in
            let uu____2449 =
              let uu____2456 = FStar_List.hd xs  in
              let uu____2457 = FStar_List.tl xs  in (uu____2456, uu____2457)
               in
            match uu____2449 with
            | (x,xs1) ->
                let init1 =
                  let uu____2473 =
                    let uu____2474 =
                      let uu____2475 = extract_range x  in
                      FStar_Range.end_of_range uu____2475  in
                    FStar_Range.line_of_pos uu____2474  in
                  let uu____2476 =
                    let uu____2477 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2477  in
                  (uu____2473, uu____2476)  in
                let uu____2478 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2478
  
let separate_map_with_comments_kw :
  'Auu____2501 'Auu____2502 .
    'Auu____2501 ->
      'Auu____2501 ->
        ('Auu____2501 -> 'Auu____2502 -> FStar_Pprint.document) ->
          'Auu____2502 Prims.list ->
            ('Auu____2502 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2564 x =
              match uu____2564 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2578 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2578 doc1
                     in
                  let uu____2579 =
                    let uu____2580 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2580  in
                  let uu____2581 =
                    let uu____2582 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2582  in
                  (uu____2579, uu____2581)
               in
            let uu____2583 =
              let uu____2590 = FStar_List.hd xs  in
              let uu____2591 = FStar_List.tl xs  in (uu____2590, uu____2591)
               in
            match uu____2583 with
            | (x,xs1) ->
                let init1 =
                  let uu____2607 =
                    let uu____2608 =
                      let uu____2609 = extract_range x  in
                      FStar_Range.end_of_range uu____2609  in
                    FStar_Range.line_of_pos uu____2608  in
                  let uu____2610 = f prefix1 x  in (uu____2607, uu____2610)
                   in
                let uu____2611 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2611
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3321)) ->
          let uu____3324 =
            let uu____3325 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3325 FStar_Util.is_upper  in
          if uu____3324
          then
            let uu____3326 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3326 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3328 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3335 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3336 =
      let uu____3337 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3338 =
        let uu____3339 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3339  in
      FStar_Pprint.op_Hat_Hat uu____3337 uu____3338  in
    FStar_Pprint.op_Hat_Hat uu____3335 uu____3336

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3341 ->
        let uu____3342 =
          let uu____3343 = str "@ "  in
          let uu____3344 =
            let uu____3345 =
              let uu____3346 =
                let uu____3347 =
                  let uu____3348 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3348  in
                FStar_Pprint.op_Hat_Hat uu____3347 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3346  in
            FStar_Pprint.op_Hat_Hat uu____3345 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3343 uu____3344  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3342

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3351  ->
    match uu____3351 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3387 =
                match uu____3387 with
                | (kwd,arg) ->
                    let uu____3394 = str "@"  in
                    let uu____3395 =
                      let uu____3396 = str kwd  in
                      let uu____3397 =
                        let uu____3398 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3398
                         in
                      FStar_Pprint.op_Hat_Hat uu____3396 uu____3397  in
                    FStar_Pprint.op_Hat_Hat uu____3394 uu____3395
                 in
              let uu____3399 =
                let uu____3400 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3400 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3399
           in
        let uu____3405 =
          let uu____3406 =
            let uu____3407 =
              let uu____3408 =
                let uu____3409 = str doc1  in
                let uu____3410 =
                  let uu____3411 =
                    let uu____3412 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3412  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3411  in
                FStar_Pprint.op_Hat_Hat uu____3409 uu____3410  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3408  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3407  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3406  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3405

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3416 =
          let uu____3417 = str "val"  in
          let uu____3418 =
            let uu____3419 =
              let uu____3420 = p_lident lid  in
              let uu____3421 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3420 uu____3421  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3419  in
          FStar_Pprint.op_Hat_Hat uu____3417 uu____3418  in
        let uu____3422 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3416 uu____3422
    | FStar_Parser_AST.TopLevelLet (uu____3423,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3448 =
               let uu____3449 = str "let"  in p_letlhs uu____3449 lb  in
             FStar_Pprint.group uu____3448) lbs
    | uu____3450 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___83_3465 =
          match uu___83_3465 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3473 = f x  in
              let uu____3474 =
                let uu____3475 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3475  in
              FStar_Pprint.op_Hat_Hat uu____3473 uu____3474
           in
        let uu____3476 = str "["  in
        let uu____3477 =
          let uu____3478 = p_list' l  in
          let uu____3479 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3478 uu____3479  in
        FStar_Pprint.op_Hat_Hat uu____3476 uu____3477

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3482 =
          let uu____3483 = str "open"  in
          let uu____3484 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3483 uu____3484  in
        FStar_Pprint.group uu____3482
    | FStar_Parser_AST.Include uid ->
        let uu____3486 =
          let uu____3487 = str "include"  in
          let uu____3488 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3487 uu____3488  in
        FStar_Pprint.group uu____3486
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3491 =
          let uu____3492 = str "module"  in
          let uu____3493 =
            let uu____3494 =
              let uu____3495 = p_uident uid1  in
              let uu____3496 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3495 uu____3496  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3494  in
          FStar_Pprint.op_Hat_Hat uu____3492 uu____3493  in
        let uu____3497 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3491 uu____3497
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3499 =
          let uu____3500 = str "module"  in
          let uu____3501 =
            let uu____3502 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3502  in
          FStar_Pprint.op_Hat_Hat uu____3500 uu____3501  in
        FStar_Pprint.group uu____3499
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3535 = str "effect"  in
          let uu____3536 =
            let uu____3537 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3537  in
          FStar_Pprint.op_Hat_Hat uu____3535 uu____3536  in
        let uu____3538 =
          let uu____3539 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3539 FStar_Pprint.equals
           in
        let uu____3540 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3538 uu____3540
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3558 =
          let uu____3559 = str "type"  in
          let uu____3560 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3559 uu____3560  in
        let uu____3573 =
          let uu____3574 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3612 =
                    let uu____3613 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3613 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3612)) uu____3574
           in
        FStar_Pprint.op_Hat_Hat uu____3558 uu____3573
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3629 = str "let"  in
          let uu____3630 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3629 uu____3630  in
        let uu____3631 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3631 p_letbinding lbs
          (fun uu____3639  ->
             match uu____3639 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3648 = str "val"  in
        let uu____3649 =
          let uu____3650 =
            let uu____3651 = p_lident lid  in
            let uu____3652 =
              let uu____3653 =
                let uu____3654 =
                  let uu____3655 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3655  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3654  in
              FStar_Pprint.group uu____3653  in
            FStar_Pprint.op_Hat_Hat uu____3651 uu____3652  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3650  in
        FStar_Pprint.op_Hat_Hat uu____3648 uu____3649
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3659 =
            let uu____3660 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3660 FStar_Util.is_upper  in
          if uu____3659
          then FStar_Pprint.empty
          else
            (let uu____3662 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3662 FStar_Pprint.space)
           in
        let uu____3663 =
          let uu____3664 = p_ident id1  in
          let uu____3665 =
            let uu____3666 =
              let uu____3667 =
                let uu____3668 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3668  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3667  in
            FStar_Pprint.group uu____3666  in
          FStar_Pprint.op_Hat_Hat uu____3664 uu____3665  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3663
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3675 = str "exception"  in
        let uu____3676 =
          let uu____3677 =
            let uu____3678 = p_uident uid  in
            let uu____3679 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3683 =
                     let uu____3684 = str "of"  in
                     let uu____3685 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3684 uu____3685  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3683) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3678 uu____3679  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3677  in
        FStar_Pprint.op_Hat_Hat uu____3675 uu____3676
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3687 = str "new_effect"  in
        let uu____3688 =
          let uu____3689 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3689  in
        FStar_Pprint.op_Hat_Hat uu____3687 uu____3688
    | FStar_Parser_AST.SubEffect se ->
        let uu____3691 = str "sub_effect"  in
        let uu____3692 =
          let uu____3693 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3693  in
        FStar_Pprint.op_Hat_Hat uu____3691 uu____3692
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3696 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3696 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3697 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3698) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3721 = str "%splice"  in
        let uu____3722 =
          let uu____3723 =
            let uu____3724 = str ";"  in p_list p_uident uu____3724 ids  in
          let uu____3725 =
            let uu____3726 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3726  in
          FStar_Pprint.op_Hat_Hat uu____3723 uu____3725  in
        FStar_Pprint.op_Hat_Hat uu____3721 uu____3722

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___84_3727  ->
    match uu___84_3727 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3729 = str "#set-options"  in
        let uu____3730 =
          let uu____3731 =
            let uu____3732 = str s  in FStar_Pprint.dquotes uu____3732  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3731  in
        FStar_Pprint.op_Hat_Hat uu____3729 uu____3730
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3736 = str "#reset-options"  in
        let uu____3737 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3741 =
                 let uu____3742 = str s  in FStar_Pprint.dquotes uu____3742
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3741) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3736 uu____3737
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
    fun uu____3771  ->
      match uu____3771 with
      | (typedecl,fsdoc_opt) ->
          let uu____3784 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3784 with
           | (decl,body) ->
               let uu____3802 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3802)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___85_3804  ->
      match uu___85_3804 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3834 = FStar_Pprint.empty  in
          let uu____3835 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3835, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3856 =
            let uu____3857 = p_typ false false t  in jump2 uu____3857  in
          let uu____3858 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3858, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3912 =
            match uu____3912 with
            | (lid1,t,doc_opt) ->
                let uu____3928 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3928
             in
          let p_fields uu____3944 =
            let uu____3945 =
              let uu____3946 =
                let uu____3947 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3947 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3946  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3945  in
          let uu____3956 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3956, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4017 =
            match uu____4017 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4043 =
                    let uu____4044 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4044  in
                  FStar_Range.extend_to_end_of_line uu____4043  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4070 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4083 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4083,
            ((fun uu____4089  ->
                let uu____4090 = datacon_doc ()  in jump2 uu____4090)))

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
  fun uu____4091  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4091 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4125 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4125  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4127 =
                        let uu____4130 =
                          let uu____4133 = p_fsdoc fsdoc  in
                          let uu____4134 =
                            let uu____4137 = cont lid_doc  in [uu____4137]
                             in
                          uu____4133 :: uu____4134  in
                        kw :: uu____4130  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4127
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4142 =
                        let uu____4143 =
                          let uu____4144 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4144 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4143
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4142
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4159 =
                          let uu____4160 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4160  in
                        prefix2 uu____4159 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4162  ->
      match uu____4162 with
      | (lid,t,doc_opt) ->
          let uu____4178 =
            let uu____4179 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4180 =
              let uu____4181 = p_lident lid  in
              let uu____4182 =
                let uu____4183 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4183  in
              FStar_Pprint.op_Hat_Hat uu____4181 uu____4182  in
            FStar_Pprint.op_Hat_Hat uu____4179 uu____4180  in
          FStar_Pprint.group uu____4178

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4184  ->
    match uu____4184 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4212 =
            let uu____4213 =
              let uu____4214 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4214  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4213  in
          FStar_Pprint.group uu____4212  in
        let uu____4215 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4216 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4220 =
                 let uu____4221 =
                   let uu____4222 =
                     let uu____4223 =
                       let uu____4224 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4224
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4223  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4222  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4221  in
               FStar_Pprint.group uu____4220) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4215 uu____4216

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4226  ->
      match uu____4226 with
      | (pat,uu____4232) ->
          let uu____4233 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4252 =
                  let uu____4253 =
                    let uu____4254 =
                      let uu____4255 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4255
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4254  in
                  FStar_Pprint.group uu____4253  in
                (pat1, uu____4252)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4267 =
                  let uu____4268 =
                    let uu____4269 =
                      let uu____4270 =
                        let uu____4271 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4271
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4270
                       in
                    FStar_Pprint.group uu____4269  in
                  let uu____4272 =
                    let uu____4273 =
                      let uu____4274 = str "by"  in
                      let uu____4275 =
                        let uu____4276 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4276
                         in
                      FStar_Pprint.op_Hat_Hat uu____4274 uu____4275  in
                    FStar_Pprint.group uu____4273  in
                  FStar_Pprint.op_Hat_Hat uu____4268 uu____4272  in
                (pat1, uu____4267)
            | uu____4277 -> (pat, FStar_Pprint.empty)  in
          (match uu____4233 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4281);
                       FStar_Parser_AST.prange = uu____4282;_},pats)
                    ->
                    let uu____4292 =
                      let uu____4293 =
                        let uu____4294 =
                          let uu____4295 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4295  in
                        FStar_Pprint.group uu____4294  in
                      let uu____4296 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4293 uu____4296  in
                    prefix2_nonempty uu____4292 ascr_doc
                | uu____4297 ->
                    let uu____4298 =
                      let uu____4299 =
                        let uu____4300 =
                          let uu____4301 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4301  in
                        FStar_Pprint.group uu____4300  in
                      FStar_Pprint.op_Hat_Hat uu____4299 ascr_doc  in
                    FStar_Pprint.group uu____4298))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4303  ->
      match uu____4303 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4312 =
            let uu____4313 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4313  in
          let uu____4314 =
            let uu____4315 =
              let uu____4316 =
                let uu____4317 =
                  let uu____4318 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4318  in
                FStar_Pprint.group uu____4317  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4316  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4315  in
          FStar_Pprint.ifflat uu____4312 uu____4314

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___86_4319  ->
    match uu___86_4319 with
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
        let uu____4344 = p_uident uid  in
        let uu____4345 = p_binders true bs  in
        let uu____4346 =
          let uu____4347 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4347  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4344 uu____4345 uu____4346

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
          let uu____4357 =
            let uu____4358 =
              let uu____4359 =
                let uu____4360 = p_uident uid  in
                let uu____4361 = p_binders true bs  in
                let uu____4362 =
                  let uu____4363 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4363  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4360 uu____4361 uu____4362
                 in
              FStar_Pprint.group uu____4359  in
            let uu____4364 =
              let uu____4365 = str "with"  in
              let uu____4366 =
                let uu____4367 =
                  let uu____4368 =
                    let uu____4369 =
                      let uu____4370 =
                        let uu____4371 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4371
                         in
                      separate_map_last uu____4370 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4369  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4368  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4367  in
              FStar_Pprint.op_Hat_Hat uu____4365 uu____4366  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4358 uu____4364  in
          braces_with_nesting uu____4357

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
          let uu____4402 =
            let uu____4403 = p_lident lid  in
            let uu____4404 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4403 uu____4404  in
          let uu____4405 = p_simpleTerm ps false e  in
          prefix2 uu____4402 uu____4405
      | uu____4406 ->
          let uu____4407 =
            let uu____4408 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4408
             in
          failwith uu____4407

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4470 =
        match uu____4470 with
        | (kwd,t) ->
            let uu____4477 =
              let uu____4478 = str kwd  in
              let uu____4479 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4478 uu____4479  in
            let uu____4480 = p_simpleTerm ps false t  in
            prefix2 uu____4477 uu____4480
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4485 =
      let uu____4486 =
        let uu____4487 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4488 =
          let uu____4489 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4489  in
        FStar_Pprint.op_Hat_Hat uu____4487 uu____4488  in
      let uu____4490 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4486 uu____4490  in
    let uu____4491 =
      let uu____4492 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4492  in
    FStar_Pprint.op_Hat_Hat uu____4485 uu____4491

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___87_4493  ->
    match uu___87_4493 with
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
    | uu____4495 ->
        let uu____4496 =
          let uu____4497 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4497  in
        FStar_Pprint.op_Hat_Hat uu____4496 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___88_4500  ->
    match uu___88_4500 with
    | FStar_Parser_AST.Rec  ->
        let uu____4501 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4501
    | FStar_Parser_AST.Mutable  ->
        let uu____4502 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4502
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___89_4503  ->
    match uu___89_4503 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4508 =
          let uu____4509 =
            let uu____4510 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4510  in
          FStar_Pprint.separate_map uu____4509 p_tuplePattern pats  in
        FStar_Pprint.group uu____4508
    | uu____4511 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4518 =
          let uu____4519 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4519 p_constructorPattern pats  in
        FStar_Pprint.group uu____4518
    | uu____4520 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4523;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4528 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4529 = p_constructorPattern hd1  in
        let uu____4530 = p_constructorPattern tl1  in
        infix0 uu____4528 uu____4529 uu____4530
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4532;_},pats)
        ->
        let uu____4538 = p_quident uid  in
        let uu____4539 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4538 uu____4539
    | uu____4540 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4556;
               FStar_Parser_AST.blevel = uu____4557;
               FStar_Parser_AST.aqual = uu____4558;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4564 =
               let uu____4565 = p_ident lid  in
               p_refinement aqual uu____4565 t1 phi  in
             soft_parens_with_nesting uu____4564
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4567;
               FStar_Parser_AST.blevel = uu____4568;
               FStar_Parser_AST.aqual = uu____4569;_},phi))
             ->
             let uu____4571 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
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
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4643 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4644 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4643 uu____4644
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4646 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4649;
           FStar_Parser_AST.prange = uu____4650;_},uu____4651)
        ->
        let uu____4656 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4656
    | FStar_Parser_AST.PatTuple (uu____4657,false ) ->
        let uu____4662 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4662
    | uu____4663 ->
        let uu____4664 =
          let uu____4665 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4665  in
        failwith uu____4664

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4667;_},uu____4668)
        -> true
    | uu____4673 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4677 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4678 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4677 uu____4678
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4685;
                   FStar_Parser_AST.blevel = uu____4686;
                   FStar_Parser_AST.aqual = uu____4687;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4689 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4689 t1 phi
            | uu____4690 ->
                let t' =
                  let uu____4692 = is_typ_tuple t  in
                  if uu____4692
                  then
                    let uu____4693 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4693
                  else p_tmFormula t  in
                let uu____4695 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4696 =
                  let uu____4697 = p_lident lid  in
                  let uu____4698 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4697 uu____4698  in
                FStar_Pprint.op_Hat_Hat uu____4695 uu____4696
             in
          if is_atomic
          then
            let uu____4699 =
              let uu____4700 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4700  in
            FStar_Pprint.group uu____4699
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4702 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4709;
                  FStar_Parser_AST.blevel = uu____4710;
                  FStar_Parser_AST.aqual = uu____4711;_},phi)
               ->
               if is_atomic
               then
                 let uu____4713 =
                   let uu____4714 =
                     let uu____4715 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4715 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4714  in
                 FStar_Pprint.group uu____4713
               else
                 (let uu____4717 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4717)
           | uu____4718 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4727 -> false
            | FStar_Parser_AST.App uu____4738 -> false
            | FStar_Parser_AST.Op uu____4745 -> false
            | uu____4752 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4756 =
            let uu____4757 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4758 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4757 uu____4758  in
          let uu____4759 =
            let uu____4760 = p_appTerm t  in
            let uu____4761 =
              let uu____4762 =
                let uu____4763 =
                  let uu____4764 = soft_braces_with_nesting_tight phi1  in
                  let uu____4765 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4764 uu____4765  in
                FStar_Pprint.group uu____4763  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4762
               in
            FStar_Pprint.op_Hat_Hat uu____4760 uu____4761  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4756 uu____4759

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4776 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4776

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4781 = FStar_Ident.text_of_id lid  in str uu____4781)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4784 = FStar_Ident.text_of_lid lid  in str uu____4784)

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
            let uu____4807 =
              let uu____4808 =
                let uu____4809 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4809 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4808  in
            let uu____4810 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4807 uu____4810
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4814 =
              let uu____4815 =
                let uu____4816 =
                  let uu____4817 = p_lident x  in
                  let uu____4818 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4817 uu____4818  in
                let uu____4819 =
                  let uu____4820 = p_noSeqTerm true false e1  in
                  let uu____4821 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4820 uu____4821  in
                op_Hat_Slash_Plus_Hat uu____4816 uu____4819  in
              FStar_Pprint.group uu____4815  in
            let uu____4822 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4814 uu____4822
        | uu____4823 ->
            let uu____4824 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4824

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
            let uu____4835 =
              let uu____4836 = p_tmIff e1  in
              let uu____4837 =
                let uu____4838 =
                  let uu____4839 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4839
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4838  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4836 uu____4837  in
            FStar_Pprint.group uu____4835
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4845 =
              let uu____4846 = p_tmIff e1  in
              let uu____4847 =
                let uu____4848 =
                  let uu____4849 =
                    let uu____4850 = p_typ false false t  in
                    let uu____4851 =
                      let uu____4852 = str "by"  in
                      let uu____4853 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4852 uu____4853  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4850 uu____4851  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4849
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4848  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4846 uu____4847  in
            FStar_Pprint.group uu____4845
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4854;_},e1::e2::e3::[])
            ->
            let uu____4860 =
              let uu____4861 =
                let uu____4862 =
                  let uu____4863 = p_atomicTermNotQUident e1  in
                  let uu____4864 =
                    let uu____4865 =
                      let uu____4866 =
                        let uu____4867 = p_term false false e2  in
                        soft_parens_with_nesting uu____4867  in
                      let uu____4868 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4866 uu____4868  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4865  in
                  FStar_Pprint.op_Hat_Hat uu____4863 uu____4864  in
                FStar_Pprint.group uu____4862  in
              let uu____4869 =
                let uu____4870 = p_noSeqTerm ps pb e3  in jump2 uu____4870
                 in
              FStar_Pprint.op_Hat_Hat uu____4861 uu____4869  in
            FStar_Pprint.group uu____4860
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4871;_},e1::e2::e3::[])
            ->
            let uu____4877 =
              let uu____4878 =
                let uu____4879 =
                  let uu____4880 = p_atomicTermNotQUident e1  in
                  let uu____4881 =
                    let uu____4882 =
                      let uu____4883 =
                        let uu____4884 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4884  in
                      let uu____4885 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4883 uu____4885  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4882  in
                  FStar_Pprint.op_Hat_Hat uu____4880 uu____4881  in
                FStar_Pprint.group uu____4879  in
              let uu____4886 =
                let uu____4887 = p_noSeqTerm ps pb e3  in jump2 uu____4887
                 in
              FStar_Pprint.op_Hat_Hat uu____4878 uu____4886  in
            FStar_Pprint.group uu____4877
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4895 =
              let uu____4896 = str "requires"  in
              let uu____4897 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4896 uu____4897  in
            FStar_Pprint.group uu____4895
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4905 =
              let uu____4906 = str "ensures"  in
              let uu____4907 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4906 uu____4907  in
            FStar_Pprint.group uu____4905
        | FStar_Parser_AST.Attributes es ->
            let uu____4911 =
              let uu____4912 = str "attributes"  in
              let uu____4913 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4912 uu____4913  in
            FStar_Pprint.group uu____4911
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4917 =
                let uu____4918 =
                  let uu____4919 = str "if"  in
                  let uu____4920 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4919 uu____4920  in
                let uu____4921 =
                  let uu____4922 = str "then"  in
                  let uu____4923 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4922 uu____4923  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4918 uu____4921  in
              FStar_Pprint.group uu____4917
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4926,uu____4927,e31) when
                     is_unit e31 ->
                     let uu____4929 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4929
                 | uu____4930 -> p_noSeqTerm false false e2  in
               let uu____4931 =
                 let uu____4932 =
                   let uu____4933 = str "if"  in
                   let uu____4934 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4933 uu____4934  in
                 let uu____4935 =
                   let uu____4936 =
                     let uu____4937 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4937 e2_doc  in
                   let uu____4938 =
                     let uu____4939 = str "else"  in
                     let uu____4940 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4939 uu____4940  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4936 uu____4938  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4932 uu____4935  in
               FStar_Pprint.group uu____4931)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4963 =
              let uu____4964 =
                let uu____4965 =
                  let uu____4966 = str "try"  in
                  let uu____4967 = p_noSeqTerm false false e1  in
                  prefix2 uu____4966 uu____4967  in
                let uu____4968 =
                  let uu____4969 = str "with"  in
                  let uu____4970 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4969 uu____4970  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4965 uu____4968  in
              FStar_Pprint.group uu____4964  in
            let uu____4979 = paren_if (ps || pb)  in uu____4979 uu____4963
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5006 =
              let uu____5007 =
                let uu____5008 =
                  let uu____5009 = str "match"  in
                  let uu____5010 = p_noSeqTerm false false e1  in
                  let uu____5011 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5009 uu____5010 uu____5011
                   in
                let uu____5012 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5008 uu____5012  in
              FStar_Pprint.group uu____5007  in
            let uu____5021 = paren_if (ps || pb)  in uu____5021 uu____5006
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5028 =
              let uu____5029 =
                let uu____5030 =
                  let uu____5031 = str "let open"  in
                  let uu____5032 = p_quident uid  in
                  let uu____5033 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5031 uu____5032 uu____5033
                   in
                let uu____5034 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5030 uu____5034  in
              FStar_Pprint.group uu____5029  in
            let uu____5035 = paren_if ps  in uu____5035 uu____5028
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5099 is_last =
              match uu____5099 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5132 =
                          let uu____5133 = str "let"  in
                          let uu____5134 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5133 uu____5134
                           in
                        FStar_Pprint.group uu____5132
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5135 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5140 =
                    if is_last
                    then
                      let uu____5141 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5142 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5141 doc_expr uu____5142
                    else
                      (let uu____5144 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5144)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5140
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5190 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5190
                     else
                       (let uu____5198 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5198)) lbs
               in
            let lbs_doc =
              let uu____5206 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5206  in
            let uu____5207 =
              let uu____5208 =
                let uu____5209 =
                  let uu____5210 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5210
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5209  in
              FStar_Pprint.group uu____5208  in
            let uu____5211 = paren_if ps  in uu____5211 uu____5207
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5218;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5221;
                                                             FStar_Parser_AST.level
                                                               = uu____5222;_})
            when matches_var maybe_x x ->
            let uu____5249 =
              let uu____5250 =
                let uu____5251 = str "function"  in
                let uu____5252 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5251 uu____5252  in
              FStar_Pprint.group uu____5250  in
            let uu____5261 = paren_if (ps || pb)  in uu____5261 uu____5249
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5267 =
              let uu____5268 = str "quote"  in
              let uu____5269 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5268 uu____5269  in
            FStar_Pprint.group uu____5267
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5271 =
              let uu____5272 = str "`"  in
              let uu____5273 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5272 uu____5273  in
            FStar_Pprint.group uu____5271
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5275 =
              let uu____5276 = str "%`"  in
              let uu____5277 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5276 uu____5277  in
            FStar_Pprint.group uu____5275
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5279 =
              let uu____5280 = str "`#"  in
              let uu____5281 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5280 uu____5281  in
            FStar_Pprint.group uu____5279
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5283 =
              let uu____5284 = str "`@"  in
              let uu____5285 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5284 uu____5285  in
            FStar_Pprint.group uu____5283
        | uu____5286 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___90_5287  ->
    match uu___90_5287 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5299 =
          let uu____5300 = str "[@"  in
          let uu____5301 =
            let uu____5302 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5303 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5302 uu____5303  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5300 uu____5301  in
        FStar_Pprint.group uu____5299

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
                 let uu____5329 =
                   let uu____5330 =
                     let uu____5331 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5331 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5330 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5329 term_doc
             | pats ->
                 let uu____5337 =
                   let uu____5338 =
                     let uu____5339 =
                       let uu____5340 =
                         let uu____5341 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5341
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5340 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5342 = p_trigger trigger  in
                     prefix2 uu____5339 uu____5342  in
                   FStar_Pprint.group uu____5338  in
                 prefix2 uu____5337 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5362 =
                   let uu____5363 =
                     let uu____5364 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5364 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5363 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5362 term_doc
             | pats ->
                 let uu____5370 =
                   let uu____5371 =
                     let uu____5372 =
                       let uu____5373 =
                         let uu____5374 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5374
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5373 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5375 = p_trigger trigger  in
                     prefix2 uu____5372 uu____5375  in
                   FStar_Pprint.group uu____5371  in
                 prefix2 uu____5370 term_doc)
        | uu____5376 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5378 -> str "forall"
    | FStar_Parser_AST.QExists uu____5391 -> str "exists"
    | uu____5404 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___91_5405  ->
    match uu___91_5405 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5417 =
          let uu____5418 =
            let uu____5419 =
              let uu____5420 = str "pattern"  in
              let uu____5421 =
                let uu____5422 =
                  let uu____5423 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5423
                   in
                FStar_Pprint.op_Hat_Hat uu____5422 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5420 uu____5421  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5419  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5418  in
        FStar_Pprint.group uu____5417

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5429 = str "\\/"  in
    FStar_Pprint.separate_map uu____5429 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5435 =
      let uu____5436 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5436 p_appTerm pats  in
    FStar_Pprint.group uu____5435

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5446 =
              let uu____5447 =
                let uu____5448 = str "fun"  in
                let uu____5449 =
                  let uu____5450 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5450
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5448 uu____5449  in
              let uu____5451 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5447 uu____5451  in
            let uu____5452 = paren_if ps  in uu____5452 uu____5446
        | uu____5457 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5461  ->
      match uu____5461 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5484 =
                    let uu____5485 =
                      let uu____5486 =
                        let uu____5487 = p_tuplePattern p  in
                        let uu____5488 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5487 uu____5488  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5486
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5485  in
                  FStar_Pprint.group uu____5484
              | FStar_Pervasives_Native.Some f ->
                  let uu____5490 =
                    let uu____5491 =
                      let uu____5492 =
                        let uu____5493 =
                          let uu____5494 =
                            let uu____5495 = p_tuplePattern p  in
                            let uu____5496 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5495
                              uu____5496
                             in
                          FStar_Pprint.group uu____5494  in
                        let uu____5497 =
                          let uu____5498 =
                            let uu____5501 = p_tmFormula f  in
                            [uu____5501; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5498  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5493 uu____5497
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5492
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5491  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5490
               in
            let uu____5502 =
              let uu____5503 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5503  in
            FStar_Pprint.group uu____5502  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5512 =
                      let uu____5513 =
                        let uu____5514 =
                          let uu____5515 =
                            let uu____5516 =
                              let uu____5517 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5517  in
                            FStar_Pprint.separate_map uu____5516
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5515
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5514
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5513  in
                    FStar_Pprint.group uu____5512
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5518 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5520;_},e1::e2::[])
        ->
        let uu____5525 = str "<==>"  in
        let uu____5526 = p_tmImplies e1  in
        let uu____5527 = p_tmIff e2  in
        infix0 uu____5525 uu____5526 uu____5527
    | uu____5528 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5530;_},e1::e2::[])
        ->
        let uu____5535 = str "==>"  in
        let uu____5536 = p_tmArrow p_tmFormula e1  in
        let uu____5537 = p_tmImplies e2  in
        infix0 uu____5535 uu____5536 uu____5537
    | uu____5538 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5546 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5546 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5567 ->
               let uu____5568 =
                 let uu____5569 =
                   let uu____5570 =
                     let uu____5571 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5571
                      in
                   FStar_Pprint.separate uu____5570 terms  in
                 let uu____5572 =
                   let uu____5573 =
                     let uu____5574 =
                       let uu____5575 =
                         let uu____5576 =
                           let uu____5577 =
                             let uu____5578 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5578
                              in
                           FStar_Pprint.separate uu____5577 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5576 last_op  in
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
                         jump2 uu____5580  in
                       FStar_Pprint.ifflat uu____5575 uu____5579  in
                     FStar_Pprint.group uu____5574  in
                   let uu____5584 = FStar_List.hd last1  in
                   prefix2 uu____5573 uu____5584  in
                 FStar_Pprint.ifflat uu____5569 uu____5572  in
               FStar_Pprint.group uu____5568)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5597 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5602 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5597 uu____5602
      | uu____5605 -> let uu____5606 = p_Tm e  in [uu____5606]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5609 =
        let uu____5610 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5610 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5609  in
    let disj =
      let uu____5612 =
        let uu____5613 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5613 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5612  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5632;_},e1::e2::[])
        ->
        let uu____5637 = p_tmDisjunction e1  in
        let uu____5642 = let uu____5647 = p_tmConjunction e2  in [uu____5647]
           in
        FStar_List.append uu____5637 uu____5642
    | uu____5656 -> let uu____5657 = p_tmConjunction e  in [uu____5657]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5667;_},e1::e2::[])
        ->
        let uu____5672 = p_tmConjunction e1  in
        let uu____5675 = let uu____5678 = p_tmTuple e2  in [uu____5678]  in
        FStar_List.append uu____5672 uu____5675
    | uu____5679 -> let uu____5680 = p_tmTuple e  in [uu____5680]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5697 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5697
          (fun uu____5705  ->
             match uu____5705 with | (e1,uu____5711) -> p_tmEq e1) args
    | uu____5712 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5717 =
             let uu____5718 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5718  in
           FStar_Pprint.group uu____5717)

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
               (let uu____5735 = FStar_Ident.text_of_id op  in
                uu____5735 = "="))
              ||
              (let uu____5737 = FStar_Ident.text_of_id op  in
               uu____5737 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5739 = levels op1  in
            (match uu____5739 with
             | (left1,mine,right1) ->
                 let uu____5749 =
                   let uu____5750 = FStar_All.pipe_left str op1  in
                   let uu____5751 = p_tmEqWith' p_X left1 e1  in
                   let uu____5752 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5750 uu____5751 uu____5752  in
                 paren_if_gt curr mine uu____5749)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5753;_},e1::e2::[])
            ->
            let uu____5758 =
              let uu____5759 = p_tmEqWith p_X e1  in
              let uu____5760 =
                let uu____5761 =
                  let uu____5762 =
                    let uu____5763 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5763  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5762  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5761  in
              FStar_Pprint.op_Hat_Hat uu____5759 uu____5760  in
            FStar_Pprint.group uu____5758
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5764;_},e1::[])
            ->
            let uu____5768 = levels "-"  in
            (match uu____5768 with
             | (left1,mine,right1) ->
                 let uu____5778 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5778)
        | uu____5779 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5823)::(e2,uu____5825)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5845 = is_list e  in Prims.op_Negation uu____5845)
              ->
              let op = "::"  in
              let uu____5847 = levels op  in
              (match uu____5847 with
               | (left1,mine,right1) ->
                   let uu____5857 =
                     let uu____5858 = str op  in
                     let uu____5859 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5860 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5858 uu____5859 uu____5860  in
                   paren_if_gt curr mine uu____5857)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5868 = levels op  in
              (match uu____5868 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5884 = p_binder false b  in
                     let uu____5885 =
                       let uu____5886 =
                         let uu____5887 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5887 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5886
                        in
                     FStar_Pprint.op_Hat_Hat uu____5884 uu____5885  in
                   let uu____5888 =
                     let uu____5889 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5890 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5889 uu____5890  in
                   paren_if_gt curr mine uu____5888)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5891;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5920 = levels op  in
              (match uu____5920 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5930 = str op  in
                     let uu____5931 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____5932 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5930 uu____5931 uu____5932
                   else
                     (let uu____5934 =
                        let uu____5935 = str op  in
                        let uu____5936 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____5937 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____5935 uu____5936 uu____5937  in
                      paren_if_gt curr mine uu____5934))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____5944 = levels op1  in
              (match uu____5944 with
               | (left1,mine,right1) ->
                   let uu____5954 =
                     let uu____5955 = str op1  in
                     let uu____5956 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5957 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5955 uu____5956 uu____5957  in
                   paren_if_gt curr mine uu____5954)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____5976 =
                let uu____5977 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____5978 =
                  let uu____5979 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____5979 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____5977 uu____5978  in
              braces_with_nesting uu____5976
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____5984;_},e1::[])
              ->
              let uu____5988 =
                let uu____5989 = str "~"  in
                let uu____5990 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____5989 uu____5990  in
              FStar_Pprint.group uu____5988
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____5992;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____5998 = levels op  in
                   (match uu____5998 with
                    | (left1,mine,right1) ->
                        let uu____6008 =
                          let uu____6009 = str op  in
                          let uu____6010 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6011 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6009 uu____6010 uu____6011  in
                        paren_if_gt curr mine uu____6008)
               | uu____6012 -> p_X e)
          | uu____6013 -> p_X e

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
        let uu____6020 =
          let uu____6021 = p_lident lid  in
          let uu____6022 =
            let uu____6023 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6023  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6021 uu____6022  in
        FStar_Pprint.group uu____6020
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6026 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6028 = p_appTerm e  in
    let uu____6029 =
      let uu____6030 =
        let uu____6031 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6031 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6030  in
    FStar_Pprint.op_Hat_Hat uu____6028 uu____6029

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6036 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6036 t phi
      | FStar_Parser_AST.TAnnotated uu____6037 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6042 ->
          let uu____6043 =
            let uu____6044 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6044
             in
          failwith uu____6043
      | FStar_Parser_AST.TVariable uu____6045 ->
          let uu____6046 =
            let uu____6047 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6047
             in
          failwith uu____6046
      | FStar_Parser_AST.NoName uu____6048 ->
          let uu____6049 =
            let uu____6050 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6050
             in
          failwith uu____6049

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6052  ->
      match uu____6052 with
      | (lid,e) ->
          let uu____6059 =
            let uu____6060 = p_qlident lid  in
            let uu____6061 =
              let uu____6062 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6062
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6060 uu____6061  in
          FStar_Pprint.group uu____6059

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6064 when is_general_application e ->
        let uu____6071 = head_and_args e  in
        (match uu____6071 with
         | (head1,args) ->
             let uu____6096 =
               let uu____6107 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6107
               then
                 let uu____6141 =
                   FStar_Util.take
                     (fun uu____6165  ->
                        match uu____6165 with
                        | (uu____6170,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6141 with
                 | (fs_typ_args,args1) ->
                     let uu____6208 =
                       let uu____6209 = p_indexingTerm head1  in
                       let uu____6210 =
                         let uu____6211 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6211 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6209 uu____6210  in
                     (uu____6208, args1)
               else
                 (let uu____6223 = p_indexingTerm head1  in
                  (uu____6223, args))
                in
             (match uu____6096 with
              | (head_doc,args1) ->
                  let uu____6244 =
                    let uu____6245 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6245 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6244))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6265 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6265)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6283 =
               let uu____6284 = p_quident lid  in
               let uu____6285 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6284 uu____6285  in
             FStar_Pprint.group uu____6283
         | hd1::tl1 ->
             let uu____6302 =
               let uu____6303 =
                 let uu____6304 =
                   let uu____6305 = p_quident lid  in
                   let uu____6306 = p_argTerm hd1  in
                   prefix2 uu____6305 uu____6306  in
                 FStar_Pprint.group uu____6304  in
               let uu____6307 =
                 let uu____6308 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6308  in
               FStar_Pprint.op_Hat_Hat uu____6303 uu____6307  in
             FStar_Pprint.group uu____6302)
    | uu____6313 -> p_indexingTerm e

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
         (let uu____6322 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6322 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6324 = str "#"  in
        let uu____6325 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6324 uu____6325
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6327  ->
    match uu____6327 with | (e,uu____6333) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6338;_},e1::e2::[])
          ->
          let uu____6343 =
            let uu____6344 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6345 =
              let uu____6346 =
                let uu____6347 = p_term false false e2  in
                soft_parens_with_nesting uu____6347  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6346  in
            FStar_Pprint.op_Hat_Hat uu____6344 uu____6345  in
          FStar_Pprint.group uu____6343
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6348;_},e1::e2::[])
          ->
          let uu____6353 =
            let uu____6354 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6355 =
              let uu____6356 =
                let uu____6357 = p_term false false e2  in
                soft_brackets_with_nesting uu____6357  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6356  in
            FStar_Pprint.op_Hat_Hat uu____6354 uu____6355  in
          FStar_Pprint.group uu____6353
      | uu____6358 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6363 = p_quident lid  in
        let uu____6364 =
          let uu____6365 =
            let uu____6366 = p_term false false e1  in
            soft_parens_with_nesting uu____6366  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6365  in
        FStar_Pprint.op_Hat_Hat uu____6363 uu____6364
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6372 =
          let uu____6373 = FStar_Ident.text_of_id op  in str uu____6373  in
        let uu____6374 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6372 uu____6374
    | uu____6375 -> p_atomicTermNotQUident e

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
         | uu____6383 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6390 =
          let uu____6391 = FStar_Ident.text_of_id op  in str uu____6391  in
        let uu____6392 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6390 uu____6392
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6396 =
          let uu____6397 =
            let uu____6398 =
              let uu____6399 = FStar_Ident.text_of_id op  in str uu____6399
               in
            let uu____6400 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6398 uu____6400  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6397  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6396
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6415 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6416 =
          let uu____6417 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6418 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6417 p_tmEq uu____6418  in
        let uu____6425 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6415 uu____6416 uu____6425
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6428 =
          let uu____6429 = p_atomicTermNotQUident e1  in
          let uu____6430 =
            let uu____6431 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6431  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6429 uu____6430
           in
        FStar_Pprint.group uu____6428
    | uu____6432 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6437 = p_quident constr_lid  in
        let uu____6438 =
          let uu____6439 =
            let uu____6440 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6440  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6439  in
        FStar_Pprint.op_Hat_Hat uu____6437 uu____6438
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6442 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6442 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6444 = p_term false false e1  in
        soft_parens_with_nesting uu____6444
    | uu____6445 when is_array e ->
        let es = extract_from_list e  in
        let uu____6449 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6450 =
          let uu____6451 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6451
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6454 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6449 uu____6450 uu____6454
    | uu____6455 when is_list e ->
        let uu____6456 =
          let uu____6457 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6458 = extract_from_list e  in
          separate_map_or_flow_last uu____6457
            (fun ps  -> p_noSeqTerm ps false) uu____6458
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6456 FStar_Pprint.rbracket
    | uu____6463 when is_lex_list e ->
        let uu____6464 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6465 =
          let uu____6466 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6467 = extract_from_list e  in
          separate_map_or_flow_last uu____6466
            (fun ps  -> p_noSeqTerm ps false) uu____6467
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6464 uu____6465 FStar_Pprint.rbracket
    | uu____6472 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6476 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6477 =
          let uu____6478 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6478 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6476 uu____6477 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6482 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6483 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6482 uu____6483
    | FStar_Parser_AST.Op (op,args) when
        let uu____6490 = handleable_op op args  in
        Prims.op_Negation uu____6490 ->
        let uu____6491 =
          let uu____6492 =
            let uu____6493 = FStar_Ident.text_of_id op  in
            let uu____6494 =
              let uu____6495 =
                let uu____6496 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6496
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6495  in
            Prims.strcat uu____6493 uu____6494  in
          Prims.strcat "Operation " uu____6492  in
        failwith uu____6491
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6498 = str "u#"  in
        let uu____6499 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6498 uu____6499
    | FStar_Parser_AST.Wild  ->
        let uu____6500 = p_term false false e  in
        soft_parens_with_nesting uu____6500
    | FStar_Parser_AST.Const uu____6501 ->
        let uu____6502 = p_term false false e  in
        soft_parens_with_nesting uu____6502
    | FStar_Parser_AST.Op uu____6503 ->
        let uu____6510 = p_term false false e  in
        soft_parens_with_nesting uu____6510
    | FStar_Parser_AST.Tvar uu____6511 ->
        let uu____6512 = p_term false false e  in
        soft_parens_with_nesting uu____6512
    | FStar_Parser_AST.Var uu____6513 ->
        let uu____6514 = p_term false false e  in
        soft_parens_with_nesting uu____6514
    | FStar_Parser_AST.Name uu____6515 ->
        let uu____6516 = p_term false false e  in
        soft_parens_with_nesting uu____6516
    | FStar_Parser_AST.Construct uu____6517 ->
        let uu____6528 = p_term false false e  in
        soft_parens_with_nesting uu____6528
    | FStar_Parser_AST.Abs uu____6529 ->
        let uu____6536 = p_term false false e  in
        soft_parens_with_nesting uu____6536
    | FStar_Parser_AST.App uu____6537 ->
        let uu____6544 = p_term false false e  in
        soft_parens_with_nesting uu____6544
    | FStar_Parser_AST.Let uu____6545 ->
        let uu____6566 = p_term false false e  in
        soft_parens_with_nesting uu____6566
    | FStar_Parser_AST.LetOpen uu____6567 ->
        let uu____6572 = p_term false false e  in
        soft_parens_with_nesting uu____6572
    | FStar_Parser_AST.Seq uu____6573 ->
        let uu____6578 = p_term false false e  in
        soft_parens_with_nesting uu____6578
    | FStar_Parser_AST.Bind uu____6579 ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586
    | FStar_Parser_AST.If uu____6587 ->
        let uu____6594 = p_term false false e  in
        soft_parens_with_nesting uu____6594
    | FStar_Parser_AST.Match uu____6595 ->
        let uu____6610 = p_term false false e  in
        soft_parens_with_nesting uu____6610
    | FStar_Parser_AST.TryWith uu____6611 ->
        let uu____6626 = p_term false false e  in
        soft_parens_with_nesting uu____6626
    | FStar_Parser_AST.Ascribed uu____6627 ->
        let uu____6636 = p_term false false e  in
        soft_parens_with_nesting uu____6636
    | FStar_Parser_AST.Record uu____6637 ->
        let uu____6650 = p_term false false e  in
        soft_parens_with_nesting uu____6650
    | FStar_Parser_AST.Project uu____6651 ->
        let uu____6656 = p_term false false e  in
        soft_parens_with_nesting uu____6656
    | FStar_Parser_AST.Product uu____6657 ->
        let uu____6664 = p_term false false e  in
        soft_parens_with_nesting uu____6664
    | FStar_Parser_AST.Sum uu____6665 ->
        let uu____6672 = p_term false false e  in
        soft_parens_with_nesting uu____6672
    | FStar_Parser_AST.QForall uu____6673 ->
        let uu____6686 = p_term false false e  in
        soft_parens_with_nesting uu____6686
    | FStar_Parser_AST.QExists uu____6687 ->
        let uu____6700 = p_term false false e  in
        soft_parens_with_nesting uu____6700
    | FStar_Parser_AST.Refine uu____6701 ->
        let uu____6706 = p_term false false e  in
        soft_parens_with_nesting uu____6706
    | FStar_Parser_AST.NamedTyp uu____6707 ->
        let uu____6712 = p_term false false e  in
        soft_parens_with_nesting uu____6712
    | FStar_Parser_AST.Requires uu____6713 ->
        let uu____6720 = p_term false false e  in
        soft_parens_with_nesting uu____6720
    | FStar_Parser_AST.Ensures uu____6721 ->
        let uu____6728 = p_term false false e  in
        soft_parens_with_nesting uu____6728
    | FStar_Parser_AST.Attributes uu____6729 ->
        let uu____6732 = p_term false false e  in
        soft_parens_with_nesting uu____6732
    | FStar_Parser_AST.Quote uu____6733 ->
        let uu____6738 = p_term false false e  in
        soft_parens_with_nesting uu____6738
    | FStar_Parser_AST.VQuote uu____6739 ->
        let uu____6740 = p_term false false e  in
        soft_parens_with_nesting uu____6740
    | FStar_Parser_AST.Antiquote uu____6741 ->
        let uu____6746 = p_term false false e  in
        soft_parens_with_nesting uu____6746

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___94_6747  ->
    match uu___94_6747 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6752) ->
        let uu____6753 = str s  in FStar_Pprint.dquotes uu____6753
    | FStar_Const.Const_bytearray (bytes,uu____6755) ->
        let uu____6760 =
          let uu____6761 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6761  in
        let uu____6762 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6760 uu____6762
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___92_6782 =
          match uu___92_6782 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___93_6788 =
          match uu___93_6788 with
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
       | FStar_Parser_AST.Module (uu____7004,decls) ->
           let uu____7010 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7010
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7019,decls,uu____7021) ->
           let uu____7026 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7026
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7083  ->
         match uu____7083 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7127,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7133,decls,uu____7135) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7184 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7197;
                 FStar_Parser_AST.doc = uu____7198;
                 FStar_Parser_AST.quals = uu____7199;
                 FStar_Parser_AST.attrs = uu____7200;_}::uu____7201 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7207 =
                   let uu____7210 =
                     let uu____7213 = FStar_List.tl ds  in d :: uu____7213
                      in
                   d0 :: uu____7210  in
                 (uu____7207, (d0.FStar_Parser_AST.drange))
             | uu____7218 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7184 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7282 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7282 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7390 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7390, comments1))))))
  