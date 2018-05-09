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
  
let (opinfix4 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Right, [FStar_Util.Inr "**"]) 
let (opinfix3 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37]) 
let (opinfix2 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let (minus_lvl :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inr "-"]) 
let (opinfix1 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let (pipe_right :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inr "|>"]) 
let (opinfix0d :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 36]) 
let (opinfix0c :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62]) 
let (equal : (associativity,token Prims.list) FStar_Pervasives_Native.tuple2)
  = (Left, [FStar_Util.Inr "="]) 
let (opinfix0b :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 38]) 
let (opinfix0a :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Left, [FStar_Util.Inl 124]) 
let (colon_equals :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (NonAssoc, [FStar_Util.Inr ":="]) 
let (amp : (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Right, [FStar_Util.Inr "&"]) 
let (colon_colon :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2) =
  (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___82_1522 =
    match uu___82_1522 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1552  ->
         match uu____1552 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1611 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1611 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1651) ->
          assoc_levels
      | uu____1680 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1716 .
    ('Auu____1716,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1761 =
        FStar_List.tryFind
          (fun uu____1791  ->
             match uu____1791 with
             | (uu____1804,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1761 with
      | FStar_Pervasives_Native.Some ((uu____1826,l1,uu____1828),uu____1829)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1864 =
            let uu____1865 =
              let uu____1866 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1866  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1865
             in
          failwith uu____1864
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1888 = assign_levels level_associativity_spec op  in
    match uu____1888 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list)
  = [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1966 =
      let uu____1975 =
        let uu____1986 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1986  in
      FStar_List.tryFind uu____1975 operatorInfix0ad12  in
    uu____1966 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2068 =
      let uu____2082 =
        let uu____2098 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2098  in
      FStar_List.tryFind uu____2082 opinfix34  in
    uu____2068 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2154 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2154
    then (Prims.parse_int "1")
    else
      (let uu____2156 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2156
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2165 . FStar_Ident.ident -> 'Auu____2165 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2181 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2181 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2183 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2183
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2184 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2184 [".()<-"; ".[]<-"]
      | uu____2185 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2223 .
    ('Auu____2223 -> FStar_Pprint.document) ->
      'Auu____2223 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2264 = FStar_ST.op_Bang comment_stack  in
          match uu____2264 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2327 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2327
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2368 =
                    let uu____2369 =
                      let uu____2370 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2370
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2369  in
                  comments_before_pos uu____2368 print_pos lookahead_pos))
              else
                (let uu____2372 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2372))
           in
        let uu____2373 =
          let uu____2378 =
            let uu____2379 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2379  in
          let uu____2380 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2378 uu____2380  in
        match uu____2373 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2386 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2386
              else comments  in
            let uu____2392 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2392
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2413 = FStar_ST.op_Bang comment_stack  in
          match uu____2413 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2505 =
                    let uu____2506 =
                      let uu____2507 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2507  in
                    uu____2506 - lbegin  in
                  max k uu____2505  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2510 =
                    let uu____2511 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2512 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2511 uu____2512  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2510  in
                let uu____2513 =
                  let uu____2514 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2514  in
                place_comments_until_pos (Prims.parse_int "1") uu____2513
                  pos_end doc2))
          | uu____2515 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2524 =
                     let uu____2525 = FStar_Range.line_of_pos pos_end  in
                     uu____2525 - lbegin  in
                   max (Prims.parse_int "1") uu____2524  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2527 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2527)
  
let separate_map_with_comments :
  'Auu____2540 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2540 -> FStar_Pprint.document) ->
          'Auu____2540 Prims.list ->
            ('Auu____2540 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2597 x =
              match uu____2597 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2611 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2611 doc1
                     in
                  let uu____2612 =
                    let uu____2613 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2613  in
                  let uu____2614 =
                    let uu____2615 =
                      let uu____2616 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2616  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2615  in
                  (uu____2612, uu____2614)
               in
            let uu____2617 =
              let uu____2624 = FStar_List.hd xs  in
              let uu____2625 = FStar_List.tl xs  in (uu____2624, uu____2625)
               in
            match uu____2617 with
            | (x,xs1) ->
                let init1 =
                  let uu____2641 =
                    let uu____2642 =
                      let uu____2643 = extract_range x  in
                      FStar_Range.end_of_range uu____2643  in
                    FStar_Range.line_of_pos uu____2642  in
                  let uu____2644 =
                    let uu____2645 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2645  in
                  (uu____2641, uu____2644)  in
                let uu____2646 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2646
  
let separate_map_with_comments_kw :
  'Auu____2669 'Auu____2670 .
    'Auu____2669 ->
      'Auu____2669 ->
        ('Auu____2669 -> 'Auu____2670 -> FStar_Pprint.document) ->
          'Auu____2670 Prims.list ->
            ('Auu____2670 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2732 x =
              match uu____2732 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2746 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2746 doc1
                     in
                  let uu____2747 =
                    let uu____2748 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2748  in
                  let uu____2749 =
                    let uu____2750 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2750  in
                  (uu____2747, uu____2749)
               in
            let uu____2751 =
              let uu____2758 = FStar_List.hd xs  in
              let uu____2759 = FStar_List.tl xs  in (uu____2758, uu____2759)
               in
            match uu____2751 with
            | (x,xs1) ->
                let init1 =
                  let uu____2775 =
                    let uu____2776 =
                      let uu____2777 = extract_range x  in
                      FStar_Range.end_of_range uu____2777  in
                    FStar_Range.line_of_pos uu____2776  in
                  let uu____2778 = f prefix1 x  in (uu____2775, uu____2778)
                   in
                let uu____2779 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2779
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3489)) ->
          let uu____3492 =
            let uu____3493 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3493 FStar_Util.is_upper  in
          if uu____3492
          then
            let uu____3494 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3494 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3496 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3503 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3504 =
      let uu____3505 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3506 =
        let uu____3507 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3507  in
      FStar_Pprint.op_Hat_Hat uu____3505 uu____3506  in
    FStar_Pprint.op_Hat_Hat uu____3503 uu____3504

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3509 ->
        let uu____3510 =
          let uu____3511 = str "@ "  in
          let uu____3512 =
            let uu____3513 =
              let uu____3514 =
                let uu____3515 =
                  let uu____3516 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3516  in
                FStar_Pprint.op_Hat_Hat uu____3515 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3514  in
            FStar_Pprint.op_Hat_Hat uu____3513 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3511 uu____3512  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3510

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3519  ->
    match uu____3519 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3555 =
                match uu____3555 with
                | (kwd,arg) ->
                    let uu____3562 = str "@"  in
                    let uu____3563 =
                      let uu____3564 = str kwd  in
                      let uu____3565 =
                        let uu____3566 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3566
                         in
                      FStar_Pprint.op_Hat_Hat uu____3564 uu____3565  in
                    FStar_Pprint.op_Hat_Hat uu____3562 uu____3563
                 in
              let uu____3567 =
                let uu____3568 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3568 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3567
           in
        let uu____3573 =
          let uu____3574 =
            let uu____3575 =
              let uu____3576 =
                let uu____3577 = str doc1  in
                let uu____3578 =
                  let uu____3579 =
                    let uu____3580 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3580  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3579  in
                FStar_Pprint.op_Hat_Hat uu____3577 uu____3578  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3576  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3575  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3574  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3573

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3584 =
          let uu____3585 = str "val"  in
          let uu____3586 =
            let uu____3587 =
              let uu____3588 = p_lident lid  in
              let uu____3589 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3588 uu____3589  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3587  in
          FStar_Pprint.op_Hat_Hat uu____3585 uu____3586  in
        let uu____3590 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3584 uu____3590
    | FStar_Parser_AST.TopLevelLet (uu____3591,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3616 =
               let uu____3617 = str "let"  in p_letlhs uu____3617 lb  in
             FStar_Pprint.group uu____3616) lbs
    | uu____3618 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___83_3633 =
          match uu___83_3633 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3641 = f x  in
              let uu____3642 =
                let uu____3643 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3643  in
              FStar_Pprint.op_Hat_Hat uu____3641 uu____3642
           in
        let uu____3644 = str "["  in
        let uu____3645 =
          let uu____3646 = p_list' l  in
          let uu____3647 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3646 uu____3647  in
        FStar_Pprint.op_Hat_Hat uu____3644 uu____3645

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3650 =
          let uu____3651 = str "open"  in
          let uu____3652 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3651 uu____3652  in
        FStar_Pprint.group uu____3650
    | FStar_Parser_AST.Include uid ->
        let uu____3654 =
          let uu____3655 = str "include"  in
          let uu____3656 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3655 uu____3656  in
        FStar_Pprint.group uu____3654
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3659 =
          let uu____3660 = str "module"  in
          let uu____3661 =
            let uu____3662 =
              let uu____3663 = p_uident uid1  in
              let uu____3664 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3663 uu____3664  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3662  in
          FStar_Pprint.op_Hat_Hat uu____3660 uu____3661  in
        let uu____3665 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3659 uu____3665
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3667 =
          let uu____3668 = str "module"  in
          let uu____3669 =
            let uu____3670 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3670  in
          FStar_Pprint.op_Hat_Hat uu____3668 uu____3669  in
        FStar_Pprint.group uu____3667
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3703 = str "effect"  in
          let uu____3704 =
            let uu____3705 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3705  in
          FStar_Pprint.op_Hat_Hat uu____3703 uu____3704  in
        let uu____3706 =
          let uu____3707 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3707 FStar_Pprint.equals
           in
        let uu____3708 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3706 uu____3708
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3726 =
          let uu____3727 = str "type"  in
          let uu____3728 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3727 uu____3728  in
        let uu____3741 =
          let uu____3742 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3780 =
                    let uu____3781 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3781 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3780)) uu____3742
           in
        FStar_Pprint.op_Hat_Hat uu____3726 uu____3741
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3797 = str "let"  in
          let uu____3798 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3797 uu____3798  in
        let uu____3799 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3799 p_letbinding lbs
          (fun uu____3807  ->
             match uu____3807 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3816 = str "val"  in
        let uu____3817 =
          let uu____3818 =
            let uu____3819 = p_lident lid  in
            let uu____3820 =
              let uu____3821 =
                let uu____3822 =
                  let uu____3823 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3823  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3822  in
              FStar_Pprint.group uu____3821  in
            FStar_Pprint.op_Hat_Hat uu____3819 uu____3820  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3818  in
        FStar_Pprint.op_Hat_Hat uu____3816 uu____3817
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3827 =
            let uu____3828 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3828 FStar_Util.is_upper  in
          if uu____3827
          then FStar_Pprint.empty
          else
            (let uu____3830 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3830 FStar_Pprint.space)
           in
        let uu____3831 =
          let uu____3832 = p_ident id1  in
          let uu____3833 =
            let uu____3834 =
              let uu____3835 =
                let uu____3836 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3836  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3835  in
            FStar_Pprint.group uu____3834  in
          FStar_Pprint.op_Hat_Hat uu____3832 uu____3833  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3831
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3843 = str "exception"  in
        let uu____3844 =
          let uu____3845 =
            let uu____3846 = p_uident uid  in
            let uu____3847 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3851 =
                     let uu____3852 = str "of"  in
                     let uu____3853 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3852 uu____3853  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3851) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3846 uu____3847  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3845  in
        FStar_Pprint.op_Hat_Hat uu____3843 uu____3844
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3855 = str "new_effect"  in
        let uu____3856 =
          let uu____3857 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3857  in
        FStar_Pprint.op_Hat_Hat uu____3855 uu____3856
    | FStar_Parser_AST.SubEffect se ->
        let uu____3859 = str "sub_effect"  in
        let uu____3860 =
          let uu____3861 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3861  in
        FStar_Pprint.op_Hat_Hat uu____3859 uu____3860
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3864 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3864 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3865 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3866) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3889 = str "%splice"  in
        let uu____3890 =
          let uu____3891 =
            let uu____3892 = str ";"  in p_list p_uident uu____3892 ids  in
          let uu____3893 =
            let uu____3894 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3894  in
          FStar_Pprint.op_Hat_Hat uu____3891 uu____3893  in
        FStar_Pprint.op_Hat_Hat uu____3889 uu____3890

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___84_3895  ->
    match uu___84_3895 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3897 = str "#set-options"  in
        let uu____3898 =
          let uu____3899 =
            let uu____3900 = str s  in FStar_Pprint.dquotes uu____3900  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3899  in
        FStar_Pprint.op_Hat_Hat uu____3897 uu____3898
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3904 = str "#reset-options"  in
        let uu____3905 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3909 =
                 let uu____3910 = str s  in FStar_Pprint.dquotes uu____3910
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3909) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3904 uu____3905
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
    fun uu____3939  ->
      match uu____3939 with
      | (typedecl,fsdoc_opt) ->
          let uu____3952 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3952 with
           | (decl,body) ->
               let uu____3970 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3970)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___85_3972  ->
      match uu___85_3972 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4002 = FStar_Pprint.empty  in
          let uu____4003 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4003, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4024 =
            let uu____4025 = p_typ false false t  in jump2 uu____4025  in
          let uu____4026 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4026, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4080 =
            match uu____4080 with
            | (lid1,t,doc_opt) ->
                let uu____4096 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4096
             in
          let p_fields uu____4112 =
            let uu____4113 =
              let uu____4114 =
                let uu____4115 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4115 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4114  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4113  in
          let uu____4124 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4124, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4185 =
            match uu____4185 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4211 =
                    let uu____4212 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4212  in
                  FStar_Range.extend_to_end_of_line uu____4211  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4238 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4251 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4251,
            ((fun uu____4257  ->
                let uu____4258 = datacon_doc ()  in jump2 uu____4258)))

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
  fun uu____4259  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4259 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4293 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4293  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4295 =
                        let uu____4298 =
                          let uu____4301 = p_fsdoc fsdoc  in
                          let uu____4302 =
                            let uu____4305 = cont lid_doc  in [uu____4305]
                             in
                          uu____4301 :: uu____4302  in
                        kw :: uu____4298  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4295
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4310 =
                        let uu____4311 =
                          let uu____4312 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4312 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4311
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4310
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4327 =
                          let uu____4328 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4328  in
                        prefix2 uu____4327 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4330  ->
      match uu____4330 with
      | (lid,t,doc_opt) ->
          let uu____4346 =
            let uu____4347 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4348 =
              let uu____4349 = p_lident lid  in
              let uu____4350 =
                let uu____4351 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4351  in
              FStar_Pprint.op_Hat_Hat uu____4349 uu____4350  in
            FStar_Pprint.op_Hat_Hat uu____4347 uu____4348  in
          FStar_Pprint.group uu____4346

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4352  ->
    match uu____4352 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4380 =
            let uu____4381 =
              let uu____4382 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4382  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4381  in
          FStar_Pprint.group uu____4380  in
        let uu____4383 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4384 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4388 =
                 let uu____4389 =
                   let uu____4390 =
                     let uu____4391 =
                       let uu____4392 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4392
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4391  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4390  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4389  in
               FStar_Pprint.group uu____4388) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4383 uu____4384

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4394  ->
      match uu____4394 with
      | (pat,uu____4400) ->
          let uu____4401 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4420 =
                  let uu____4421 =
                    let uu____4422 =
                      let uu____4423 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4423
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4422  in
                  FStar_Pprint.group uu____4421  in
                (pat1, uu____4420)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4435 =
                  let uu____4436 =
                    let uu____4437 =
                      let uu____4438 =
                        let uu____4439 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4439
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4438
                       in
                    FStar_Pprint.group uu____4437  in
                  let uu____4440 =
                    let uu____4441 =
                      let uu____4442 = str "by"  in
                      let uu____4443 =
                        let uu____4444 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4444
                         in
                      FStar_Pprint.op_Hat_Hat uu____4442 uu____4443  in
                    FStar_Pprint.group uu____4441  in
                  FStar_Pprint.op_Hat_Hat uu____4436 uu____4440  in
                (pat1, uu____4435)
            | uu____4445 -> (pat, FStar_Pprint.empty)  in
          (match uu____4401 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4449);
                       FStar_Parser_AST.prange = uu____4450;_},pats)
                    ->
                    let uu____4460 =
                      let uu____4461 =
                        let uu____4462 =
                          let uu____4463 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4463  in
                        FStar_Pprint.group uu____4462  in
                      let uu____4464 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4461 uu____4464  in
                    prefix2_nonempty uu____4460 ascr_doc
                | uu____4465 ->
                    let uu____4466 =
                      let uu____4467 =
                        let uu____4468 =
                          let uu____4469 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4469  in
                        FStar_Pprint.group uu____4468  in
                      FStar_Pprint.op_Hat_Hat uu____4467 ascr_doc  in
                    FStar_Pprint.group uu____4466))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4471  ->
      match uu____4471 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4480 =
            let uu____4481 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4481  in
          let uu____4482 =
            let uu____4483 =
              let uu____4484 =
                let uu____4485 =
                  let uu____4486 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4486  in
                FStar_Pprint.group uu____4485  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4484  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4483  in
          FStar_Pprint.ifflat uu____4480 uu____4482

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___86_4487  ->
    match uu___86_4487 with
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
        let uu____4512 = p_uident uid  in
        let uu____4513 = p_binders true bs  in
        let uu____4514 =
          let uu____4515 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4515  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4512 uu____4513 uu____4514

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
          let uu____4525 =
            let uu____4526 =
              let uu____4527 =
                let uu____4528 = p_uident uid  in
                let uu____4529 = p_binders true bs  in
                let uu____4530 =
                  let uu____4531 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4531  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4528 uu____4529 uu____4530
                 in
              FStar_Pprint.group uu____4527  in
            let uu____4532 =
              let uu____4533 = str "with"  in
              let uu____4534 =
                let uu____4535 =
                  let uu____4536 =
                    let uu____4537 =
                      let uu____4538 =
                        let uu____4539 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4539
                         in
                      separate_map_last uu____4538 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4537  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4536  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4535  in
              FStar_Pprint.op_Hat_Hat uu____4533 uu____4534  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4526 uu____4532  in
          braces_with_nesting uu____4525

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
          let uu____4570 =
            let uu____4571 = p_lident lid  in
            let uu____4572 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4571 uu____4572  in
          let uu____4573 = p_simpleTerm ps false e  in
          prefix2 uu____4570 uu____4573
      | uu____4574 ->
          let uu____4575 =
            let uu____4576 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4576
             in
          failwith uu____4575

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4638 =
        match uu____4638 with
        | (kwd,t) ->
            let uu____4645 =
              let uu____4646 = str kwd  in
              let uu____4647 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4646 uu____4647  in
            let uu____4648 = p_simpleTerm ps false t  in
            prefix2 uu____4645 uu____4648
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4653 =
      let uu____4654 =
        let uu____4655 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4656 =
          let uu____4657 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4657  in
        FStar_Pprint.op_Hat_Hat uu____4655 uu____4656  in
      let uu____4658 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4654 uu____4658  in
    let uu____4659 =
      let uu____4660 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4660  in
    FStar_Pprint.op_Hat_Hat uu____4653 uu____4659

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___87_4661  ->
    match uu___87_4661 with
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
    | uu____4663 ->
        let uu____4664 =
          let uu____4665 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4665  in
        FStar_Pprint.op_Hat_Hat uu____4664 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___88_4668  ->
    match uu___88_4668 with
    | FStar_Parser_AST.Rec  ->
        let uu____4669 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4669
    | FStar_Parser_AST.Mutable  ->
        let uu____4670 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4670
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___89_4671  ->
    match uu___89_4671 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4676 =
          let uu____4677 =
            let uu____4678 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4678  in
          FStar_Pprint.separate_map uu____4677 p_tuplePattern pats  in
        FStar_Pprint.group uu____4676
    | uu____4679 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4686 =
          let uu____4687 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4687 p_constructorPattern pats  in
        FStar_Pprint.group uu____4686
    | uu____4688 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4691;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4696 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4697 = p_constructorPattern hd1  in
        let uu____4698 = p_constructorPattern tl1  in
        infix0 uu____4696 uu____4697 uu____4698
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4700;_},pats)
        ->
        let uu____4706 = p_quident uid  in
        let uu____4707 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4706 uu____4707
    | uu____4708 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4724;
               FStar_Parser_AST.blevel = uu____4725;
               FStar_Parser_AST.aqual = uu____4726;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4732 =
               let uu____4733 = p_ident lid  in
               p_refinement aqual uu____4733 t1 phi  in
             soft_parens_with_nesting uu____4732
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4735;
               FStar_Parser_AST.blevel = uu____4736;
               FStar_Parser_AST.aqual = uu____4737;_},phi))
             ->
             let uu____4739 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4739
         | uu____4740 ->
             let uu____4745 =
               let uu____4746 = p_tuplePattern pat  in
               let uu____4747 =
                 let uu____4748 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4748
                  in
               FStar_Pprint.op_Hat_Hat uu____4746 uu____4747  in
             soft_parens_with_nesting uu____4745)
    | FStar_Parser_AST.PatList pats ->
        let uu____4752 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4752 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4769 =
          match uu____4769 with
          | (lid,pat) ->
              let uu____4776 = p_qlident lid  in
              let uu____4777 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4776 uu____4777
           in
        let uu____4778 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4778
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4788 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4789 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4790 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4788 uu____4789 uu____4790
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4799 =
          let uu____4800 =
            let uu____4801 =
              let uu____4802 = FStar_Ident.text_of_id op  in str uu____4802
               in
            let uu____4803 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4801 uu____4803  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4800  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4799
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4811 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4812 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4811 uu____4812
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4814 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4817;
           FStar_Parser_AST.prange = uu____4818;_},uu____4819)
        ->
        let uu____4824 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4824
    | FStar_Parser_AST.PatTuple (uu____4825,false ) ->
        let uu____4830 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4830
    | uu____4831 ->
        let uu____4832 =
          let uu____4833 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4833  in
        failwith uu____4832

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4835;_},uu____4836)
        -> true
    | uu____4841 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4845 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4846 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4845 uu____4846
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4853;
                   FStar_Parser_AST.blevel = uu____4854;
                   FStar_Parser_AST.aqual = uu____4855;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4857 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4857 t1 phi
            | uu____4858 ->
                let t' =
                  let uu____4860 = is_typ_tuple t  in
                  if uu____4860
                  then
                    let uu____4861 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4861
                  else p_tmFormula t  in
                let uu____4863 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4864 =
                  let uu____4865 = p_lident lid  in
                  let uu____4866 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4865 uu____4866  in
                FStar_Pprint.op_Hat_Hat uu____4863 uu____4864
             in
          if is_atomic
          then
            let uu____4867 =
              let uu____4868 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4868  in
            FStar_Pprint.group uu____4867
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4870 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4877;
                  FStar_Parser_AST.blevel = uu____4878;
                  FStar_Parser_AST.aqual = uu____4879;_},phi)
               ->
               if is_atomic
               then
                 let uu____4881 =
                   let uu____4882 =
                     let uu____4883 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4883 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4882  in
                 FStar_Pprint.group uu____4881
               else
                 (let uu____4885 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4885)
           | uu____4886 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4895 -> false
            | FStar_Parser_AST.App uu____4906 -> false
            | FStar_Parser_AST.Op uu____4913 -> false
            | uu____4920 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4924 =
            let uu____4925 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4926 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4925 uu____4926  in
          let uu____4927 =
            let uu____4928 = p_appTerm t  in
            let uu____4929 =
              let uu____4930 =
                let uu____4931 =
                  let uu____4932 = soft_braces_with_nesting_tight phi1  in
                  let uu____4933 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4932 uu____4933  in
                FStar_Pprint.group uu____4931  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4930
               in
            FStar_Pprint.op_Hat_Hat uu____4928 uu____4929  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4924 uu____4927

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4944 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4944

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4949 = FStar_Ident.text_of_id lid  in str uu____4949)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4952 = FStar_Ident.text_of_lid lid  in str uu____4952)

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
            let uu____4975 =
              let uu____4976 =
                let uu____4977 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4977 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4976  in
            let uu____4978 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4975 uu____4978
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4982 =
              let uu____4983 =
                let uu____4984 =
                  let uu____4985 = p_lident x  in
                  let uu____4986 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4985 uu____4986  in
                let uu____4987 =
                  let uu____4988 = p_noSeqTerm true false e1  in
                  let uu____4989 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4988 uu____4989  in
                op_Hat_Slash_Plus_Hat uu____4984 uu____4987  in
              FStar_Pprint.group uu____4983  in
            let uu____4990 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4982 uu____4990
        | uu____4991 ->
            let uu____4992 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4992

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
            let uu____5003 =
              let uu____5004 = p_tmIff e1  in
              let uu____5005 =
                let uu____5006 =
                  let uu____5007 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5007
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5006  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5004 uu____5005  in
            FStar_Pprint.group uu____5003
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5013 =
              let uu____5014 = p_tmIff e1  in
              let uu____5015 =
                let uu____5016 =
                  let uu____5017 =
                    let uu____5018 = p_typ false false t  in
                    let uu____5019 =
                      let uu____5020 = str "by"  in
                      let uu____5021 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5020 uu____5021  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5019  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5017
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5016  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5014 uu____5015  in
            FStar_Pprint.group uu____5013
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5022;_},e1::e2::e3::[])
            ->
            let uu____5028 =
              let uu____5029 =
                let uu____5030 =
                  let uu____5031 = p_atomicTermNotQUident e1  in
                  let uu____5032 =
                    let uu____5033 =
                      let uu____5034 =
                        let uu____5035 = p_term false false e2  in
                        soft_parens_with_nesting uu____5035  in
                      let uu____5036 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5034 uu____5036  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5033  in
                  FStar_Pprint.op_Hat_Hat uu____5031 uu____5032  in
                FStar_Pprint.group uu____5030  in
              let uu____5037 =
                let uu____5038 = p_noSeqTerm ps pb e3  in jump2 uu____5038
                 in
              FStar_Pprint.op_Hat_Hat uu____5029 uu____5037  in
            FStar_Pprint.group uu____5028
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5039;_},e1::e2::e3::[])
            ->
            let uu____5045 =
              let uu____5046 =
                let uu____5047 =
                  let uu____5048 = p_atomicTermNotQUident e1  in
                  let uu____5049 =
                    let uu____5050 =
                      let uu____5051 =
                        let uu____5052 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5052  in
                      let uu____5053 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5051 uu____5053  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5050  in
                  FStar_Pprint.op_Hat_Hat uu____5048 uu____5049  in
                FStar_Pprint.group uu____5047  in
              let uu____5054 =
                let uu____5055 = p_noSeqTerm ps pb e3  in jump2 uu____5055
                 in
              FStar_Pprint.op_Hat_Hat uu____5046 uu____5054  in
            FStar_Pprint.group uu____5045
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5063 =
              let uu____5064 = str "requires"  in
              let uu____5065 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5064 uu____5065  in
            FStar_Pprint.group uu____5063
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5073 =
              let uu____5074 = str "ensures"  in
              let uu____5075 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5074 uu____5075  in
            FStar_Pprint.group uu____5073
        | FStar_Parser_AST.Attributes es ->
            let uu____5079 =
              let uu____5080 = str "attributes"  in
              let uu____5081 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5080 uu____5081  in
            FStar_Pprint.group uu____5079
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5085 =
                let uu____5086 =
                  let uu____5087 = str "if"  in
                  let uu____5088 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5087 uu____5088  in
                let uu____5089 =
                  let uu____5090 = str "then"  in
                  let uu____5091 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5090 uu____5091  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5086 uu____5089  in
              FStar_Pprint.group uu____5085
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5094,uu____5095,e31) when
                     is_unit e31 ->
                     let uu____5097 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5097
                 | uu____5098 -> p_noSeqTerm false false e2  in
               let uu____5099 =
                 let uu____5100 =
                   let uu____5101 = str "if"  in
                   let uu____5102 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5101 uu____5102  in
                 let uu____5103 =
                   let uu____5104 =
                     let uu____5105 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5105 e2_doc  in
                   let uu____5106 =
                     let uu____5107 = str "else"  in
                     let uu____5108 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5107 uu____5108  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5104 uu____5106  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5100 uu____5103  in
               FStar_Pprint.group uu____5099)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5131 =
              let uu____5132 =
                let uu____5133 =
                  let uu____5134 = str "try"  in
                  let uu____5135 = p_noSeqTerm false false e1  in
                  prefix2 uu____5134 uu____5135  in
                let uu____5136 =
                  let uu____5137 = str "with"  in
                  let uu____5138 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5137 uu____5138  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5133 uu____5136  in
              FStar_Pprint.group uu____5132  in
            let uu____5147 = paren_if (ps || pb)  in uu____5147 uu____5131
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5174 =
              let uu____5175 =
                let uu____5176 =
                  let uu____5177 = str "match"  in
                  let uu____5178 = p_noSeqTerm false false e1  in
                  let uu____5179 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5177 uu____5178 uu____5179
                   in
                let uu____5180 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5176 uu____5180  in
              FStar_Pprint.group uu____5175  in
            let uu____5189 = paren_if (ps || pb)  in uu____5189 uu____5174
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5196 =
              let uu____5197 =
                let uu____5198 =
                  let uu____5199 = str "let open"  in
                  let uu____5200 = p_quident uid  in
                  let uu____5201 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5199 uu____5200 uu____5201
                   in
                let uu____5202 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5198 uu____5202  in
              FStar_Pprint.group uu____5197  in
            let uu____5203 = paren_if ps  in uu____5203 uu____5196
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5267 is_last =
              match uu____5267 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5300 =
                          let uu____5301 = str "let"  in
                          let uu____5302 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5301 uu____5302
                           in
                        FStar_Pprint.group uu____5300
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5303 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5308 =
                    if is_last
                    then
                      let uu____5309 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5310 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5309 doc_expr uu____5310
                    else
                      (let uu____5312 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5312)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5308
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5358 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5358
                     else
                       (let uu____5366 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5366)) lbs
               in
            let lbs_doc =
              let uu____5374 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5374  in
            let uu____5375 =
              let uu____5376 =
                let uu____5377 =
                  let uu____5378 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5378
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5377  in
              FStar_Pprint.group uu____5376  in
            let uu____5379 = paren_if ps  in uu____5379 uu____5375
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5386;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5389;
                                                             FStar_Parser_AST.level
                                                               = uu____5390;_})
            when matches_var maybe_x x ->
            let uu____5417 =
              let uu____5418 =
                let uu____5419 = str "function"  in
                let uu____5420 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5419 uu____5420  in
              FStar_Pprint.group uu____5418  in
            let uu____5429 = paren_if (ps || pb)  in uu____5429 uu____5417
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5435 =
              let uu____5436 = str "quote"  in
              let uu____5437 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5436 uu____5437  in
            FStar_Pprint.group uu____5435
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5439 =
              let uu____5440 = str "`"  in
              let uu____5441 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5440 uu____5441  in
            FStar_Pprint.group uu____5439
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5443 =
              let uu____5444 = str "%`"  in
              let uu____5445 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5444 uu____5445  in
            FStar_Pprint.group uu____5443
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5447 =
              let uu____5448 = str "`#"  in
              let uu____5449 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5448 uu____5449  in
            FStar_Pprint.group uu____5447
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5451 =
              let uu____5452 = str "`@"  in
              let uu____5453 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5452 uu____5453  in
            FStar_Pprint.group uu____5451
        | uu____5454 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___90_5455  ->
    match uu___90_5455 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5467 =
          let uu____5468 = str "[@"  in
          let uu____5469 =
            let uu____5470 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5471 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5470 uu____5471  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5468 uu____5469  in
        FStar_Pprint.group uu____5467

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
                 let uu____5497 =
                   let uu____5498 =
                     let uu____5499 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5499 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5498 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5497 term_doc
             | pats ->
                 let uu____5505 =
                   let uu____5506 =
                     let uu____5507 =
                       let uu____5508 =
                         let uu____5509 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5509
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5508 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5510 = p_trigger trigger  in
                     prefix2 uu____5507 uu____5510  in
                   FStar_Pprint.group uu____5506  in
                 prefix2 uu____5505 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5530 =
                   let uu____5531 =
                     let uu____5532 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5532 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5531 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5530 term_doc
             | pats ->
                 let uu____5538 =
                   let uu____5539 =
                     let uu____5540 =
                       let uu____5541 =
                         let uu____5542 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5542
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5541 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5543 = p_trigger trigger  in
                     prefix2 uu____5540 uu____5543  in
                   FStar_Pprint.group uu____5539  in
                 prefix2 uu____5538 term_doc)
        | uu____5544 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5546 -> str "forall"
    | FStar_Parser_AST.QExists uu____5559 -> str "exists"
    | uu____5572 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___91_5573  ->
    match uu___91_5573 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5585 =
          let uu____5586 =
            let uu____5587 =
              let uu____5588 = str "pattern"  in
              let uu____5589 =
                let uu____5590 =
                  let uu____5591 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5591
                   in
                FStar_Pprint.op_Hat_Hat uu____5590 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5588 uu____5589  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5587  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5586  in
        FStar_Pprint.group uu____5585

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5597 = str "\\/"  in
    FStar_Pprint.separate_map uu____5597 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5603 =
      let uu____5604 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5604 p_appTerm pats  in
    FStar_Pprint.group uu____5603

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5614 =
              let uu____5615 =
                let uu____5616 = str "fun"  in
                let uu____5617 =
                  let uu____5618 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5618
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5616 uu____5617  in
              let uu____5619 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5615 uu____5619  in
            let uu____5620 = paren_if ps  in uu____5620 uu____5614
        | uu____5625 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5629  ->
      match uu____5629 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5652 =
                    let uu____5653 =
                      let uu____5654 =
                        let uu____5655 = p_tuplePattern p  in
                        let uu____5656 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5655 uu____5656  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5654
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5653  in
                  FStar_Pprint.group uu____5652
              | FStar_Pervasives_Native.Some f ->
                  let uu____5658 =
                    let uu____5659 =
                      let uu____5660 =
                        let uu____5661 =
                          let uu____5662 =
                            let uu____5663 = p_tuplePattern p  in
                            let uu____5664 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5663
                              uu____5664
                             in
                          FStar_Pprint.group uu____5662  in
                        let uu____5665 =
                          let uu____5666 =
                            let uu____5669 = p_tmFormula f  in
                            [uu____5669; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5666  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5661 uu____5665
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5660
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5659  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5658
               in
            let uu____5670 =
              let uu____5671 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5671  in
            FStar_Pprint.group uu____5670  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5680 =
                      let uu____5681 =
                        let uu____5682 =
                          let uu____5683 =
                            let uu____5684 =
                              let uu____5685 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5685  in
                            FStar_Pprint.separate_map uu____5684
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5683
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5682
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5681  in
                    FStar_Pprint.group uu____5680
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5686 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5688;_},e1::e2::[])
        ->
        let uu____5693 = str "<==>"  in
        let uu____5694 = p_tmImplies e1  in
        let uu____5695 = p_tmIff e2  in
        infix0 uu____5693 uu____5694 uu____5695
    | uu____5696 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5698;_},e1::e2::[])
        ->
        let uu____5703 = str "==>"  in
        let uu____5704 = p_tmArrow p_tmFormula e1  in
        let uu____5705 = p_tmImplies e2  in
        infix0 uu____5703 uu____5704 uu____5705
    | uu____5706 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5714 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5714 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5735 ->
               let uu____5736 =
                 let uu____5737 =
                   let uu____5738 =
                     let uu____5739 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5739
                      in
                   FStar_Pprint.separate uu____5738 terms  in
                 let uu____5740 =
                   let uu____5741 =
                     let uu____5742 =
                       let uu____5743 =
                         let uu____5744 =
                           let uu____5745 =
                             let uu____5746 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5746
                              in
                           FStar_Pprint.separate uu____5745 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5744 last_op  in
                       let uu____5747 =
                         let uu____5748 =
                           let uu____5749 =
                             let uu____5750 =
                               let uu____5751 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5751
                                in
                             FStar_Pprint.separate uu____5750 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5749 last_op  in
                         jump2 uu____5748  in
                       FStar_Pprint.ifflat uu____5743 uu____5747  in
                     FStar_Pprint.group uu____5742  in
                   let uu____5752 = FStar_List.hd last1  in
                   prefix2 uu____5741 uu____5752  in
                 FStar_Pprint.ifflat uu____5737 uu____5740  in
               FStar_Pprint.group uu____5736)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5765 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5770 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5765 uu____5770
      | uu____5773 -> let uu____5774 = p_Tm e  in [uu____5774]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5777 =
        let uu____5778 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5778 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5777  in
    let disj =
      let uu____5780 =
        let uu____5781 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5781 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5780  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5800;_},e1::e2::[])
        ->
        let uu____5805 = p_tmDisjunction e1  in
        let uu____5810 = let uu____5815 = p_tmConjunction e2  in [uu____5815]
           in
        FStar_List.append uu____5805 uu____5810
    | uu____5824 -> let uu____5825 = p_tmConjunction e  in [uu____5825]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5835;_},e1::e2::[])
        ->
        let uu____5840 = p_tmConjunction e1  in
        let uu____5843 = let uu____5846 = p_tmTuple e2  in [uu____5846]  in
        FStar_List.append uu____5840 uu____5843
    | uu____5847 -> let uu____5848 = p_tmTuple e  in [uu____5848]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5865 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5865
          (fun uu____5873  ->
             match uu____5873 with | (e1,uu____5879) -> p_tmEq e1) args
    | uu____5880 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5885 =
             let uu____5886 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5886  in
           FStar_Pprint.group uu____5885)

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
               (let uu____5927 = FStar_Ident.text_of_id op  in
                uu____5927 = "="))
              ||
              (let uu____5929 = FStar_Ident.text_of_id op  in
               uu____5929 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5931 = levels op1  in
            (match uu____5931 with
             | (left1,mine,right1) ->
                 let uu____5941 =
                   let uu____5942 = FStar_All.pipe_left str op1  in
                   let uu____5943 = p_tmEqWith' p_X left1 e1  in
                   let uu____5944 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5942 uu____5943 uu____5944  in
                 paren_if_gt curr mine uu____5941)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5945;_},e1::e2::[])
            ->
            let uu____5950 =
              let uu____5951 = p_tmEqWith p_X e1  in
              let uu____5952 =
                let uu____5953 =
                  let uu____5954 =
                    let uu____5955 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5955  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5954  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5953  in
              FStar_Pprint.op_Hat_Hat uu____5951 uu____5952  in
            FStar_Pprint.group uu____5950
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5956;_},e1::[])
            ->
            let uu____5960 = levels "-"  in
            (match uu____5960 with
             | (left1,mine,right1) ->
                 let uu____5970 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5970)
        | uu____5971 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____6015)::(e2,uu____6017)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6037 = is_list e  in Prims.op_Negation uu____6037)
              ->
              let op = "::"  in
              let uu____6039 = levels op  in
              (match uu____6039 with
               | (left1,mine,right1) ->
                   let uu____6049 =
                     let uu____6050 = str op  in
                     let uu____6051 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6052 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6050 uu____6051 uu____6052  in
                   paren_if_gt curr mine uu____6049)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6060 = levels op  in
              (match uu____6060 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6076 = p_binder false b  in
                     let uu____6077 =
                       let uu____6078 =
                         let uu____6079 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6079 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6078
                        in
                     FStar_Pprint.op_Hat_Hat uu____6076 uu____6077  in
                   let uu____6080 =
                     let uu____6081 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6082 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6081 uu____6082  in
                   paren_if_gt curr mine uu____6080)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6083;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6112 = levels op  in
              (match uu____6112 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6122 = str op  in
                     let uu____6123 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6124 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6122 uu____6123 uu____6124
                   else
                     (let uu____6126 =
                        let uu____6127 = str op  in
                        let uu____6128 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6129 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6127 uu____6128 uu____6129  in
                      paren_if_gt curr mine uu____6126))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6136 = levels op1  in
              (match uu____6136 with
               | (left1,mine,right1) ->
                   let uu____6146 =
                     let uu____6147 = str op1  in
                     let uu____6148 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6149 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6147 uu____6148 uu____6149  in
                   paren_if_gt curr mine uu____6146)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6168 =
                let uu____6169 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6170 =
                  let uu____6171 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6171 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6169 uu____6170  in
              braces_with_nesting uu____6168
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6176;_},e1::[])
              ->
              let uu____6180 =
                let uu____6181 = str "~"  in
                let uu____6182 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6181 uu____6182  in
              FStar_Pprint.group uu____6180
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6184;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6190 = levels op  in
                   (match uu____6190 with
                    | (left1,mine,right1) ->
                        let uu____6200 =
                          let uu____6201 = str op  in
                          let uu____6202 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6203 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6201 uu____6202 uu____6203  in
                        paren_if_gt curr mine uu____6200)
               | uu____6204 -> p_X e)
          | uu____6205 -> p_X e

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
        let uu____6212 =
          let uu____6213 = p_lident lid  in
          let uu____6214 =
            let uu____6215 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6215  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6213 uu____6214  in
        FStar_Pprint.group uu____6212
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6218 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6220 = p_appTerm e  in
    let uu____6221 =
      let uu____6222 =
        let uu____6223 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6223 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6222  in
    FStar_Pprint.op_Hat_Hat uu____6220 uu____6221

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6228 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6228 t phi
      | FStar_Parser_AST.TAnnotated uu____6229 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6234 ->
          let uu____6235 =
            let uu____6236 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6236
             in
          failwith uu____6235
      | FStar_Parser_AST.TVariable uu____6237 ->
          let uu____6238 =
            let uu____6239 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6239
             in
          failwith uu____6238
      | FStar_Parser_AST.NoName uu____6240 ->
          let uu____6241 =
            let uu____6242 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6242
             in
          failwith uu____6241

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6244  ->
      match uu____6244 with
      | (lid,e) ->
          let uu____6251 =
            let uu____6252 = p_qlident lid  in
            let uu____6253 =
              let uu____6254 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6254
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6252 uu____6253  in
          FStar_Pprint.group uu____6251

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6256 when is_general_application e ->
        let uu____6263 = head_and_args e  in
        (match uu____6263 with
         | (head1,args) ->
             let uu____6288 =
               let uu____6299 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6299
               then
                 let uu____6333 =
                   FStar_Util.take
                     (fun uu____6357  ->
                        match uu____6357 with
                        | (uu____6362,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6333 with
                 | (fs_typ_args,args1) ->
                     let uu____6400 =
                       let uu____6401 = p_indexingTerm head1  in
                       let uu____6402 =
                         let uu____6403 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6403 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6401 uu____6402  in
                     (uu____6400, args1)
               else
                 (let uu____6415 = p_indexingTerm head1  in
                  (uu____6415, args))
                in
             (match uu____6288 with
              | (head_doc,args1) ->
                  let uu____6436 =
                    let uu____6437 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6437 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6436))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6457 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6457)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6475 =
               let uu____6476 = p_quident lid  in
               let uu____6477 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6476 uu____6477  in
             FStar_Pprint.group uu____6475
         | hd1::tl1 ->
             let uu____6494 =
               let uu____6495 =
                 let uu____6496 =
                   let uu____6497 = p_quident lid  in
                   let uu____6498 = p_argTerm hd1  in
                   prefix2 uu____6497 uu____6498  in
                 FStar_Pprint.group uu____6496  in
               let uu____6499 =
                 let uu____6500 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6500  in
               FStar_Pprint.op_Hat_Hat uu____6495 uu____6499  in
             FStar_Pprint.group uu____6494)
    | uu____6505 -> p_indexingTerm e

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
         (let uu____6514 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6514 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6516 = str "#"  in
        let uu____6517 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6516 uu____6517
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6519  ->
    match uu____6519 with | (e,uu____6525) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6530;_},e1::e2::[])
          ->
          let uu____6535 =
            let uu____6536 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6537 =
              let uu____6538 =
                let uu____6539 = p_term false false e2  in
                soft_parens_with_nesting uu____6539  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6538  in
            FStar_Pprint.op_Hat_Hat uu____6536 uu____6537  in
          FStar_Pprint.group uu____6535
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6540;_},e1::e2::[])
          ->
          let uu____6545 =
            let uu____6546 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6547 =
              let uu____6548 =
                let uu____6549 = p_term false false e2  in
                soft_brackets_with_nesting uu____6549  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6548  in
            FStar_Pprint.op_Hat_Hat uu____6546 uu____6547  in
          FStar_Pprint.group uu____6545
      | uu____6550 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6555 = p_quident lid  in
        let uu____6556 =
          let uu____6557 =
            let uu____6558 = p_term false false e1  in
            soft_parens_with_nesting uu____6558  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6557  in
        FStar_Pprint.op_Hat_Hat uu____6555 uu____6556
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6564 =
          let uu____6565 = FStar_Ident.text_of_id op  in str uu____6565  in
        let uu____6566 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6564 uu____6566
    | uu____6567 -> p_atomicTermNotQUident e

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
         | uu____6575 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6582 =
          let uu____6583 = FStar_Ident.text_of_id op  in str uu____6583  in
        let uu____6584 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6582 uu____6584
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6588 =
          let uu____6589 =
            let uu____6590 =
              let uu____6591 = FStar_Ident.text_of_id op  in str uu____6591
               in
            let uu____6592 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6590 uu____6592  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6589  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6588
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6607 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6608 =
          let uu____6609 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6610 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6609 p_tmEq uu____6610  in
        let uu____6617 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6607 uu____6608 uu____6617
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6620 =
          let uu____6621 = p_atomicTermNotQUident e1  in
          let uu____6622 =
            let uu____6623 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6623  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6621 uu____6622
           in
        FStar_Pprint.group uu____6620
    | uu____6624 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6629 = p_quident constr_lid  in
        let uu____6630 =
          let uu____6631 =
            let uu____6632 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6632  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6631  in
        FStar_Pprint.op_Hat_Hat uu____6629 uu____6630
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6634 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6634 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6636 = p_term false false e1  in
        soft_parens_with_nesting uu____6636
    | uu____6637 when is_array e ->
        let es = extract_from_list e  in
        let uu____6641 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6642 =
          let uu____6643 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6643
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6646 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6641 uu____6642 uu____6646
    | uu____6647 when is_list e ->
        let uu____6648 =
          let uu____6649 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6650 = extract_from_list e  in
          separate_map_or_flow_last uu____6649
            (fun ps  -> p_noSeqTerm ps false) uu____6650
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6648 FStar_Pprint.rbracket
    | uu____6655 when is_lex_list e ->
        let uu____6656 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6657 =
          let uu____6658 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6659 = extract_from_list e  in
          separate_map_or_flow_last uu____6658
            (fun ps  -> p_noSeqTerm ps false) uu____6659
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6656 uu____6657 FStar_Pprint.rbracket
    | uu____6664 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6668 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6669 =
          let uu____6670 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6670 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6668 uu____6669 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6674 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6675 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6674 uu____6675
    | FStar_Parser_AST.Op (op,args) when
        let uu____6682 = handleable_op op args  in
        Prims.op_Negation uu____6682 ->
        let uu____6683 =
          let uu____6684 =
            let uu____6685 = FStar_Ident.text_of_id op  in
            let uu____6686 =
              let uu____6687 =
                let uu____6688 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6688
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6687  in
            Prims.strcat uu____6685 uu____6686  in
          Prims.strcat "Operation " uu____6684  in
        failwith uu____6683
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6690 = str "u#"  in
        let uu____6691 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6690 uu____6691
    | FStar_Parser_AST.Wild  ->
        let uu____6692 = p_term false false e  in
        soft_parens_with_nesting uu____6692
    | FStar_Parser_AST.Const uu____6693 ->
        let uu____6694 = p_term false false e  in
        soft_parens_with_nesting uu____6694
    | FStar_Parser_AST.Op uu____6695 ->
        let uu____6702 = p_term false false e  in
        soft_parens_with_nesting uu____6702
    | FStar_Parser_AST.Tvar uu____6703 ->
        let uu____6704 = p_term false false e  in
        soft_parens_with_nesting uu____6704
    | FStar_Parser_AST.Var uu____6705 ->
        let uu____6706 = p_term false false e  in
        soft_parens_with_nesting uu____6706
    | FStar_Parser_AST.Name uu____6707 ->
        let uu____6708 = p_term false false e  in
        soft_parens_with_nesting uu____6708
    | FStar_Parser_AST.Construct uu____6709 ->
        let uu____6720 = p_term false false e  in
        soft_parens_with_nesting uu____6720
    | FStar_Parser_AST.Abs uu____6721 ->
        let uu____6728 = p_term false false e  in
        soft_parens_with_nesting uu____6728
    | FStar_Parser_AST.App uu____6729 ->
        let uu____6736 = p_term false false e  in
        soft_parens_with_nesting uu____6736
    | FStar_Parser_AST.Let uu____6737 ->
        let uu____6758 = p_term false false e  in
        soft_parens_with_nesting uu____6758
    | FStar_Parser_AST.LetOpen uu____6759 ->
        let uu____6764 = p_term false false e  in
        soft_parens_with_nesting uu____6764
    | FStar_Parser_AST.Seq uu____6765 ->
        let uu____6770 = p_term false false e  in
        soft_parens_with_nesting uu____6770
    | FStar_Parser_AST.Bind uu____6771 ->
        let uu____6778 = p_term false false e  in
        soft_parens_with_nesting uu____6778
    | FStar_Parser_AST.If uu____6779 ->
        let uu____6786 = p_term false false e  in
        soft_parens_with_nesting uu____6786
    | FStar_Parser_AST.Match uu____6787 ->
        let uu____6802 = p_term false false e  in
        soft_parens_with_nesting uu____6802
    | FStar_Parser_AST.TryWith uu____6803 ->
        let uu____6818 = p_term false false e  in
        soft_parens_with_nesting uu____6818
    | FStar_Parser_AST.Ascribed uu____6819 ->
        let uu____6828 = p_term false false e  in
        soft_parens_with_nesting uu____6828
    | FStar_Parser_AST.Record uu____6829 ->
        let uu____6842 = p_term false false e  in
        soft_parens_with_nesting uu____6842
    | FStar_Parser_AST.Project uu____6843 ->
        let uu____6848 = p_term false false e  in
        soft_parens_with_nesting uu____6848
    | FStar_Parser_AST.Product uu____6849 ->
        let uu____6856 = p_term false false e  in
        soft_parens_with_nesting uu____6856
    | FStar_Parser_AST.Sum uu____6857 ->
        let uu____6864 = p_term false false e  in
        soft_parens_with_nesting uu____6864
    | FStar_Parser_AST.QForall uu____6865 ->
        let uu____6878 = p_term false false e  in
        soft_parens_with_nesting uu____6878
    | FStar_Parser_AST.QExists uu____6879 ->
        let uu____6892 = p_term false false e  in
        soft_parens_with_nesting uu____6892
    | FStar_Parser_AST.Refine uu____6893 ->
        let uu____6898 = p_term false false e  in
        soft_parens_with_nesting uu____6898
    | FStar_Parser_AST.NamedTyp uu____6899 ->
        let uu____6904 = p_term false false e  in
        soft_parens_with_nesting uu____6904
    | FStar_Parser_AST.Requires uu____6905 ->
        let uu____6912 = p_term false false e  in
        soft_parens_with_nesting uu____6912
    | FStar_Parser_AST.Ensures uu____6913 ->
        let uu____6920 = p_term false false e  in
        soft_parens_with_nesting uu____6920
    | FStar_Parser_AST.Attributes uu____6921 ->
        let uu____6924 = p_term false false e  in
        soft_parens_with_nesting uu____6924
    | FStar_Parser_AST.Quote uu____6925 ->
        let uu____6930 = p_term false false e  in
        soft_parens_with_nesting uu____6930
    | FStar_Parser_AST.VQuote uu____6931 ->
        let uu____6932 = p_term false false e  in
        soft_parens_with_nesting uu____6932
    | FStar_Parser_AST.Antiquote uu____6933 ->
        let uu____6938 = p_term false false e  in
        soft_parens_with_nesting uu____6938

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___94_6939  ->
    match uu___94_6939 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6944) ->
        let uu____6945 = str s  in FStar_Pprint.dquotes uu____6945
    | FStar_Const.Const_bytearray (bytes,uu____6947) ->
        let uu____6952 =
          let uu____6953 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6953  in
        let uu____6954 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6952 uu____6954
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___92_6974 =
          match uu___92_6974 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___93_6980 =
          match uu___93_6980 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6991  ->
               match uu____6991 with
               | (s,w) ->
                   let uu____6998 = signedness s  in
                   let uu____6999 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6998 uu____6999)
            sign_width_opt
           in
        let uu____7000 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7000 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7002 = FStar_Range.string_of_range r  in str uu____7002
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7004 = p_quident lid  in
        let uu____7005 =
          let uu____7006 =
            let uu____7007 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7007  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7006  in
        FStar_Pprint.op_Hat_Hat uu____7004 uu____7005

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7009 = str "u#"  in
    let uu____7010 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7009 uu____7010

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7012;_},u1::u2::[])
        ->
        let uu____7017 =
          let uu____7018 = p_universeFrom u1  in
          let uu____7019 =
            let uu____7020 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7020  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7018 uu____7019  in
        FStar_Pprint.group uu____7017
    | FStar_Parser_AST.App uu____7021 ->
        let uu____7028 = head_and_args u  in
        (match uu____7028 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7054 =
                    let uu____7055 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7056 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7064  ->
                           match uu____7064 with
                           | (u1,uu____7070) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7055 uu____7056  in
                  FStar_Pprint.group uu____7054
              | uu____7071 ->
                  let uu____7072 =
                    let uu____7073 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7073
                     in
                  failwith uu____7072))
    | uu____7074 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7097 = FStar_Ident.text_of_id id1  in str uu____7097
    | FStar_Parser_AST.Paren u1 ->
        let uu____7099 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7099
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7100;_},uu____7101::uu____7102::[])
        ->
        let uu____7105 = p_universeFrom u  in
        soft_parens_with_nesting uu____7105
    | FStar_Parser_AST.App uu____7106 ->
        let uu____7113 = p_universeFrom u  in
        soft_parens_with_nesting uu____7113
    | uu____7114 ->
        let uu____7115 =
          let uu____7116 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7116
           in
        failwith uu____7115

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
       | FStar_Parser_AST.Module (uu____7196,decls) ->
           let uu____7202 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7202
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7211,decls,uu____7213) ->
           let uu____7218 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7218
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7275  ->
         match uu____7275 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7319,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7325,decls,uu____7327) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7376 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7389;
                 FStar_Parser_AST.doc = uu____7390;
                 FStar_Parser_AST.quals = uu____7391;
                 FStar_Parser_AST.attrs = uu____7392;_}::uu____7393 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7399 =
                   let uu____7402 =
                     let uu____7405 = FStar_List.tl ds  in d :: uu____7405
                      in
                   d0 :: uu____7402  in
                 (uu____7399, (d0.FStar_Parser_AST.drange))
             | uu____7410 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7376 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7474 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7474 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7582 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7582, comments1))))))
  