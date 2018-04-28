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
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1195 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1201 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1207 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___53_1227  ->
    match uu___53_1227 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___54_1248  ->
      match uu___54_1248 with
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
  let levels_from_associativity l uu___55_2014 =
    match uu___55_2014 with
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
         (id1,uu____4204)) ->
          let uu____4207 =
            let uu____4208 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4208 FStar_Util.is_upper  in
          if uu____4207
          then
            let uu____4209 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____4209 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____4211 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____4216 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____4217 =
      let uu____4218 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____4219 =
        let uu____4220 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____4220  in
      FStar_Pprint.op_Hat_Hat uu____4218 uu____4219  in
    FStar_Pprint.op_Hat_Hat uu____4216 uu____4217

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____4222 ->
        let uu____4223 =
          let uu____4224 = str "@ "  in
          let uu____4225 =
            let uu____4226 =
              let uu____4227 =
                let uu____4228 =
                  let uu____4229 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____4229  in
                FStar_Pprint.op_Hat_Hat uu____4228 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____4227  in
            FStar_Pprint.op_Hat_Hat uu____4226 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____4224 uu____4225  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____4223

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____4232  ->
    match uu____4232 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____4268 =
                match uu____4268 with
                | (kwd,arg) ->
                    let uu____4275 = str "@"  in
                    let uu____4276 =
                      let uu____4277 = str kwd  in
                      let uu____4278 =
                        let uu____4279 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4279
                         in
                      FStar_Pprint.op_Hat_Hat uu____4277 uu____4278  in
                    FStar_Pprint.op_Hat_Hat uu____4275 uu____4276
                 in
              let uu____4280 =
                let uu____4281 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____4281 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4280
           in
        let uu____4286 =
          let uu____4287 =
            let uu____4288 =
              let uu____4289 =
                let uu____4290 = str doc1  in
                let uu____4291 =
                  let uu____4292 =
                    let uu____4293 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4293  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____4292  in
                FStar_Pprint.op_Hat_Hat uu____4290 uu____4291  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4289  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____4288  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4287  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4286

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4297 =
          let uu____4298 = str "val"  in
          let uu____4299 =
            let uu____4300 =
              let uu____4301 = p_lident lid  in
              let uu____4302 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4301 uu____4302  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4300  in
          FStar_Pprint.op_Hat_Hat uu____4298 uu____4299  in
        let uu____4303 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____4297 uu____4303
    | FStar_Parser_AST.TopLevelLet (uu____4304,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4329 =
               let uu____4330 = str "let"  in p_letlhs uu____4330 lb  in
             FStar_Pprint.group uu____4329) lbs
    | uu____4331 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___56_4346 =
          match uu___56_4346 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4354 = f x  in
              let uu____4355 =
                let uu____4356 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4356  in
              FStar_Pprint.op_Hat_Hat uu____4354 uu____4355
           in
        let uu____4357 = str "["  in
        let uu____4358 =
          let uu____4359 = p_list' l  in
          let uu____4360 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4359 uu____4360  in
        FStar_Pprint.op_Hat_Hat uu____4357 uu____4358

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4363 =
          let uu____4364 = str "open"  in
          let uu____4365 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4364 uu____4365  in
        FStar_Pprint.group uu____4363
    | FStar_Parser_AST.Include uid ->
        let uu____4367 =
          let uu____4368 = str "include"  in
          let uu____4369 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4368 uu____4369  in
        FStar_Pprint.group uu____4367
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4372 =
          let uu____4373 = str "module"  in
          let uu____4374 =
            let uu____4375 =
              let uu____4376 = p_uident uid1  in
              let uu____4377 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4376 uu____4377  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4375  in
          FStar_Pprint.op_Hat_Hat uu____4373 uu____4374  in
        let uu____4378 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4372 uu____4378
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4380 =
          let uu____4381 = str "module"  in
          let uu____4382 =
            let uu____4383 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4383  in
          FStar_Pprint.op_Hat_Hat uu____4381 uu____4382  in
        FStar_Pprint.group uu____4380
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____4416 = str "effect"  in
          let uu____4417 =
            let uu____4418 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4418  in
          FStar_Pprint.op_Hat_Hat uu____4416 uu____4417  in
        let uu____4419 =
          let uu____4420 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4420 FStar_Pprint.equals
           in
        let uu____4421 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4419 uu____4421
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____4439 =
          let uu____4440 = str "type"  in
          let uu____4441 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____4440 uu____4441  in
        let uu____4454 =
          let uu____4455 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____4493 =
                    let uu____4494 = str "and"  in
                    p_fsdocTypeDeclPairs uu____4494 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____4493)) uu____4455
           in
        FStar_Pprint.op_Hat_Hat uu____4439 uu____4454
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4510 = str "let"  in
          let uu____4511 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4510 uu____4511  in
        let uu____4512 = str "and"  in
        separate_map_with_comments_kw let_doc uu____4512 p_letbinding lbs
          (fun uu____4520  ->
             match uu____4520 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4529 = str "val"  in
        let uu____4530 =
          let uu____4531 =
            let uu____4532 = p_lident lid  in
            let uu____4533 =
              let uu____4534 =
                let uu____4535 =
                  let uu____4536 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4536  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4535  in
              FStar_Pprint.group uu____4534  in
            FStar_Pprint.op_Hat_Hat uu____4532 uu____4533  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4531  in
        FStar_Pprint.op_Hat_Hat uu____4529 uu____4530
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4540 =
            let uu____4541 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4541 FStar_Util.is_upper  in
          if uu____4540
          then FStar_Pprint.empty
          else
            (let uu____4543 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4543 FStar_Pprint.space)
           in
        let uu____4544 =
          let uu____4545 = p_ident id1  in
          let uu____4546 =
            let uu____4547 =
              let uu____4548 =
                let uu____4549 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4549  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4548  in
            FStar_Pprint.group uu____4547  in
          FStar_Pprint.op_Hat_Hat uu____4545 uu____4546  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____4544
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4556 = str "exception"  in
        let uu____4557 =
          let uu____4558 =
            let uu____4559 = p_uident uid  in
            let uu____4560 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4564 =
                     let uu____4565 = str "of"  in
                     let uu____4566 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4565 uu____4566  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4564) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4559 uu____4560  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4558  in
        FStar_Pprint.op_Hat_Hat uu____4556 uu____4557
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4568 = str "new_effect"  in
        let uu____4569 =
          let uu____4570 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4570  in
        FStar_Pprint.op_Hat_Hat uu____4568 uu____4569
    | FStar_Parser_AST.SubEffect se ->
        let uu____4572 = str "sub_effect"  in
        let uu____4573 =
          let uu____4574 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4574  in
        FStar_Pprint.op_Hat_Hat uu____4572 uu____4573
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4577 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4577 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4578 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4579) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4602 = str "%splice"  in
        let uu____4603 =
          let uu____4604 =
            let uu____4605 = str ";"  in p_list p_uident uu____4605 ids  in
          let uu____4606 =
            let uu____4607 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4607  in
          FStar_Pprint.op_Hat_Hat uu____4604 uu____4606  in
        FStar_Pprint.op_Hat_Hat uu____4602 uu____4603

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___57_4608  ->
    match uu___57_4608 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4610 = str "#set-options"  in
        let uu____4611 =
          let uu____4612 =
            let uu____4613 = str s  in FStar_Pprint.dquotes uu____4613  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4612  in
        FStar_Pprint.op_Hat_Hat uu____4610 uu____4611
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4617 = str "#reset-options"  in
        let uu____4618 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4622 =
                 let uu____4623 = str s  in FStar_Pprint.dquotes uu____4623
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4622) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4617 uu____4618
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
    fun uu____4652  ->
      match uu____4652 with
      | (typedecl,fsdoc_opt) ->
          let uu____4665 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____4665 with
           | (decl,body) ->
               let uu____4683 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____4683)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___58_4685  ->
      match uu___58_4685 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____4715 = FStar_Pprint.empty  in
          let uu____4716 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____4716, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____4737 =
            let uu____4738 = p_typ false false t  in jump2 uu____4738  in
          let uu____4739 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4739, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4793 =
            match uu____4793 with
            | (lid1,t,doc_opt) ->
                let uu____4809 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4809
             in
          let p_fields uu____4825 =
            let uu____4826 =
              let uu____4827 =
                let uu____4828 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4828 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4827  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4826  in
          let uu____4837 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4837, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4898 =
            match uu____4898 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4924 =
                    let uu____4925 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4925  in
                  FStar_Range.extend_to_end_of_line uu____4924  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4951 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4964 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4964,
            ((fun uu____4970  ->
                let uu____4971 = datacon_doc ()  in jump2 uu____4971)))

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
  fun uu____4972  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4972 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____5006 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____5006  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____5008 =
                        let uu____5011 =
                          let uu____5014 = p_fsdoc fsdoc  in
                          let uu____5015 =
                            let uu____5018 = cont lid_doc  in [uu____5018]
                             in
                          uu____5014 :: uu____5015  in
                        kw :: uu____5011  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____5008
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____5023 =
                        let uu____5024 =
                          let uu____5025 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5025 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5024
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5023
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____5040 =
                          let uu____5041 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____5041  in
                        prefix2 uu____5040 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5043  ->
      match uu____5043 with
      | (lid,t,doc_opt) ->
          let uu____5059 =
            let uu____5060 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____5061 =
              let uu____5062 = p_lident lid  in
              let uu____5063 =
                let uu____5064 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5064  in
              FStar_Pprint.op_Hat_Hat uu____5062 uu____5063  in
            FStar_Pprint.op_Hat_Hat uu____5060 uu____5061  in
          FStar_Pprint.group uu____5059

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____5065  ->
    match uu____5065 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____5093 =
            let uu____5094 =
              let uu____5095 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5095  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5094  in
          FStar_Pprint.group uu____5093  in
        let uu____5096 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____5097 =
          default_or_map uid_doc
            (fun t  ->
               let uu____5101 =
                 let uu____5102 =
                   let uu____5103 =
                     let uu____5104 =
                       let uu____5105 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5105
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____5104  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5103  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____5102  in
               FStar_Pprint.group uu____5101) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____5096 uu____5097

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5107  ->
      match uu____5107 with
      | (pat,uu____5113) ->
          let uu____5114 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____5133 =
                  let uu____5134 =
                    let uu____5135 =
                      let uu____5136 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5136
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5135  in
                  FStar_Pprint.group uu____5134  in
                (pat1, uu____5133)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____5148 =
                  let uu____5149 =
                    let uu____5150 =
                      let uu____5151 =
                        let uu____5152 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5152
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5151
                       in
                    FStar_Pprint.group uu____5150  in
                  let uu____5153 =
                    let uu____5154 =
                      let uu____5155 = str "by"  in
                      let uu____5156 =
                        let uu____5157 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5157
                         in
                      FStar_Pprint.op_Hat_Hat uu____5155 uu____5156  in
                    FStar_Pprint.group uu____5154  in
                  FStar_Pprint.op_Hat_Hat uu____5149 uu____5153  in
                (pat1, uu____5148)
            | uu____5158 -> (pat, FStar_Pprint.empty)  in
          (match uu____5114 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____5162);
                       FStar_Parser_AST.prange = uu____5163;_},pats)
                    ->
                    let uu____5173 =
                      let uu____5174 =
                        let uu____5175 =
                          let uu____5176 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5176  in
                        FStar_Pprint.group uu____5175  in
                      let uu____5177 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____5174 uu____5177  in
                    prefix2_nonempty uu____5173 ascr_doc
                | uu____5178 ->
                    let uu____5179 =
                      let uu____5180 =
                        let uu____5181 =
                          let uu____5182 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____5182  in
                        FStar_Pprint.group uu____5181  in
                      FStar_Pprint.op_Hat_Hat uu____5180 ascr_doc  in
                    FStar_Pprint.group uu____5179))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____5184  ->
      match uu____5184 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____5193 =
            let uu____5194 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____5194  in
          let uu____5195 =
            let uu____5196 =
              let uu____5197 =
                let uu____5198 =
                  let uu____5199 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____5199  in
                FStar_Pprint.group uu____5198  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5197  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____5196  in
          FStar_Pprint.ifflat uu____5193 uu____5195

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___59_5200  ->
    match uu___59_5200 with
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
        let uu____5225 = p_uident uid  in
        let uu____5226 = p_binders true bs  in
        let uu____5227 =
          let uu____5228 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____5228  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5225 uu____5226 uu____5227

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
          let uu____5238 =
            let uu____5239 =
              let uu____5240 =
                let uu____5241 = p_uident uid  in
                let uu____5242 = p_binders true bs  in
                let uu____5243 =
                  let uu____5244 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____5244  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____5241 uu____5242 uu____5243
                 in
              FStar_Pprint.group uu____5240  in
            let uu____5245 =
              let uu____5246 = str "with"  in
              let uu____5247 =
                let uu____5248 =
                  let uu____5249 =
                    let uu____5250 =
                      let uu____5251 =
                        let uu____5252 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____5252
                         in
                      separate_map_last uu____5251 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5250  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5249  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5248  in
              FStar_Pprint.op_Hat_Hat uu____5246 uu____5247  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5239 uu____5245  in
          braces_with_nesting uu____5238

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
          let uu____5283 =
            let uu____5284 = p_lident lid  in
            let uu____5285 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____5284 uu____5285  in
          let uu____5286 = p_simpleTerm ps false e  in
          prefix2 uu____5283 uu____5286
      | uu____5287 ->
          let uu____5288 =
            let uu____5289 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____5289
             in
          failwith uu____5288

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____5351 =
        match uu____5351 with
        | (kwd,t) ->
            let uu____5358 =
              let uu____5359 = str kwd  in
              let uu____5360 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____5359 uu____5360  in
            let uu____5361 = p_simpleTerm ps false t  in
            prefix2 uu____5358 uu____5361
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____5366 =
      let uu____5367 =
        let uu____5368 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____5369 =
          let uu____5370 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5370  in
        FStar_Pprint.op_Hat_Hat uu____5368 uu____5369  in
      let uu____5371 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____5367 uu____5371  in
    let uu____5372 =
      let uu____5373 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5373  in
    FStar_Pprint.op_Hat_Hat uu____5366 uu____5372

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___60_5374  ->
    match uu___60_5374 with
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
    | uu____5376 ->
        let uu____5377 =
          let uu____5378 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____5378  in
        FStar_Pprint.op_Hat_Hat uu____5377 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___61_5381  ->
    match uu___61_5381 with
    | FStar_Parser_AST.Rec  ->
        let uu____5382 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5382
    | FStar_Parser_AST.Mutable  ->
        let uu____5383 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5383
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___62_5384  ->
    match uu___62_5384 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____5389 =
          let uu____5390 =
            let uu____5391 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____5391  in
          FStar_Pprint.separate_map uu____5390 p_tuplePattern pats  in
        FStar_Pprint.group uu____5389
    | uu____5392 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____5399 =
          let uu____5400 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____5400 p_constructorPattern pats  in
        FStar_Pprint.group uu____5399
    | uu____5401 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____5404;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____5409 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____5410 = p_constructorPattern hd1  in
        let uu____5411 = p_constructorPattern tl1  in
        infix0 uu____5409 uu____5410 uu____5411
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____5413;_},pats)
        ->
        let uu____5419 = p_quident uid  in
        let uu____5420 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5419 uu____5420
    | uu____5421 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5437;
               FStar_Parser_AST.blevel = uu____5438;
               FStar_Parser_AST.aqual = uu____5439;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5445 =
               let uu____5446 = p_ident lid  in
               p_refinement aqual uu____5446 t1 phi  in
             soft_parens_with_nesting uu____5445
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5448;
               FStar_Parser_AST.blevel = uu____5449;
               FStar_Parser_AST.aqual = uu____5450;_},phi))
             ->
             let uu____5452 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____5452
         | uu____5453 ->
             let uu____5458 =
               let uu____5459 = p_tuplePattern pat  in
               let uu____5460 =
                 let uu____5461 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5461
                  in
               FStar_Pprint.op_Hat_Hat uu____5459 uu____5460  in
             soft_parens_with_nesting uu____5458)
    | FStar_Parser_AST.PatList pats ->
        let uu____5465 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5465 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5482 =
          match uu____5482 with
          | (lid,pat) ->
              let uu____5489 = p_qlident lid  in
              let uu____5490 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5489 uu____5490
           in
        let uu____5491 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5491
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5501 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5502 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5503 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5501 uu____5502 uu____5503
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5512 =
          let uu____5513 =
            let uu____5514 =
              let uu____5515 = FStar_Ident.text_of_id op  in str uu____5515
               in
            let uu____5516 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5514 uu____5516  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5513  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5512
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5524 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5525 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5524 uu____5525
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5527 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5530;
           FStar_Parser_AST.prange = uu____5531;_},uu____5532)
        ->
        let uu____5537 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5537
    | FStar_Parser_AST.PatTuple (uu____5538,false ) ->
        let uu____5543 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5543
    | uu____5544 ->
        let uu____5545 =
          let uu____5546 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5546  in
        failwith uu____5545

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5550 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5551 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5550 uu____5551
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5558;
                   FStar_Parser_AST.blevel = uu____5559;
                   FStar_Parser_AST.aqual = uu____5560;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5562 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5562 t1 phi
            | uu____5563 ->
                let uu____5564 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5565 =
                  let uu____5566 = p_lident lid  in
                  let uu____5567 =
                    let uu____5568 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____5568
                     in
                  FStar_Pprint.op_Hat_Hat uu____5566 uu____5567  in
                FStar_Pprint.op_Hat_Hat uu____5564 uu____5565
             in
          if is_atomic
          then
            let uu____5569 =
              let uu____5570 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5570  in
            FStar_Pprint.group uu____5569
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5572 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5579;
                  FStar_Parser_AST.blevel = uu____5580;
                  FStar_Parser_AST.aqual = uu____5581;_},phi)
               ->
               if is_atomic
               then
                 let uu____5583 =
                   let uu____5584 =
                     let uu____5585 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5585 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5584  in
                 FStar_Pprint.group uu____5583
               else
                 (let uu____5587 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5587)
           | uu____5588 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____5597 -> false
            | FStar_Parser_AST.App uu____5608 -> false
            | FStar_Parser_AST.Op uu____5615 -> false
            | uu____5622 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____5626 =
            let uu____5627 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____5628 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____5627 uu____5628  in
          let uu____5629 =
            let uu____5630 = p_appTerm t  in
            let uu____5631 =
              let uu____5632 =
                let uu____5633 =
                  let uu____5634 = soft_braces_with_nesting_tight phi1  in
                  let uu____5635 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____5634 uu____5635  in
                FStar_Pprint.group uu____5633  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____5632
               in
            FStar_Pprint.op_Hat_Hat uu____5630 uu____5631  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5626 uu____5629

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____5646 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____5646

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5651 = FStar_Ident.text_of_id lid  in str uu____5651)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____5654 = FStar_Ident.text_of_lid lid  in str uu____5654)

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
            let uu____5672 =
              let uu____5673 =
                let uu____5674 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5674 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5673  in
            let uu____5675 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5672 uu____5675
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5679 =
              let uu____5680 =
                let uu____5681 =
                  let uu____5682 = p_lident x  in
                  let uu____5683 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5682 uu____5683  in
                let uu____5684 =
                  let uu____5685 = p_noSeqTerm true false e1  in
                  let uu____5686 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5685 uu____5686  in
                op_Hat_Slash_Plus_Hat uu____5681 uu____5684  in
              FStar_Pprint.group uu____5680  in
            let uu____5687 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5679 uu____5687
        | uu____5688 ->
            let uu____5689 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5689

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
            let uu____5700 =
              let uu____5701 = p_tmIff e1  in
              let uu____5702 =
                let uu____5703 =
                  let uu____5704 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5704
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5703  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5701 uu____5702  in
            FStar_Pprint.group uu____5700
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5710 =
              let uu____5711 = p_tmIff e1  in
              let uu____5712 =
                let uu____5713 =
                  let uu____5714 =
                    let uu____5715 = p_typ false false t  in
                    let uu____5716 =
                      let uu____5717 = str "by"  in
                      let uu____5718 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5717 uu____5718  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5715 uu____5716  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5714
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5713  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5711 uu____5712  in
            FStar_Pprint.group uu____5710
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5719;_},e1::e2::e3::[])
            ->
            let uu____5725 =
              let uu____5726 =
                let uu____5727 =
                  let uu____5728 = p_atomicTermNotQUident e1  in
                  let uu____5729 =
                    let uu____5730 =
                      let uu____5731 =
                        let uu____5732 = p_term false false e2  in
                        soft_parens_with_nesting uu____5732  in
                      let uu____5733 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5731 uu____5733  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5730  in
                  FStar_Pprint.op_Hat_Hat uu____5728 uu____5729  in
                FStar_Pprint.group uu____5727  in
              let uu____5734 =
                let uu____5735 = p_noSeqTerm ps pb e3  in jump2 uu____5735
                 in
              FStar_Pprint.op_Hat_Hat uu____5726 uu____5734  in
            FStar_Pprint.group uu____5725
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5736;_},e1::e2::e3::[])
            ->
            let uu____5742 =
              let uu____5743 =
                let uu____5744 =
                  let uu____5745 = p_atomicTermNotQUident e1  in
                  let uu____5746 =
                    let uu____5747 =
                      let uu____5748 =
                        let uu____5749 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5749  in
                      let uu____5750 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5748 uu____5750  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5747  in
                  FStar_Pprint.op_Hat_Hat uu____5745 uu____5746  in
                FStar_Pprint.group uu____5744  in
              let uu____5751 =
                let uu____5752 = p_noSeqTerm ps pb e3  in jump2 uu____5752
                 in
              FStar_Pprint.op_Hat_Hat uu____5743 uu____5751  in
            FStar_Pprint.group uu____5742
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5760 =
              let uu____5761 = str "requires"  in
              let uu____5762 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5761 uu____5762  in
            FStar_Pprint.group uu____5760
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5770 =
              let uu____5771 = str "ensures"  in
              let uu____5772 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5771 uu____5772  in
            FStar_Pprint.group uu____5770
        | FStar_Parser_AST.Attributes es ->
            let uu____5776 =
              let uu____5777 = str "attributes"  in
              let uu____5778 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5777 uu____5778  in
            FStar_Pprint.group uu____5776
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5782 =
                let uu____5783 =
                  let uu____5784 = str "if"  in
                  let uu____5785 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5784 uu____5785  in
                let uu____5786 =
                  let uu____5787 = str "then"  in
                  let uu____5788 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5787 uu____5788  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5783 uu____5786  in
              FStar_Pprint.group uu____5782
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5791,uu____5792,e31) when
                     is_unit e31 ->
                     let uu____5794 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5794
                 | uu____5795 -> p_noSeqTerm false false e2  in
               let uu____5796 =
                 let uu____5797 =
                   let uu____5798 = str "if"  in
                   let uu____5799 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5798 uu____5799  in
                 let uu____5800 =
                   let uu____5801 =
                     let uu____5802 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5802 e2_doc  in
                   let uu____5803 =
                     let uu____5804 = str "else"  in
                     let uu____5805 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5804 uu____5805  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5801 uu____5803  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5797 uu____5800  in
               FStar_Pprint.group uu____5796)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5828 =
              let uu____5829 =
                let uu____5830 =
                  let uu____5831 = str "try"  in
                  let uu____5832 = p_noSeqTerm false false e1  in
                  prefix2 uu____5831 uu____5832  in
                let uu____5833 =
                  let uu____5834 = str "with"  in
                  let uu____5835 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5834 uu____5835  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5830 uu____5833  in
              FStar_Pprint.group uu____5829  in
            let uu____5844 = paren_if (ps || pb)  in uu____5844 uu____5828
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5871 =
              let uu____5872 =
                let uu____5873 =
                  let uu____5874 = str "match"  in
                  let uu____5875 = p_noSeqTerm false false e1  in
                  let uu____5876 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5874 uu____5875 uu____5876
                   in
                let uu____5877 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5873 uu____5877  in
              FStar_Pprint.group uu____5872  in
            let uu____5886 = paren_if (ps || pb)  in uu____5886 uu____5871
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5893 =
              let uu____5894 =
                let uu____5895 =
                  let uu____5896 = str "let open"  in
                  let uu____5897 = p_quident uid  in
                  let uu____5898 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5896 uu____5897 uu____5898
                   in
                let uu____5899 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5895 uu____5899  in
              FStar_Pprint.group uu____5894  in
            let uu____5900 = paren_if ps  in uu____5900 uu____5893
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5964 is_last =
              match uu____5964 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5997 =
                          let uu____5998 = str "let"  in
                          let uu____5999 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5998 uu____5999
                           in
                        FStar_Pprint.group uu____5997
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____6000 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____6005 =
                    if is_last
                    then
                      let uu____6006 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____6007 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____6006 doc_expr uu____6007
                    else
                      (let uu____6009 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____6009)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____6005
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____6055 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____6055
                     else
                       (let uu____6063 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____6063)) lbs
               in
            let lbs_doc =
              let uu____6071 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____6071  in
            let uu____6072 =
              let uu____6073 =
                let uu____6074 =
                  let uu____6075 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____6075
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____6074  in
              FStar_Pprint.group uu____6073  in
            let uu____6076 = paren_if ps  in uu____6076 uu____6072
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____6083;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____6086;
                                                             FStar_Parser_AST.level
                                                               = uu____6087;_})
            when matches_var maybe_x x ->
            let uu____6114 =
              let uu____6115 =
                let uu____6116 = str "function"  in
                let uu____6117 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____6116 uu____6117  in
              FStar_Pprint.group uu____6115  in
            let uu____6126 = paren_if (ps || pb)  in uu____6126 uu____6114
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____6132 =
              let uu____6133 = str "quote"  in
              let uu____6134 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6133 uu____6134  in
            FStar_Pprint.group uu____6132
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____6136 =
              let uu____6137 = str "`"  in
              let uu____6138 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6137 uu____6138  in
            FStar_Pprint.group uu____6136
        | FStar_Parser_AST.VQuote e1 ->
            let uu____6140 =
              let uu____6141 = str "%`"  in
              let uu____6142 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6141 uu____6142  in
            FStar_Pprint.group uu____6140
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____6144 =
              let uu____6145 = str "`#"  in
              let uu____6146 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6145 uu____6146  in
            FStar_Pprint.group uu____6144
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____6148 =
              let uu____6149 = str "`@"  in
              let uu____6150 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____6149 uu____6150  in
            FStar_Pprint.group uu____6148
        | uu____6151 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___63_6152  ->
    match uu___63_6152 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____6164 =
          let uu____6165 = str "[@"  in
          let uu____6166 =
            let uu____6167 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____6168 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____6167 uu____6168  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6165 uu____6166  in
        FStar_Pprint.group uu____6164

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
                 let uu____6194 =
                   let uu____6195 =
                     let uu____6196 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6196 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6195 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6194 term_doc
             | pats ->
                 let uu____6202 =
                   let uu____6203 =
                     let uu____6204 =
                       let uu____6205 =
                         let uu____6206 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6206
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6205 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6207 = p_trigger trigger  in
                     prefix2 uu____6204 uu____6207  in
                   FStar_Pprint.group uu____6203  in
                 prefix2 uu____6202 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____6227 =
                   let uu____6228 =
                     let uu____6229 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____6229 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____6228 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____6227 term_doc
             | pats ->
                 let uu____6235 =
                   let uu____6236 =
                     let uu____6237 =
                       let uu____6238 =
                         let uu____6239 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____6239
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____6238 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____6240 = p_trigger trigger  in
                     prefix2 uu____6237 uu____6240  in
                   FStar_Pprint.group uu____6236  in
                 prefix2 uu____6235 term_doc)
        | uu____6241 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____6243 -> str "forall"
    | FStar_Parser_AST.QExists uu____6256 -> str "exists"
    | uu____6269 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___64_6270  ->
    match uu___64_6270 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____6282 =
          let uu____6283 =
            let uu____6284 =
              let uu____6285 = str "pattern"  in
              let uu____6286 =
                let uu____6287 =
                  let uu____6288 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____6288
                   in
                FStar_Pprint.op_Hat_Hat uu____6287 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____6285 uu____6286  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6284  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____6283  in
        FStar_Pprint.group uu____6282

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6294 = str "\\/"  in
    FStar_Pprint.separate_map uu____6294 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____6300 =
      let uu____6301 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____6301 p_appTerm pats  in
    FStar_Pprint.group uu____6300

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____6311 =
              let uu____6312 =
                let uu____6313 = str "fun"  in
                let uu____6314 =
                  let uu____6315 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____6315
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____6313 uu____6314  in
              let uu____6316 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____6312 uu____6316  in
            let uu____6317 = paren_if ps  in uu____6317 uu____6311
        | uu____6322 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____6326  ->
      match uu____6326 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____6349 =
                    let uu____6350 =
                      let uu____6351 =
                        let uu____6352 = p_tuplePattern p  in
                        let uu____6353 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____6352 uu____6353  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6351
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6350  in
                  FStar_Pprint.group uu____6349
              | FStar_Pervasives_Native.Some f ->
                  let uu____6355 =
                    let uu____6356 =
                      let uu____6357 =
                        let uu____6358 =
                          let uu____6359 =
                            let uu____6360 = p_tuplePattern p  in
                            let uu____6361 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____6360
                              uu____6361
                             in
                          FStar_Pprint.group uu____6359  in
                        let uu____6362 =
                          let uu____6363 =
                            let uu____6366 = p_tmFormula f  in
                            [uu____6366; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____6363  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____6358 uu____6362
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6357
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6356  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____6355
               in
            let uu____6367 =
              let uu____6368 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____6368  in
            FStar_Pprint.group uu____6367  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____6377 =
                      let uu____6378 =
                        let uu____6379 =
                          let uu____6380 =
                            let uu____6381 =
                              let uu____6382 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____6382  in
                            FStar_Pprint.separate_map uu____6381
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____6380
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6379
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____6378  in
                    FStar_Pprint.group uu____6377
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____6383 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____6385;_},e1::e2::[])
        ->
        let uu____6390 = str "<==>"  in
        let uu____6391 = p_tmImplies e1  in
        let uu____6392 = p_tmIff e2  in
        infix0 uu____6390 uu____6391 uu____6392
    | uu____6393 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____6395;_},e1::e2::[])
        ->
        let uu____6400 = str "==>"  in
        let uu____6401 = p_tmArrow p_tmFormula e1  in
        let uu____6402 = p_tmImplies e2  in
        infix0 uu____6400 uu____6401 uu____6402
    | uu____6403 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____6411 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____6411 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____6432 ->
               let uu____6433 =
                 let uu____6434 =
                   let uu____6435 =
                     let uu____6436 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6436
                      in
                   FStar_Pprint.separate uu____6435 terms  in
                 let uu____6437 =
                   let uu____6438 =
                     let uu____6439 =
                       let uu____6440 =
                         let uu____6441 =
                           let uu____6442 =
                             let uu____6443 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____6443
                              in
                           FStar_Pprint.separate uu____6442 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____6441 last_op  in
                       let uu____6444 =
                         let uu____6445 =
                           let uu____6446 =
                             let uu____6447 =
                               let uu____6448 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____6448
                                in
                             FStar_Pprint.separate uu____6447 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____6446 last_op  in
                         jump2 uu____6445  in
                       FStar_Pprint.ifflat uu____6440 uu____6444  in
                     FStar_Pprint.group uu____6439  in
                   let uu____6449 = FStar_List.hd last1  in
                   prefix2 uu____6438 uu____6449  in
                 FStar_Pprint.ifflat uu____6434 uu____6437  in
               FStar_Pprint.group uu____6433)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____6462 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____6467 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____6462 uu____6467
      | uu____6470 -> let uu____6471 = p_Tm e  in [uu____6471]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____6474 =
        let uu____6475 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____6475 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6474  in
    let disj =
      let uu____6477 =
        let uu____6478 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____6478 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6477  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____6497;_},e1::e2::[])
        ->
        let uu____6502 = p_tmDisjunction e1  in
        let uu____6507 = let uu____6512 = p_tmConjunction e2  in [uu____6512]
           in
        FStar_List.append uu____6502 uu____6507
    | uu____6521 -> let uu____6522 = p_tmConjunction e  in [uu____6522]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____6532;_},e1::e2::[])
        ->
        let uu____6537 = p_tmConjunction e1  in
        let uu____6540 = let uu____6543 = p_tmTuple e2  in [uu____6543]  in
        FStar_List.append uu____6537 uu____6540
    | uu____6544 -> let uu____6545 = p_tmTuple e  in [uu____6545]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____6562 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____6562
          (fun uu____6570  ->
             match uu____6570 with | (e1,uu____6576) -> p_tmEq e1) args
    | uu____6577 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____6582 =
             let uu____6583 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6583  in
           FStar_Pprint.group uu____6582)

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
               (let uu____6646 = FStar_Ident.text_of_id op  in
                uu____6646 = "="))
              ||
              (let uu____6648 = FStar_Ident.text_of_id op  in
               uu____6648 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6650 = levels op1  in
            (match uu____6650 with
             | (left1,mine,right1) ->
                 let uu____6660 =
                   let uu____6661 = FStar_All.pipe_left str op1  in
                   let uu____6662 = p_tmEqWith' p_X left1 e1  in
                   let uu____6663 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6661 uu____6662 uu____6663  in
                 paren_if_gt curr mine uu____6660)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6664;_},e1::e2::[])
            ->
            let uu____6669 =
              let uu____6670 = p_tmEqWith p_X e1  in
              let uu____6671 =
                let uu____6672 =
                  let uu____6673 =
                    let uu____6674 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6674  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6673  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6672  in
              FStar_Pprint.op_Hat_Hat uu____6670 uu____6671  in
            FStar_Pprint.group uu____6669
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6675;_},e1::[])
            ->
            let uu____6679 = levels "-"  in
            (match uu____6679 with
             | (left1,mine,right1) ->
                 let uu____6689 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6689)
        | uu____6690 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____6762)::(e2,uu____6764)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____6784 = is_list e  in Prims.op_Negation uu____6784)
              ->
              let op = "::"  in
              let uu____6786 = levels op  in
              (match uu____6786 with
               | (left1,mine,right1) ->
                   let uu____6796 =
                     let uu____6797 = str op  in
                     let uu____6798 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6799 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6797 uu____6798 uu____6799  in
                   paren_if_gt curr mine uu____6796)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6807 = levels op  in
              (match uu____6807 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6823 = p_binder false b  in
                     let uu____6824 =
                       let uu____6825 =
                         let uu____6826 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6826 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6825
                        in
                     FStar_Pprint.op_Hat_Hat uu____6823 uu____6824  in
                   let uu____6827 =
                     let uu____6828 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6829 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6828 uu____6829  in
                   paren_if_gt curr mine uu____6827)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6830;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6859 = levels op  in
              (match uu____6859 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6869 = str op  in
                     let uu____6870 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6871 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6869 uu____6870 uu____6871
                   else
                     (let uu____6873 =
                        let uu____6874 = str op  in
                        let uu____6875 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6876 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6874 uu____6875 uu____6876  in
                      paren_if_gt curr mine uu____6873))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6883 = levels op1  in
              (match uu____6883 with
               | (left1,mine,right1) ->
                   let uu____6893 =
                     let uu____6894 = str op1  in
                     let uu____6895 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6896 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6894 uu____6895 uu____6896  in
                   paren_if_gt curr mine uu____6893)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6915 =
                let uu____6916 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6917 =
                  let uu____6918 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6918 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6916 uu____6917  in
              braces_with_nesting uu____6915
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6923;_},e1::[])
              ->
              let uu____6927 =
                let uu____6928 = str "~"  in
                let uu____6929 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6928 uu____6929  in
              FStar_Pprint.group uu____6927
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6931;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6937 = levels op  in
                   (match uu____6937 with
                    | (left1,mine,right1) ->
                        let uu____6947 =
                          let uu____6948 = str op  in
                          let uu____6949 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6950 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6948 uu____6949 uu____6950  in
                        paren_if_gt curr mine uu____6947)
               | uu____6951 -> p_X e)
          | uu____6952 -> p_X e

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
        let uu____6959 =
          let uu____6960 = p_lident lid  in
          let uu____6961 =
            let uu____6962 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6962  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6960 uu____6961  in
        FStar_Pprint.group uu____6959
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6965 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6967 = p_appTerm e  in
    let uu____6968 =
      let uu____6969 =
        let uu____6970 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6970 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6969  in
    FStar_Pprint.op_Hat_Hat uu____6967 uu____6968

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6975 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6975 t phi
      | FStar_Parser_AST.TAnnotated uu____6976 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6981 ->
          let uu____6982 =
            let uu____6983 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6983
             in
          failwith uu____6982
      | FStar_Parser_AST.TVariable uu____6984 ->
          let uu____6985 =
            let uu____6986 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6986
             in
          failwith uu____6985
      | FStar_Parser_AST.NoName uu____6987 ->
          let uu____6988 =
            let uu____6989 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6989
             in
          failwith uu____6988

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6991  ->
      match uu____6991 with
      | (lid,e) ->
          let uu____6998 =
            let uu____6999 = p_qlident lid  in
            let uu____7000 =
              let uu____7001 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____7001
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6999 uu____7000  in
          FStar_Pprint.group uu____6998

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____7003 when is_general_application e ->
        let uu____7010 = head_and_args e  in
        (match uu____7010 with
         | (head1,args) ->
             let uu____7035 =
               let uu____7046 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____7046
               then
                 let uu____7080 =
                   FStar_Util.take
                     (fun uu____7104  ->
                        match uu____7104 with
                        | (uu____7109,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____7080 with
                 | (fs_typ_args,args1) ->
                     let uu____7147 =
                       let uu____7148 = p_indexingTerm head1  in
                       let uu____7149 =
                         let uu____7150 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____7150 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____7148 uu____7149  in
                     (uu____7147, args1)
               else
                 (let uu____7162 = p_indexingTerm head1  in
                  (uu____7162, args))
                in
             (match uu____7035 with
              | (head_doc,args1) ->
                  let uu____7183 =
                    let uu____7184 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____7184 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____7183))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____7204 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____7204)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____7222 =
               let uu____7223 = p_quident lid  in
               let uu____7224 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____7223 uu____7224  in
             FStar_Pprint.group uu____7222
         | hd1::tl1 ->
             let uu____7241 =
               let uu____7242 =
                 let uu____7243 =
                   let uu____7244 = p_quident lid  in
                   let uu____7245 = p_argTerm hd1  in
                   prefix2 uu____7244 uu____7245  in
                 FStar_Pprint.group uu____7243  in
               let uu____7246 =
                 let uu____7247 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____7247  in
               FStar_Pprint.op_Hat_Hat uu____7242 uu____7246  in
             FStar_Pprint.group uu____7241)
    | uu____7252 -> p_indexingTerm e

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
         (let uu____7261 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____7261 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____7263 = str "#"  in
        let uu____7264 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____7263 uu____7264
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____7266  ->
    match uu____7266 with | (e,uu____7272) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____7277;_},e1::e2::[])
          ->
          let uu____7282 =
            let uu____7283 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7284 =
              let uu____7285 =
                let uu____7286 = p_term false false e2  in
                soft_parens_with_nesting uu____7286  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7285  in
            FStar_Pprint.op_Hat_Hat uu____7283 uu____7284  in
          FStar_Pprint.group uu____7282
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____7287;_},e1::e2::[])
          ->
          let uu____7292 =
            let uu____7293 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____7294 =
              let uu____7295 =
                let uu____7296 = p_term false false e2  in
                soft_brackets_with_nesting uu____7296  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7295  in
            FStar_Pprint.op_Hat_Hat uu____7293 uu____7294  in
          FStar_Pprint.group uu____7292
      | uu____7297 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____7302 = p_quident lid  in
        let uu____7303 =
          let uu____7304 =
            let uu____7305 = p_term false false e1  in
            soft_parens_with_nesting uu____7305  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7304  in
        FStar_Pprint.op_Hat_Hat uu____7302 uu____7303
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7311 =
          let uu____7312 = FStar_Ident.text_of_id op  in str uu____7312  in
        let uu____7313 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____7311 uu____7313
    | uu____7314 -> p_atomicTermNotQUident e

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
         | uu____7321 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____7328 =
          let uu____7329 = FStar_Ident.text_of_id op  in str uu____7329  in
        let uu____7330 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____7328 uu____7330
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____7334 =
          let uu____7335 =
            let uu____7336 =
              let uu____7337 = FStar_Ident.text_of_id op  in str uu____7337
               in
            let uu____7338 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____7336 uu____7338  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____7335  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____7334
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____7353 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____7354 =
          let uu____7355 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____7356 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____7355 p_tmEq uu____7356  in
        let uu____7363 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7353 uu____7354 uu____7363
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____7366 =
          let uu____7367 = p_atomicTermNotQUident e1  in
          let uu____7368 =
            let uu____7369 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7369  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____7367 uu____7368
           in
        FStar_Pprint.group uu____7366
    | uu____7370 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____7375 = p_quident constr_lid  in
        let uu____7376 =
          let uu____7377 =
            let uu____7378 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7378  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7377  in
        FStar_Pprint.op_Hat_Hat uu____7375 uu____7376
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____7380 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____7380 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____7382 = p_term false false e1  in
        soft_parens_with_nesting uu____7382
    | uu____7383 when is_array e ->
        let es = extract_from_list e  in
        let uu____7387 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____7388 =
          let uu____7389 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____7389
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____7392 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7387 uu____7388 uu____7392
    | uu____7393 when is_list e ->
        let uu____7394 =
          let uu____7395 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7396 = extract_from_list e  in
          separate_map_or_flow_last uu____7395
            (fun ps  -> p_noSeqTerm ps false) uu____7396
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____7394 FStar_Pprint.rbracket
    | uu____7401 when is_lex_list e ->
        let uu____7402 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____7403 =
          let uu____7404 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____7405 = extract_from_list e  in
          separate_map_or_flow_last uu____7404
            (fun ps  -> p_noSeqTerm ps false) uu____7405
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____7402 uu____7403 FStar_Pprint.rbracket
    | uu____7410 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____7414 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____7415 =
          let uu____7416 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____7416 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____7414 uu____7415 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____7420 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____7421 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____7420 uu____7421
    | FStar_Parser_AST.Op (op,args) when
        let uu____7428 = handleable_op op args  in
        Prims.op_Negation uu____7428 ->
        let uu____7429 =
          let uu____7430 =
            let uu____7431 = FStar_Ident.text_of_id op  in
            let uu____7432 =
              let uu____7433 =
                let uu____7434 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____7434
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____7433  in
            Prims.strcat uu____7431 uu____7432  in
          Prims.strcat "Operation " uu____7430  in
        failwith uu____7429
    | FStar_Parser_AST.Uvar uu____7435 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____7436 = p_term false false e  in
        soft_parens_with_nesting uu____7436
    | FStar_Parser_AST.Const uu____7437 ->
        let uu____7438 = p_term false false e  in
        soft_parens_with_nesting uu____7438
    | FStar_Parser_AST.Op uu____7439 ->
        let uu____7446 = p_term false false e  in
        soft_parens_with_nesting uu____7446
    | FStar_Parser_AST.Tvar uu____7447 ->
        let uu____7448 = p_term false false e  in
        soft_parens_with_nesting uu____7448
    | FStar_Parser_AST.Var uu____7449 ->
        let uu____7450 = p_term false false e  in
        soft_parens_with_nesting uu____7450
    | FStar_Parser_AST.Name uu____7451 ->
        let uu____7452 = p_term false false e  in
        soft_parens_with_nesting uu____7452
    | FStar_Parser_AST.Construct uu____7453 ->
        let uu____7464 = p_term false false e  in
        soft_parens_with_nesting uu____7464
    | FStar_Parser_AST.Abs uu____7465 ->
        let uu____7472 = p_term false false e  in
        soft_parens_with_nesting uu____7472
    | FStar_Parser_AST.App uu____7473 ->
        let uu____7480 = p_term false false e  in
        soft_parens_with_nesting uu____7480
    | FStar_Parser_AST.Let uu____7481 ->
        let uu____7502 = p_term false false e  in
        soft_parens_with_nesting uu____7502
    | FStar_Parser_AST.LetOpen uu____7503 ->
        let uu____7508 = p_term false false e  in
        soft_parens_with_nesting uu____7508
    | FStar_Parser_AST.Seq uu____7509 ->
        let uu____7514 = p_term false false e  in
        soft_parens_with_nesting uu____7514
    | FStar_Parser_AST.Bind uu____7515 ->
        let uu____7522 = p_term false false e  in
        soft_parens_with_nesting uu____7522
    | FStar_Parser_AST.If uu____7523 ->
        let uu____7530 = p_term false false e  in
        soft_parens_with_nesting uu____7530
    | FStar_Parser_AST.Match uu____7531 ->
        let uu____7546 = p_term false false e  in
        soft_parens_with_nesting uu____7546
    | FStar_Parser_AST.TryWith uu____7547 ->
        let uu____7562 = p_term false false e  in
        soft_parens_with_nesting uu____7562
    | FStar_Parser_AST.Ascribed uu____7563 ->
        let uu____7572 = p_term false false e  in
        soft_parens_with_nesting uu____7572
    | FStar_Parser_AST.Record uu____7573 ->
        let uu____7586 = p_term false false e  in
        soft_parens_with_nesting uu____7586
    | FStar_Parser_AST.Project uu____7587 ->
        let uu____7592 = p_term false false e  in
        soft_parens_with_nesting uu____7592
    | FStar_Parser_AST.Product uu____7593 ->
        let uu____7600 = p_term false false e  in
        soft_parens_with_nesting uu____7600
    | FStar_Parser_AST.Sum uu____7601 ->
        let uu____7608 = p_term false false e  in
        soft_parens_with_nesting uu____7608
    | FStar_Parser_AST.QForall uu____7609 ->
        let uu____7622 = p_term false false e  in
        soft_parens_with_nesting uu____7622
    | FStar_Parser_AST.QExists uu____7623 ->
        let uu____7636 = p_term false false e  in
        soft_parens_with_nesting uu____7636
    | FStar_Parser_AST.Refine uu____7637 ->
        let uu____7642 = p_term false false e  in
        soft_parens_with_nesting uu____7642
    | FStar_Parser_AST.NamedTyp uu____7643 ->
        let uu____7648 = p_term false false e  in
        soft_parens_with_nesting uu____7648
    | FStar_Parser_AST.Requires uu____7649 ->
        let uu____7656 = p_term false false e  in
        soft_parens_with_nesting uu____7656
    | FStar_Parser_AST.Ensures uu____7657 ->
        let uu____7664 = p_term false false e  in
        soft_parens_with_nesting uu____7664
    | FStar_Parser_AST.Attributes uu____7665 ->
        let uu____7668 = p_term false false e  in
        soft_parens_with_nesting uu____7668
    | FStar_Parser_AST.Quote uu____7669 ->
        let uu____7674 = p_term false false e  in
        soft_parens_with_nesting uu____7674
    | FStar_Parser_AST.VQuote uu____7675 ->
        let uu____7676 = p_term false false e  in
        soft_parens_with_nesting uu____7676
    | FStar_Parser_AST.Antiquote uu____7677 ->
        let uu____7682 = p_term false false e  in
        soft_parens_with_nesting uu____7682

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___67_7683  ->
    match uu___67_7683 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____7688) ->
        let uu____7689 = str s  in FStar_Pprint.dquotes uu____7689
    | FStar_Const.Const_bytearray (bytes,uu____7691) ->
        let uu____7696 =
          let uu____7697 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____7697  in
        let uu____7698 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____7696 uu____7698
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___65_7718 =
          match uu___65_7718 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___66_7724 =
          match uu___66_7724 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7735  ->
               match uu____7735 with
               | (s,w) ->
                   let uu____7742 = signedness s  in
                   let uu____7743 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7742 uu____7743)
            sign_width_opt
           in
        let uu____7744 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7744 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7746 = FStar_Range.string_of_range r  in str uu____7746
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7748 = p_quident lid  in
        let uu____7749 =
          let uu____7750 =
            let uu____7751 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7751  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7750  in
        FStar_Pprint.op_Hat_Hat uu____7748 uu____7749

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7753 = str "u#"  in
    let uu____7754 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7753 uu____7754

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7756;_},u1::u2::[])
        ->
        let uu____7761 =
          let uu____7762 = p_universeFrom u1  in
          let uu____7763 =
            let uu____7764 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7764  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7762 uu____7763  in
        FStar_Pprint.group uu____7761
    | FStar_Parser_AST.App uu____7765 ->
        let uu____7772 = head_and_args u  in
        (match uu____7772 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7798 =
                    let uu____7799 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7800 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7808  ->
                           match uu____7808 with
                           | (u1,uu____7814) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7799 uu____7800  in
                  FStar_Pprint.group uu____7798
              | uu____7815 ->
                  let uu____7816 =
                    let uu____7817 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7817
                     in
                  failwith uu____7816))
    | uu____7818 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7841 = FStar_Ident.text_of_id id1  in str uu____7841
    | FStar_Parser_AST.Paren u1 ->
        let uu____7843 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7843
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7844;_},uu____7845::uu____7846::[])
        ->
        let uu____7849 = p_universeFrom u  in
        soft_parens_with_nesting uu____7849
    | FStar_Parser_AST.App uu____7850 ->
        let uu____7857 = p_universeFrom u  in
        soft_parens_with_nesting uu____7857
    | uu____7858 ->
        let uu____7859 =
          let uu____7860 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7860
           in
        failwith uu____7859

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
       | FStar_Parser_AST.Module (uu____7940,decls) ->
           let uu____7946 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7946
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7955,decls,uu____7957) ->
           let uu____7962 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7962
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____8019  ->
         match uu____8019 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____8063,decls) -> decls
        | FStar_Parser_AST.Interface (uu____8069,decls,uu____8071) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____8120 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____8133;
                 FStar_Parser_AST.doc = uu____8134;
                 FStar_Parser_AST.quals = uu____8135;
                 FStar_Parser_AST.attrs = uu____8136;_}::uu____8137 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____8143 =
                   let uu____8146 =
                     let uu____8149 = FStar_List.tl ds  in d :: uu____8149
                      in
                   d0 :: uu____8146  in
                 (uu____8143, (d0.FStar_Parser_AST.drange))
             | uu____8154 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____8120 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____8218 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____8218 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____8326 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____8326, comments1))))))
  