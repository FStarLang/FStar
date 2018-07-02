open Prims
let (min : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then y else x 
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun x  -> fun y  -> if x > y then x else y 
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____59 'Auu____60 .
    Prims.bool -> ('Auu____59 -> 'Auu____60) -> 'Auu____59 -> 'Auu____60
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
  'Auu____157 'Auu____158 .
    'Auu____157 ->
      ('Auu____158 -> 'Auu____157) ->
        'Auu____158 FStar_Pervasives_Native.option -> 'Auu____157
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
  'Auu____252 .
    FStar_Pprint.document ->
      ('Auu____252 -> FStar_Pprint.document) ->
        'Auu____252 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____277 =
          let uu____278 =
            let uu____279 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____279  in
          FStar_Pprint.separate_map uu____278 f l  in
        FStar_Pprint.group uu____277
  
let precede_break_separate_map :
  'Auu____290 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____290 -> FStar_Pprint.document) ->
          'Auu____290 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____320 =
            let uu____321 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____322 =
              let uu____323 = FStar_List.hd l  in
              FStar_All.pipe_right uu____323 f  in
            FStar_Pprint.precede uu____321 uu____322  in
          let uu____324 =
            let uu____325 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____331 =
                   let uu____332 =
                     let uu____333 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____333  in
                   FStar_Pprint.op_Hat_Hat sep uu____332  in
                 FStar_Pprint.op_Hat_Hat break1 uu____331) uu____325
             in
          FStar_Pprint.op_Hat_Hat uu____320 uu____324
  
let concat_break_map :
  'Auu____340 .
    ('Auu____340 -> FStar_Pprint.document) ->
      'Auu____340 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____360 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____364 = f x  in FStar_Pprint.op_Hat_Hat uu____364 break1)
          l
         in
      FStar_Pprint.group uu____360
  
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
    let uu____405 = str "begin"  in
    let uu____406 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____405 contents uu____406
  
let separate_map_last :
  'Auu____415 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____415 -> FStar_Pprint.document) ->
        'Auu____415 Prims.list -> FStar_Pprint.document
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
  'Auu____467 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____467 -> FStar_Pprint.document) ->
        'Auu____467 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____497 =
          let uu____498 =
            let uu____499 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____499  in
          separate_map_last uu____498 f l  in
        FStar_Pprint.group uu____497
  
let separate_map_or_flow :
  'Auu____508 .
    FStar_Pprint.document ->
      ('Auu____508 -> FStar_Pprint.document) ->
        'Auu____508 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____542 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____542 -> FStar_Pprint.document) ->
        'Auu____542 Prims.list -> FStar_Pprint.document
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
  'Auu____594 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____594 -> FStar_Pprint.document) ->
        'Auu____594 Prims.list -> FStar_Pprint.document
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
              let uu____664 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____664
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____684 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____684 -> FStar_Pprint.document) ->
                  'Auu____684 Prims.list -> FStar_Pprint.document
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
                    (let uu____737 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____737
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____756 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____756 -> FStar_Pprint.document) ->
                  'Auu____756 Prims.list -> FStar_Pprint.document
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
                    (let uu____809 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____809
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____824  ->
    match uu____824 with
    | (comment,keywords) ->
        let uu____849 =
          let uu____850 =
            let uu____853 = str comment  in
            let uu____854 =
              let uu____857 =
                let uu____860 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____869  ->
                       match uu____869 with
                       | (k,v1) ->
                           let uu____876 =
                             let uu____879 = str k  in
                             let uu____880 =
                               let uu____883 =
                                 let uu____886 = str v1  in [uu____886]  in
                               FStar_Pprint.rarrow :: uu____883  in
                             uu____879 :: uu____880  in
                           FStar_Pprint.concat uu____876) keywords
                   in
                [uu____860]  in
              FStar_Pprint.space :: uu____857  in
            uu____853 :: uu____854  in
          FStar_Pprint.concat uu____850  in
        FStar_Pprint.group uu____849
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____892 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____904 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____904
      | uu____905 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____947::(e2,uu____949)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____972 -> false  in
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
    | FStar_Parser_AST.Construct (uu____990,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1001,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1022 = extract_from_list e2  in e1 :: uu____1022
    | uu____1025 ->
        let uu____1026 =
          let uu____1027 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1027  in
        failwith uu____1026
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1036;
           FStar_Parser_AST.level = uu____1037;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1039 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1047;
           FStar_Parser_AST.level = uu____1048;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1050;
                                                         FStar_Parser_AST.level
                                                           = uu____1051;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1053;
                                                    FStar_Parser_AST.level =
                                                      uu____1054;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1056;
                FStar_Parser_AST.level = uu____1057;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1059;
           FStar_Parser_AST.level = uu____1060;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1062 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1072 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1073;
           FStar_Parser_AST.range = uu____1074;
           FStar_Parser_AST.level = uu____1075;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1076;
                                                         FStar_Parser_AST.range
                                                           = uu____1077;
                                                         FStar_Parser_AST.level
                                                           = uu____1078;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1080;
                                                    FStar_Parser_AST.level =
                                                      uu____1081;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1082;
                FStar_Parser_AST.range = uu____1083;
                FStar_Parser_AST.level = uu____1084;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1086;
           FStar_Parser_AST.level = uu____1087;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1089 = extract_from_ref_set e1  in
        let uu____1092 = extract_from_ref_set e2  in
        FStar_List.append uu____1089 uu____1092
    | uu____1095 ->
        let uu____1096 =
          let uu____1097 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1097  in
        failwith uu____1096
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1105 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1105
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1111 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1111
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1119 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1119 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1127 = FStar_Ident.text_of_id op  in uu____1127 <> "~"))
  
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
      | uu____1193 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1209 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1215 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1221 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___101_1242  ->
    match uu___101_1242 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___102_1267  ->
      match uu___102_1267 with
      | FStar_Util.Inl c ->
          let uu____1276 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1276 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1287 .
    Prims.string ->
      ('Auu____1287,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1308  ->
      match uu____1308 with
      | (assoc_levels,tokens) ->
          let uu____1336 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1336 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___103_1454 =
    match uu___103_1454 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1484  ->
         match uu____1484 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1543 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1543 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1583) ->
          assoc_levels
      | uu____1612 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____1637 .
    ('Auu____1637,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1682 =
        FStar_List.tryFind
          (fun uu____1712  ->
             match uu____1712 with
             | (uu____1725,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1682 with
      | FStar_Pervasives_Native.Some ((uu____1747,l1,uu____1749),uu____1750)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1785 =
            let uu____1786 =
              let uu____1787 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1787  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1786
             in
          failwith uu____1785
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1809 = assign_levels level_associativity_spec op  in
    match uu____1809 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1839 =
      let uu____1842 =
        let uu____1847 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1847  in
      FStar_List.tryFind uu____1842 operatorInfix0ad12  in
    uu____1839 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1905 =
      let uu____1919 =
        let uu____1935 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1935  in
      FStar_List.tryFind uu____1919 opinfix34  in
    uu____1905 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____1991 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____1991
    then (Prims.parse_int "1")
    else
      (let uu____1993 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____1993
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2002 . FStar_Ident.ident -> 'Auu____2002 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2018 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2018 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2020 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2020
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2021 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2021 [".()<-"; ".[]<-"]
      | uu____2022 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2060 .
    ('Auu____2060 -> FStar_Pprint.document) ->
      'Auu____2060 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2101 = FStar_ST.op_Bang comment_stack  in
          match uu____2101 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2160 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2160
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2197 =
                    let uu____2198 =
                      let uu____2199 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2199
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2198  in
                  comments_before_pos uu____2197 print_pos lookahead_pos))
              else
                (let uu____2201 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2201))
           in
        let uu____2202 =
          let uu____2207 =
            let uu____2208 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2208  in
          let uu____2209 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2207 uu____2209  in
        match uu____2202 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2215 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2215
              else comments  in
            let uu____2221 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2221
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        Prims.int ->
          Prims.int -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun end_correction  ->
          fun fsdoc_correction  ->
            fun doc1  ->
              let uu____2252 = FStar_ST.op_Bang comment_stack  in
              match uu____2252 with
              | (comment,crange)::cs when
                  FStar_Range.range_before_pos crange pos_end ->
                  (FStar_ST.op_Colon_Equals comment_stack cs;
                   (let lnum =
                      let uu____2336 =
                        let uu____2337 =
                          let uu____2338 = FStar_Range.start_of_range crange
                             in
                          FStar_Range.line_of_pos uu____2338  in
                        uu____2337 - lbegin  in
                      max k uu____2336  in
                    let lnum1 = min (Prims.parse_int "2") lnum  in
                    let doc2 =
                      let uu____2341 =
                        let uu____2342 =
                          FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                        let uu____2343 = str comment  in
                        FStar_Pprint.op_Hat_Hat uu____2342 uu____2343  in
                      FStar_Pprint.op_Hat_Hat doc1 uu____2341  in
                    let uu____2344 =
                      let uu____2345 = FStar_Range.end_of_range crange  in
                      FStar_Range.line_of_pos uu____2345  in
                    place_comments_until_pos (Prims.parse_int "1") uu____2344
                      pos_end end_correction fsdoc_correction doc2))
              | uu____2346 ->
                  if doc1 = FStar_Pprint.empty
                  then FStar_Pprint.empty
                  else
                    (let lnum =
                       let uu____2355 = FStar_Range.line_of_pos pos_end  in
                       uu____2355 - lbegin  in
                     let lnum1 =
                       if lnum >= (Prims.parse_int "2")
                       then lnum - end_correction
                       else lnum  in
                     let lnum2 = min (Prims.parse_int "2") lnum1  in
                     let lnum3 =
                       if lnum2 >= (Prims.parse_int "2")
                       then lnum2 - fsdoc_correction
                       else lnum2  in
                     let uu____2361 =
                       FStar_Pprint.repeat lnum3 FStar_Pprint.hardline  in
                     FStar_Pprint.op_Hat_Hat doc1 uu____2361)
  
let separate_map_with_comments :
  'Auu____2374 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2374 -> FStar_Pprint.document) ->
          'Auu____2374 Prims.list ->
            ('Auu____2374 ->
               (FStar_Range.range,Prims.int,Prims.int)
                 FStar_Pervasives_Native.tuple3)
              -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2443 x =
              match uu____2443 with
              | (last_line,doc1) ->
                  let uu____2455 = extract_range x  in
                  (match uu____2455 with
                   | (r,end_c,fsdoc_c) ->
                       let doc2 =
                         let uu____2470 = FStar_Range.start_of_range r  in
                         place_comments_until_pos (Prims.parse_int "1")
                           last_line uu____2470 end_c fsdoc_c doc1
                          in
                       let uu____2471 =
                         let uu____2472 = FStar_Range.end_of_range r  in
                         FStar_Range.line_of_pos uu____2472  in
                       let uu____2473 =
                         let uu____2474 =
                           let uu____2475 = f x  in
                           FStar_Pprint.op_Hat_Hat sep uu____2475  in
                         FStar_Pprint.op_Hat_Hat doc2 uu____2474  in
                       (uu____2471, uu____2473))
               in
            let uu____2476 =
              let uu____2483 = FStar_List.hd xs  in
              let uu____2484 = FStar_List.tl xs  in (uu____2483, uu____2484)
               in
            match uu____2476 with
            | (x,xs1) ->
                let init1 =
                  let uu____2500 = extract_range x  in
                  match uu____2500 with
                  | (r,uu____2512,uu____2513) ->
                      let uu____2514 =
                        let uu____2515 = FStar_Range.end_of_range r  in
                        FStar_Range.line_of_pos uu____2515  in
                      let uu____2516 =
                        let uu____2517 = f x  in
                        FStar_Pprint.op_Hat_Hat prefix1 uu____2517  in
                      (uu____2514, uu____2516)
                   in
                let uu____2518 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2518
  
let separate_map_with_comments_kw :
  'Auu____2541 'Auu____2542 .
    'Auu____2541 ->
      'Auu____2541 ->
        ('Auu____2541 -> 'Auu____2542 -> FStar_Pprint.document) ->
          'Auu____2542 Prims.list ->
            ('Auu____2542 ->
               (FStar_Range.range,Prims.int,Prims.int)
                 FStar_Pervasives_Native.tuple3)
              -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2616 x =
              match uu____2616 with
              | (last_line,doc1) ->
                  let uu____2628 = extract_range x  in
                  (match uu____2628 with
                   | (r,end_c,fsdoc_c) ->
                       let doc2 =
                         let uu____2643 = FStar_Range.start_of_range r  in
                         place_comments_until_pos (Prims.parse_int "1")
                           last_line uu____2643 end_c fsdoc_c doc1
                          in
                       let uu____2644 =
                         let uu____2645 = FStar_Range.end_of_range r  in
                         FStar_Range.line_of_pos uu____2645  in
                       let uu____2646 =
                         let uu____2647 = f sep x  in
                         FStar_Pprint.op_Hat_Hat doc2 uu____2647  in
                       (uu____2644, uu____2646))
               in
            let uu____2648 =
              let uu____2655 = FStar_List.hd xs  in
              let uu____2656 = FStar_List.tl xs  in (uu____2655, uu____2656)
               in
            match uu____2648 with
            | (x,xs1) ->
                let init1 =
                  let uu____2672 = extract_range x  in
                  match uu____2672 with
                  | (r,uu____2684,uu____2685) ->
                      let uu____2686 =
                        let uu____2687 = FStar_Range.end_of_range r  in
                        FStar_Range.line_of_pos uu____2687  in
                      let uu____2688 = f prefix1 x  in
                      (uu____2686, uu____2688)
                   in
                let uu____2689 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2689
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3399)) ->
          let uu____3402 =
            let uu____3403 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3403 FStar_Util.is_upper  in
          if uu____3402
          then
            let uu____3406 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3406 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3408 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3415 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3416 =
      let uu____3417 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3418 =
        let uu____3419 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3419  in
      FStar_Pprint.op_Hat_Hat uu____3417 uu____3418  in
    FStar_Pprint.op_Hat_Hat uu____3415 uu____3416

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3421 ->
        let uu____3422 =
          let uu____3423 = str "@ "  in
          let uu____3424 =
            let uu____3425 =
              let uu____3426 =
                let uu____3427 =
                  let uu____3428 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3428  in
                FStar_Pprint.op_Hat_Hat uu____3427 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3426  in
            FStar_Pprint.op_Hat_Hat uu____3425 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3423 uu____3424  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3422

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3431  ->
    match uu____3431 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3467 =
                match uu____3467 with
                | (kwd,arg) ->
                    let uu____3474 = str "@"  in
                    let uu____3475 =
                      let uu____3476 = str kwd  in
                      let uu____3477 =
                        let uu____3478 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3478
                         in
                      FStar_Pprint.op_Hat_Hat uu____3476 uu____3477  in
                    FStar_Pprint.op_Hat_Hat uu____3474 uu____3475
                 in
              let uu____3479 =
                let uu____3480 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3480 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3479
           in
        let uu____3485 =
          let uu____3486 =
            let uu____3487 =
              let uu____3488 = str doc1  in
              let uu____3489 =
                let uu____3490 =
                  let uu____3491 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3491  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3490  in
              FStar_Pprint.op_Hat_Hat uu____3488 uu____3489  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3487  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3486  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3485

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3495 =
          let uu____3496 = str "val"  in
          let uu____3497 =
            let uu____3498 =
              let uu____3499 = p_lident lid  in
              let uu____3500 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3499 uu____3500  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3498  in
          FStar_Pprint.op_Hat_Hat uu____3496 uu____3497  in
        let uu____3501 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3495 uu____3501
    | FStar_Parser_AST.TopLevelLet (uu____3502,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3527 =
               let uu____3528 = str "let"  in p_letlhs uu____3528 lb  in
             FStar_Pprint.group uu____3527) lbs
    | uu____3529 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___104_3544 =
          match uu___104_3544 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3552 = f x  in
              let uu____3553 =
                let uu____3554 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3554  in
              FStar_Pprint.op_Hat_Hat uu____3552 uu____3553
           in
        let uu____3555 = str "["  in
        let uu____3556 =
          let uu____3557 = p_list' l  in
          let uu____3558 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3557 uu____3558  in
        FStar_Pprint.op_Hat_Hat uu____3555 uu____3556

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3561 =
          let uu____3562 = str "open"  in
          let uu____3563 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3562 uu____3563  in
        FStar_Pprint.group uu____3561
    | FStar_Parser_AST.Include uid ->
        let uu____3565 =
          let uu____3566 = str "include"  in
          let uu____3567 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3566 uu____3567  in
        FStar_Pprint.group uu____3565
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3570 =
          let uu____3571 = str "module"  in
          let uu____3572 =
            let uu____3573 =
              let uu____3574 = p_uident uid1  in
              let uu____3575 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3574 uu____3575  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3573  in
          FStar_Pprint.op_Hat_Hat uu____3571 uu____3572  in
        let uu____3576 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3570 uu____3576
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3578 =
          let uu____3579 = str "module"  in
          let uu____3580 =
            let uu____3581 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3581  in
          FStar_Pprint.op_Hat_Hat uu____3579 uu____3580  in
        FStar_Pprint.group uu____3578
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3614 = str "effect"  in
          let uu____3615 =
            let uu____3616 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3616  in
          FStar_Pprint.op_Hat_Hat uu____3614 uu____3615  in
        let uu____3617 =
          let uu____3618 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3618 FStar_Pprint.equals
           in
        let uu____3619 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3617 uu____3619
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3637 =
          let uu____3638 = str "type"  in
          let uu____3639 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3638 uu____3639  in
        let uu____3652 =
          let uu____3653 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3691 =
                    let uu____3692 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3692 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3691)) uu____3653
           in
        FStar_Pprint.op_Hat_Hat uu____3637 uu____3652
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3708 = str "let"  in
          let uu____3709 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3708 uu____3709  in
        let uu____3710 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3710 p_letbinding lbs
          (fun uu____3719  ->
             match uu____3719 with
             | (p,t) ->
                 let uu____3732 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 (uu____3732, (Prims.parse_int "0"),
                   (if FStar_Util.is_some d.FStar_Parser_AST.doc
                    then (Prims.parse_int "1")
                    else (Prims.parse_int "0"))))
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3736 = str "val"  in
        let uu____3737 =
          let uu____3738 =
            let uu____3739 = p_lident lid  in
            let uu____3740 =
              let uu____3741 =
                let uu____3742 =
                  let uu____3743 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3743  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3742  in
              FStar_Pprint.group uu____3741  in
            FStar_Pprint.op_Hat_Hat uu____3739 uu____3740  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3738  in
        FStar_Pprint.op_Hat_Hat uu____3736 uu____3737
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3747 =
            let uu____3748 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3748 FStar_Util.is_upper  in
          if uu____3747
          then FStar_Pprint.empty
          else
            (let uu____3752 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3752 FStar_Pprint.space)
           in
        let uu____3753 =
          let uu____3754 = p_ident id1  in
          let uu____3755 =
            let uu____3756 =
              let uu____3757 =
                let uu____3758 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3758  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3757  in
            FStar_Pprint.group uu____3756  in
          FStar_Pprint.op_Hat_Hat uu____3754 uu____3755  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3753
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3765 = str "exception"  in
        let uu____3766 =
          let uu____3767 =
            let uu____3768 = p_uident uid  in
            let uu____3769 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3773 =
                     let uu____3774 = str "of"  in
                     let uu____3775 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3774 uu____3775  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3773) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3768 uu____3769  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3767  in
        FStar_Pprint.op_Hat_Hat uu____3765 uu____3766
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3777 = str "new_effect"  in
        let uu____3778 =
          let uu____3779 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3779  in
        FStar_Pprint.op_Hat_Hat uu____3777 uu____3778
    | FStar_Parser_AST.SubEffect se ->
        let uu____3781 = str "sub_effect"  in
        let uu____3782 =
          let uu____3783 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3783  in
        FStar_Pprint.op_Hat_Hat uu____3781 uu____3782
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3786 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3786 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3787 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3788) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3811 = str "%splice"  in
        let uu____3812 =
          let uu____3813 =
            let uu____3814 = str ";"  in p_list p_uident uu____3814 ids  in
          let uu____3815 =
            let uu____3816 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3816  in
          FStar_Pprint.op_Hat_Hat uu____3813 uu____3815  in
        FStar_Pprint.op_Hat_Hat uu____3811 uu____3812

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___105_3817  ->
    match uu___105_3817 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3819 = str "#set-options"  in
        let uu____3820 =
          let uu____3821 =
            let uu____3822 = str s  in FStar_Pprint.dquotes uu____3822  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3821  in
        FStar_Pprint.op_Hat_Hat uu____3819 uu____3820
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3826 = str "#reset-options"  in
        let uu____3827 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3831 =
                 let uu____3832 = str s  in FStar_Pprint.dquotes uu____3832
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3831) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3826 uu____3827
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
    fun uu____3857  ->
      match uu____3857 with
      | (typedecl,fsdoc_opt) ->
          let uu____3870 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3870 with
           | (decl,body) ->
               let uu____3888 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3888)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___106_3890  ->
      match uu___106_3890 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3920 = FStar_Pprint.empty  in
          let uu____3921 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3921, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3942 =
            let uu____3943 = p_typ false false t  in jump2 uu____3943  in
          let uu____3944 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3944, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3998 =
            match uu____3998 with
            | (lid1,t,doc_opt) ->
                let uu____4014 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4014
             in
          let p_fields uu____4030 =
            let uu____4031 =
              let uu____4032 =
                let uu____4033 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4033 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4032  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4031  in
          let uu____4042 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4042, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4103 =
            match uu____4103 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4129 =
                    let uu____4130 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4130  in
                  FStar_Range.extend_to_end_of_line uu____4129  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4156 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4169 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4169,
            ((fun uu____4175  ->
                let uu____4176 = datacon_doc ()  in jump2 uu____4176)))

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
  fun uu____4177  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4177 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4211 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4211  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4213 =
                        let uu____4216 =
                          let uu____4219 = p_fsdoc fsdoc  in
                          let uu____4220 =
                            let uu____4223 = cont lid_doc  in [uu____4223]
                             in
                          uu____4219 :: uu____4220  in
                        kw :: uu____4216  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4213
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4228 =
                        let uu____4229 =
                          let uu____4230 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4230 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4229
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4228
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4245 =
                          let uu____4246 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4246  in
                        prefix2 uu____4245 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4248  ->
      match uu____4248 with
      | (lid,t,doc_opt) ->
          let uu____4264 =
            let uu____4265 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4266 =
              let uu____4267 = p_lident lid  in
              let uu____4268 =
                let uu____4269 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4269  in
              FStar_Pprint.op_Hat_Hat uu____4267 uu____4268  in
            FStar_Pprint.op_Hat_Hat uu____4265 uu____4266  in
          FStar_Pprint.group uu____4264

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4270  ->
    match uu____4270 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4298 =
            let uu____4299 =
              let uu____4300 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4300  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4299  in
          FStar_Pprint.group uu____4298  in
        let uu____4301 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4302 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4306 =
                 let uu____4307 =
                   let uu____4308 =
                     let uu____4309 =
                       let uu____4310 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4310
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4309  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4308  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4307  in
               FStar_Pprint.group uu____4306) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4301 uu____4302

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4312  ->
      match uu____4312 with
      | (pat,uu____4318) ->
          let uu____4319 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4338 =
                  let uu____4339 =
                    let uu____4340 =
                      let uu____4341 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4341
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4340  in
                  FStar_Pprint.group uu____4339  in
                (pat1, uu____4338)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4353 =
                  let uu____4354 =
                    let uu____4355 =
                      let uu____4356 =
                        let uu____4357 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4357
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4356
                       in
                    FStar_Pprint.group uu____4355  in
                  let uu____4358 =
                    let uu____4359 =
                      let uu____4360 = str "by"  in
                      let uu____4361 =
                        let uu____4362 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4362
                         in
                      FStar_Pprint.op_Hat_Hat uu____4360 uu____4361  in
                    FStar_Pprint.group uu____4359  in
                  FStar_Pprint.op_Hat_Hat uu____4354 uu____4358  in
                (pat1, uu____4353)
            | uu____4363 -> (pat, FStar_Pprint.empty)  in
          (match uu____4319 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4367);
                       FStar_Parser_AST.prange = uu____4368;_},pats)
                    ->
                    let uu____4378 =
                      let uu____4379 =
                        let uu____4380 =
                          let uu____4381 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4381  in
                        FStar_Pprint.group uu____4380  in
                      let uu____4382 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4379 uu____4382  in
                    prefix2_nonempty uu____4378 ascr_doc
                | uu____4383 ->
                    let uu____4384 =
                      let uu____4385 =
                        let uu____4386 =
                          let uu____4387 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4387  in
                        FStar_Pprint.group uu____4386  in
                      FStar_Pprint.op_Hat_Hat uu____4385 ascr_doc  in
                    FStar_Pprint.group uu____4384))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4389  ->
      match uu____4389 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4398 =
            let uu____4399 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4399  in
          let uu____4400 =
            let uu____4401 =
              let uu____4402 =
                let uu____4403 =
                  let uu____4404 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4404  in
                FStar_Pprint.group uu____4403  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4402  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4401  in
          FStar_Pprint.ifflat uu____4398 uu____4400

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___107_4405  ->
    match uu___107_4405 with
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
        let uu____4430 = p_uident uid  in
        let uu____4431 = p_binders true bs  in
        let uu____4432 =
          let uu____4433 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4433  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4430 uu____4431 uu____4432

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
          let uu____4443 =
            let uu____4444 =
              let uu____4445 =
                let uu____4446 = p_uident uid  in
                let uu____4447 = p_binders true bs  in
                let uu____4448 =
                  let uu____4449 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4449  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4446 uu____4447 uu____4448
                 in
              FStar_Pprint.group uu____4445  in
            let uu____4450 =
              let uu____4451 = str "with"  in
              let uu____4452 =
                let uu____4453 =
                  let uu____4454 =
                    let uu____4455 =
                      let uu____4456 =
                        let uu____4457 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4457
                         in
                      separate_map_last uu____4456 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4455  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4454  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4453  in
              FStar_Pprint.op_Hat_Hat uu____4451 uu____4452  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4444 uu____4450  in
          braces_with_nesting uu____4443

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
          let uu____4488 =
            let uu____4489 = p_lident lid  in
            let uu____4490 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4489 uu____4490  in
          let uu____4491 = p_simpleTerm ps false e  in
          prefix2 uu____4488 uu____4491
      | uu____4492 ->
          let uu____4493 =
            let uu____4494 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4494
             in
          failwith uu____4493

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4556 =
        match uu____4556 with
        | (kwd,t) ->
            let uu____4563 =
              let uu____4564 = str kwd  in
              let uu____4565 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4564 uu____4565  in
            let uu____4566 = p_simpleTerm ps false t  in
            prefix2 uu____4563 uu____4566
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4571 =
      let uu____4572 =
        let uu____4573 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4574 =
          let uu____4575 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4575  in
        FStar_Pprint.op_Hat_Hat uu____4573 uu____4574  in
      let uu____4576 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4572 uu____4576  in
    let uu____4577 =
      let uu____4578 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4578  in
    FStar_Pprint.op_Hat_Hat uu____4571 uu____4577

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___108_4579  ->
    match uu___108_4579 with
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
    | q::[] ->
        let uu____4582 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4582 FStar_Pprint.hardline
    | uu____4583 ->
        let uu____4584 =
          let uu____4585 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4585  in
        FStar_Pprint.op_Hat_Hat uu____4584 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___109_4588  ->
    match uu___109_4588 with
    | FStar_Parser_AST.Rec  ->
        let uu____4589 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4589
    | FStar_Parser_AST.Mutable  ->
        let uu____4590 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4590
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___110_4591  ->
    match uu___110_4591 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4596 =
          let uu____4597 =
            let uu____4598 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4598  in
          FStar_Pprint.separate_map uu____4597 p_tuplePattern pats  in
        FStar_Pprint.group uu____4596
    | uu____4599 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4606 =
          let uu____4607 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4607 p_constructorPattern pats  in
        FStar_Pprint.group uu____4606
    | uu____4608 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4611;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4616 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4617 = p_constructorPattern hd1  in
        let uu____4618 = p_constructorPattern tl1  in
        infix0 uu____4616 uu____4617 uu____4618
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4620;_},pats)
        ->
        let uu____4626 = p_quident uid  in
        let uu____4627 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4626 uu____4627
    | uu____4628 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4644;
               FStar_Parser_AST.blevel = uu____4645;
               FStar_Parser_AST.aqual = uu____4646;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4652 =
               let uu____4653 = p_ident lid  in
               p_refinement aqual uu____4653 t1 phi  in
             soft_parens_with_nesting uu____4652
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4655;
               FStar_Parser_AST.blevel = uu____4656;
               FStar_Parser_AST.aqual = uu____4657;_},phi))
             ->
             let uu____4659 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4659
         | uu____4660 ->
             let uu____4665 =
               let uu____4666 = p_tuplePattern pat  in
               let uu____4667 =
                 let uu____4668 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4668
                  in
               FStar_Pprint.op_Hat_Hat uu____4666 uu____4667  in
             soft_parens_with_nesting uu____4665)
    | FStar_Parser_AST.PatList pats ->
        let uu____4672 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4672 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4689 =
          match uu____4689 with
          | (lid,pat) ->
              let uu____4696 = p_qlident lid  in
              let uu____4697 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4696 uu____4697
           in
        let uu____4698 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4698
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4708 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4709 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4710 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4708 uu____4709 uu____4710
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4719 =
          let uu____4720 =
            let uu____4721 =
              let uu____4722 = FStar_Ident.text_of_id op  in str uu____4722
               in
            let uu____4723 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4721 uu____4723  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4720  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4719
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4731 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4732 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4731 uu____4732
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4734 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4737;
           FStar_Parser_AST.prange = uu____4738;_},uu____4739)
        ->
        let uu____4744 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4744
    | FStar_Parser_AST.PatTuple (uu____4745,false ) ->
        let uu____4750 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4750
    | uu____4751 ->
        let uu____4752 =
          let uu____4753 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4753  in
        failwith uu____4752

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4755;_},uu____4756)
        -> true
    | uu____4761 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4765 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4766 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4765 uu____4766
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4773;
                   FStar_Parser_AST.blevel = uu____4774;
                   FStar_Parser_AST.aqual = uu____4775;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4777 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4777 t1 phi
            | uu____4778 ->
                let t' =
                  let uu____4780 = is_typ_tuple t  in
                  if uu____4780
                  then
                    let uu____4781 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4781
                  else p_tmFormula t  in
                let uu____4783 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4784 =
                  let uu____4785 = p_lident lid  in
                  let uu____4786 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4785 uu____4786  in
                FStar_Pprint.op_Hat_Hat uu____4783 uu____4784
             in
          if is_atomic
          then
            let uu____4787 =
              let uu____4788 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4788  in
            FStar_Pprint.group uu____4787
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4790 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4797;
                  FStar_Parser_AST.blevel = uu____4798;
                  FStar_Parser_AST.aqual = uu____4799;_},phi)
               ->
               if is_atomic
               then
                 let uu____4801 =
                   let uu____4802 =
                     let uu____4803 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4803 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4802  in
                 FStar_Pprint.group uu____4801
               else
                 (let uu____4805 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4805)
           | uu____4806 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4815 -> false
            | FStar_Parser_AST.App uu____4826 -> false
            | FStar_Parser_AST.Op uu____4833 -> false
            | uu____4840 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4844 =
            let uu____4845 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4846 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4845 uu____4846  in
          let uu____4847 =
            let uu____4848 = p_appTerm t  in
            let uu____4849 =
              let uu____4850 =
                let uu____4851 =
                  let uu____4852 = soft_braces_with_nesting_tight phi1  in
                  let uu____4853 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4852 uu____4853  in
                FStar_Pprint.group uu____4851  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4850
               in
            FStar_Pprint.op_Hat_Hat uu____4848 uu____4849  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4844 uu____4847

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4864 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4864

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4869 = FStar_Ident.text_of_id lid  in str uu____4869)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4872 = FStar_Ident.text_of_lid lid  in str uu____4872)

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
            let uu____4890 =
              let uu____4891 =
                let uu____4892 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4892 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4891  in
            let uu____4893 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4890 uu____4893
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4897 =
              let uu____4898 =
                let uu____4899 =
                  let uu____4900 = p_lident x  in
                  let uu____4901 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4900 uu____4901  in
                let uu____4902 =
                  let uu____4903 = p_noSeqTerm true false e1  in
                  let uu____4904 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4903 uu____4904  in
                op_Hat_Slash_Plus_Hat uu____4899 uu____4902  in
              FStar_Pprint.group uu____4898  in
            let uu____4905 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4897 uu____4905
        | uu____4906 ->
            let uu____4907 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4907

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
            let uu____4918 =
              let uu____4919 = p_tmIff e1  in
              let uu____4920 =
                let uu____4921 =
                  let uu____4922 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4922
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4921  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4919 uu____4920  in
            FStar_Pprint.group uu____4918
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4928 =
              let uu____4929 = p_tmIff e1  in
              let uu____4930 =
                let uu____4931 =
                  let uu____4932 =
                    let uu____4933 = p_typ false false t  in
                    let uu____4934 =
                      let uu____4935 = str "by"  in
                      let uu____4936 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4935 uu____4936  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4933 uu____4934  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4932
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4931  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4929 uu____4930  in
            FStar_Pprint.group uu____4928
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4937;_},e1::e2::e3::[])
            ->
            let uu____4943 =
              let uu____4944 =
                let uu____4945 =
                  let uu____4946 = p_atomicTermNotQUident e1  in
                  let uu____4947 =
                    let uu____4948 =
                      let uu____4949 =
                        let uu____4950 = p_term false false e2  in
                        soft_parens_with_nesting uu____4950  in
                      let uu____4951 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4949 uu____4951  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4948  in
                  FStar_Pprint.op_Hat_Hat uu____4946 uu____4947  in
                FStar_Pprint.group uu____4945  in
              let uu____4952 =
                let uu____4953 = p_noSeqTerm ps pb e3  in jump2 uu____4953
                 in
              FStar_Pprint.op_Hat_Hat uu____4944 uu____4952  in
            FStar_Pprint.group uu____4943
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4954;_},e1::e2::e3::[])
            ->
            let uu____4960 =
              let uu____4961 =
                let uu____4962 =
                  let uu____4963 = p_atomicTermNotQUident e1  in
                  let uu____4964 =
                    let uu____4965 =
                      let uu____4966 =
                        let uu____4967 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4967  in
                      let uu____4968 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4966 uu____4968  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4965  in
                  FStar_Pprint.op_Hat_Hat uu____4963 uu____4964  in
                FStar_Pprint.group uu____4962  in
              let uu____4969 =
                let uu____4970 = p_noSeqTerm ps pb e3  in jump2 uu____4970
                 in
              FStar_Pprint.op_Hat_Hat uu____4961 uu____4969  in
            FStar_Pprint.group uu____4960
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4978 =
              let uu____4979 = str "requires"  in
              let uu____4980 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4979 uu____4980  in
            FStar_Pprint.group uu____4978
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4988 =
              let uu____4989 = str "ensures"  in
              let uu____4990 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4989 uu____4990  in
            FStar_Pprint.group uu____4988
        | FStar_Parser_AST.Attributes es ->
            let uu____4994 =
              let uu____4995 = str "attributes"  in
              let uu____4996 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4995 uu____4996  in
            FStar_Pprint.group uu____4994
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5000 =
                let uu____5001 =
                  let uu____5002 = str "if"  in
                  let uu____5003 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5002 uu____5003  in
                let uu____5004 =
                  let uu____5005 = str "then"  in
                  let uu____5006 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5005 uu____5006  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5001 uu____5004  in
              FStar_Pprint.group uu____5000
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5009,uu____5010,e31) when
                     is_unit e31 ->
                     let uu____5012 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5012
                 | uu____5013 -> p_noSeqTerm false false e2  in
               let uu____5014 =
                 let uu____5015 =
                   let uu____5016 = str "if"  in
                   let uu____5017 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5016 uu____5017  in
                 let uu____5018 =
                   let uu____5019 =
                     let uu____5020 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5020 e2_doc  in
                   let uu____5021 =
                     let uu____5022 = str "else"  in
                     let uu____5023 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5022 uu____5023  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5019 uu____5021  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5015 uu____5018  in
               FStar_Pprint.group uu____5014)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5046 =
              let uu____5047 =
                let uu____5048 =
                  let uu____5049 = str "try"  in
                  let uu____5050 = p_noSeqTerm false false e1  in
                  prefix2 uu____5049 uu____5050  in
                let uu____5051 =
                  let uu____5052 = str "with"  in
                  let uu____5053 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5052 uu____5053  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5048 uu____5051  in
              FStar_Pprint.group uu____5047  in
            let uu____5062 = paren_if (ps || pb)  in uu____5062 uu____5046
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5089 =
              let uu____5090 =
                let uu____5091 =
                  let uu____5092 = str "match"  in
                  let uu____5093 = p_noSeqTerm false false e1  in
                  let uu____5094 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5092 uu____5093 uu____5094
                   in
                let uu____5095 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5091 uu____5095  in
              FStar_Pprint.group uu____5090  in
            let uu____5104 = paren_if (ps || pb)  in uu____5104 uu____5089
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5111 =
              let uu____5112 =
                let uu____5113 =
                  let uu____5114 = str "let open"  in
                  let uu____5115 = p_quident uid  in
                  let uu____5116 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5114 uu____5115 uu____5116
                   in
                let uu____5117 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5113 uu____5117  in
              FStar_Pprint.group uu____5112  in
            let uu____5118 = paren_if ps  in uu____5118 uu____5111
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5182 is_last =
              match uu____5182 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5215 =
                          let uu____5216 = str "let"  in
                          let uu____5217 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5216 uu____5217
                           in
                        FStar_Pprint.group uu____5215
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5218 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5223 =
                    if is_last
                    then
                      let uu____5224 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5225 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5224 doc_expr uu____5225
                    else
                      (let uu____5227 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5227)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5223
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5273 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5273
                     else
                       (let uu____5281 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5281)) lbs
               in
            let lbs_doc =
              let uu____5289 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5289  in
            let uu____5290 =
              let uu____5291 =
                let uu____5292 =
                  let uu____5293 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5293
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5292  in
              FStar_Pprint.group uu____5291  in
            let uu____5294 = paren_if ps  in uu____5294 uu____5290
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5301;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5304;
                                                             FStar_Parser_AST.level
                                                               = uu____5305;_})
            when matches_var maybe_x x ->
            let uu____5332 =
              let uu____5333 =
                let uu____5334 = str "function"  in
                let uu____5335 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5334 uu____5335  in
              FStar_Pprint.group uu____5333  in
            let uu____5344 = paren_if (ps || pb)  in uu____5344 uu____5332
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5350 =
              let uu____5351 = str "quote"  in
              let uu____5352 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5351 uu____5352  in
            FStar_Pprint.group uu____5350
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5354 =
              let uu____5355 = str "`"  in
              let uu____5356 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5355 uu____5356  in
            FStar_Pprint.group uu____5354
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5358 =
              let uu____5359 = str "%`"  in
              let uu____5360 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5359 uu____5360  in
            FStar_Pprint.group uu____5358
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5362 =
              let uu____5363 = str "`#"  in
              let uu____5364 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5363 uu____5364  in
            FStar_Pprint.group uu____5362
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5366 =
              let uu____5367 = str "`@"  in
              let uu____5368 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5367 uu____5368  in
            FStar_Pprint.group uu____5366
        | uu____5369 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___111_5370  ->
    match uu___111_5370 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5382 =
          let uu____5383 = str "[@"  in
          let uu____5384 =
            let uu____5385 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5386 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5385 uu____5386  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5383 uu____5384  in
        FStar_Pprint.group uu____5382

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
                 let uu____5412 =
                   let uu____5413 =
                     let uu____5414 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5414 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5413 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5412 term_doc
             | pats ->
                 let uu____5420 =
                   let uu____5421 =
                     let uu____5422 =
                       let uu____5423 =
                         let uu____5424 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5424
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5423 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5425 = p_trigger trigger  in
                     prefix2 uu____5422 uu____5425  in
                   FStar_Pprint.group uu____5421  in
                 prefix2 uu____5420 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5445 =
                   let uu____5446 =
                     let uu____5447 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5447 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5446 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5445 term_doc
             | pats ->
                 let uu____5453 =
                   let uu____5454 =
                     let uu____5455 =
                       let uu____5456 =
                         let uu____5457 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5457
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5456 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5458 = p_trigger trigger  in
                     prefix2 uu____5455 uu____5458  in
                   FStar_Pprint.group uu____5454  in
                 prefix2 uu____5453 term_doc)
        | uu____5459 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5461 -> str "forall"
    | FStar_Parser_AST.QExists uu____5474 -> str "exists"
    | uu____5487 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___112_5488  ->
    match uu___112_5488 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5500 =
          let uu____5501 =
            let uu____5502 =
              let uu____5503 = str "pattern"  in
              let uu____5504 =
                let uu____5505 =
                  let uu____5506 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5506
                   in
                FStar_Pprint.op_Hat_Hat uu____5505 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5503 uu____5504  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5502  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5501  in
        FStar_Pprint.group uu____5500

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5512 = str "\\/"  in
    FStar_Pprint.separate_map uu____5512 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5518 =
      let uu____5519 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5519 p_appTerm pats  in
    FStar_Pprint.group uu____5518

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5529 =
              let uu____5530 =
                let uu____5531 = str "fun"  in
                let uu____5532 =
                  let uu____5533 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5533
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5531 uu____5532  in
              let uu____5534 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5530 uu____5534  in
            let uu____5535 = paren_if ps  in uu____5535 uu____5529
        | uu____5540 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5544  ->
      match uu____5544 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5567 =
                    let uu____5568 =
                      let uu____5569 =
                        let uu____5570 = p_tuplePattern p  in
                        let uu____5571 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5570 uu____5571  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5569
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5568  in
                  FStar_Pprint.group uu____5567
              | FStar_Pervasives_Native.Some f ->
                  let uu____5573 =
                    let uu____5574 =
                      let uu____5575 =
                        let uu____5576 =
                          let uu____5577 =
                            let uu____5578 = p_tuplePattern p  in
                            let uu____5579 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5578
                              uu____5579
                             in
                          FStar_Pprint.group uu____5577  in
                        let uu____5580 =
                          let uu____5581 =
                            let uu____5584 = p_tmFormula f  in
                            [uu____5584; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5581  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5576 uu____5580
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5575
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5574  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5573
               in
            let uu____5585 =
              let uu____5586 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5586  in
            FStar_Pprint.group uu____5585  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5595 =
                      let uu____5596 =
                        let uu____5597 =
                          let uu____5598 =
                            let uu____5599 =
                              let uu____5600 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5600  in
                            FStar_Pprint.separate_map uu____5599
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5598
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5597
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5596  in
                    FStar_Pprint.group uu____5595
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5601 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5603;_},e1::e2::[])
        ->
        let uu____5608 = str "<==>"  in
        let uu____5609 = p_tmImplies e1  in
        let uu____5610 = p_tmIff e2  in
        infix0 uu____5608 uu____5609 uu____5610
    | uu____5611 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5613;_},e1::e2::[])
        ->
        let uu____5618 = str "==>"  in
        let uu____5619 = p_tmArrow p_tmFormula e1  in
        let uu____5620 = p_tmImplies e2  in
        infix0 uu____5618 uu____5619 uu____5620
    | uu____5621 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5629 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5629 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5650 ->
               let uu____5651 =
                 let uu____5652 =
                   let uu____5653 =
                     let uu____5654 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5654
                      in
                   FStar_Pprint.separate uu____5653 terms  in
                 let uu____5655 =
                   let uu____5656 =
                     let uu____5657 =
                       let uu____5658 =
                         let uu____5659 =
                           let uu____5660 =
                             let uu____5661 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5661
                              in
                           FStar_Pprint.separate uu____5660 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5659 last_op  in
                       let uu____5662 =
                         let uu____5663 =
                           let uu____5664 =
                             let uu____5665 =
                               let uu____5666 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5666
                                in
                             FStar_Pprint.separate uu____5665 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5664 last_op  in
                         jump2 uu____5663  in
                       FStar_Pprint.ifflat uu____5658 uu____5662  in
                     FStar_Pprint.group uu____5657  in
                   let uu____5667 = FStar_List.hd last1  in
                   prefix2 uu____5656 uu____5667  in
                 FStar_Pprint.ifflat uu____5652 uu____5655  in
               FStar_Pprint.group uu____5651)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5680 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5685 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5680 uu____5685
      | uu____5688 -> let uu____5689 = p_Tm e  in [uu____5689]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5692 =
        let uu____5693 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5693 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5692  in
    let disj =
      let uu____5695 =
        let uu____5696 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5696 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5695  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5715;_},e1::e2::[])
        ->
        let uu____5720 = p_tmDisjunction e1  in
        let uu____5725 = let uu____5730 = p_tmConjunction e2  in [uu____5730]
           in
        FStar_List.append uu____5720 uu____5725
    | uu____5739 -> let uu____5740 = p_tmConjunction e  in [uu____5740]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5750;_},e1::e2::[])
        ->
        let uu____5755 = p_tmConjunction e1  in
        let uu____5758 = let uu____5761 = p_tmTuple e2  in [uu____5761]  in
        FStar_List.append uu____5755 uu____5758
    | uu____5762 -> let uu____5763 = p_tmTuple e  in [uu____5763]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5780 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5780
          (fun uu____5788  ->
             match uu____5788 with | (e1,uu____5794) -> p_tmEq e1) args
    | uu____5795 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5800 =
             let uu____5801 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5801  in
           FStar_Pprint.group uu____5800)

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
               (let uu____5818 = FStar_Ident.text_of_id op  in
                uu____5818 = "="))
              ||
              (let uu____5820 = FStar_Ident.text_of_id op  in
               uu____5820 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5822 = levels op1  in
            (match uu____5822 with
             | (left1,mine,right1) ->
                 let uu____5832 =
                   let uu____5833 = FStar_All.pipe_left str op1  in
                   let uu____5834 = p_tmEqWith' p_X left1 e1  in
                   let uu____5835 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5833 uu____5834 uu____5835  in
                 paren_if_gt curr mine uu____5832)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5836;_},e1::e2::[])
            ->
            let uu____5841 =
              let uu____5842 = p_tmEqWith p_X e1  in
              let uu____5843 =
                let uu____5844 =
                  let uu____5845 =
                    let uu____5846 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5846  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5845  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5844  in
              FStar_Pprint.op_Hat_Hat uu____5842 uu____5843  in
            FStar_Pprint.group uu____5841
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5847;_},e1::[])
            ->
            let uu____5851 = levels "-"  in
            (match uu____5851 with
             | (left1,mine,right1) ->
                 let uu____5861 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5861)
        | uu____5862 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5906)::(e2,uu____5908)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5928 = is_list e  in Prims.op_Negation uu____5928)
              ->
              let op = "::"  in
              let uu____5930 = levels op  in
              (match uu____5930 with
               | (left1,mine,right1) ->
                   let uu____5940 =
                     let uu____5941 = str op  in
                     let uu____5942 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5943 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5941 uu____5942 uu____5943  in
                   paren_if_gt curr mine uu____5940)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5951 = levels op  in
              (match uu____5951 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5967 = p_binder false b  in
                     let uu____5968 =
                       let uu____5969 =
                         let uu____5970 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5970 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5969
                        in
                     FStar_Pprint.op_Hat_Hat uu____5967 uu____5968  in
                   let uu____5971 =
                     let uu____5972 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5973 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5972 uu____5973  in
                   paren_if_gt curr mine uu____5971)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5974;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5999 = levels op  in
              (match uu____5999 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6009 = str op  in
                     let uu____6010 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6011 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6009 uu____6010 uu____6011
                   else
                     (let uu____6013 =
                        let uu____6014 = str op  in
                        let uu____6015 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6016 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6014 uu____6015 uu____6016  in
                      paren_if_gt curr mine uu____6013))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6023 = levels op1  in
              (match uu____6023 with
               | (left1,mine,right1) ->
                   let uu____6033 =
                     let uu____6034 = str op1  in
                     let uu____6035 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6036 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6034 uu____6035 uu____6036  in
                   paren_if_gt curr mine uu____6033)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6055 =
                let uu____6056 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6057 =
                  let uu____6058 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6058 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6056 uu____6057  in
              braces_with_nesting uu____6055
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6063;_},e1::[])
              ->
              let uu____6067 =
                let uu____6068 = str "~"  in
                let uu____6069 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6068 uu____6069  in
              FStar_Pprint.group uu____6067
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6071;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6077 = levels op  in
                   (match uu____6077 with
                    | (left1,mine,right1) ->
                        let uu____6087 =
                          let uu____6088 = str op  in
                          let uu____6089 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6090 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6088 uu____6089 uu____6090  in
                        paren_if_gt curr mine uu____6087)
               | uu____6091 -> p_X e)
          | uu____6092 -> p_X e

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
        let uu____6099 =
          let uu____6100 = p_lident lid  in
          let uu____6101 =
            let uu____6102 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6102  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6100 uu____6101  in
        FStar_Pprint.group uu____6099
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6105 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6107 = p_appTerm e  in
    let uu____6108 =
      let uu____6109 =
        let uu____6110 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6110 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6109  in
    FStar_Pprint.op_Hat_Hat uu____6107 uu____6108

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6115 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6115 t phi
      | FStar_Parser_AST.TAnnotated uu____6116 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6121 ->
          let uu____6122 =
            let uu____6123 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6123
             in
          failwith uu____6122
      | FStar_Parser_AST.TVariable uu____6124 ->
          let uu____6125 =
            let uu____6126 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6126
             in
          failwith uu____6125
      | FStar_Parser_AST.NoName uu____6127 ->
          let uu____6128 =
            let uu____6129 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6129
             in
          failwith uu____6128

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6131  ->
      match uu____6131 with
      | (lid,e) ->
          let uu____6138 =
            let uu____6139 = p_qlident lid  in
            let uu____6140 =
              let uu____6141 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6141
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6139 uu____6140  in
          FStar_Pprint.group uu____6138

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6143 when is_general_application e ->
        let uu____6150 = head_and_args e  in
        (match uu____6150 with
         | (head1,args) ->
             let uu____6175 =
               let uu____6186 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6186
               then
                 let uu____6216 =
                   FStar_Util.take
                     (fun uu____6240  ->
                        match uu____6240 with
                        | (uu____6245,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6216 with
                 | (fs_typ_args,args1) ->
                     let uu____6283 =
                       let uu____6284 = p_indexingTerm head1  in
                       let uu____6285 =
                         let uu____6286 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6286 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6284 uu____6285  in
                     (uu____6283, args1)
               else
                 (let uu____6298 = p_indexingTerm head1  in
                  (uu____6298, args))
                in
             (match uu____6175 with
              | (head_doc,args1) ->
                  let uu____6319 =
                    let uu____6320 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6320 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6319))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6340 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6340)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6358 =
               let uu____6359 = p_quident lid  in
               let uu____6360 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6359 uu____6360  in
             FStar_Pprint.group uu____6358
         | hd1::tl1 ->
             let uu____6377 =
               let uu____6378 =
                 let uu____6379 =
                   let uu____6380 = p_quident lid  in
                   let uu____6381 = p_argTerm hd1  in
                   prefix2 uu____6380 uu____6381  in
                 FStar_Pprint.group uu____6379  in
               let uu____6382 =
                 let uu____6383 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6383  in
               FStar_Pprint.op_Hat_Hat uu____6378 uu____6382  in
             FStar_Pprint.group uu____6377)
    | uu____6388 -> p_indexingTerm e

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
         (let uu____6397 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6397 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6399 = str "#"  in
        let uu____6400 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6399 uu____6400
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6402  ->
    match uu____6402 with | (e,uu____6408) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6413;_},e1::e2::[])
          ->
          let uu____6418 =
            let uu____6419 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6420 =
              let uu____6421 =
                let uu____6422 = p_term false false e2  in
                soft_parens_with_nesting uu____6422  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6421  in
            FStar_Pprint.op_Hat_Hat uu____6419 uu____6420  in
          FStar_Pprint.group uu____6418
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6423;_},e1::e2::[])
          ->
          let uu____6428 =
            let uu____6429 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6430 =
              let uu____6431 =
                let uu____6432 = p_term false false e2  in
                soft_brackets_with_nesting uu____6432  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6431  in
            FStar_Pprint.op_Hat_Hat uu____6429 uu____6430  in
          FStar_Pprint.group uu____6428
      | uu____6433 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6438 = p_quident lid  in
        let uu____6439 =
          let uu____6440 =
            let uu____6441 = p_term false false e1  in
            soft_parens_with_nesting uu____6441  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6440  in
        FStar_Pprint.op_Hat_Hat uu____6438 uu____6439
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6447 =
          let uu____6448 = FStar_Ident.text_of_id op  in str uu____6448  in
        let uu____6449 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6447 uu____6449
    | uu____6450 -> p_atomicTermNotQUident e

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
         | uu____6459 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6466 =
          let uu____6467 = FStar_Ident.text_of_id op  in str uu____6467  in
        let uu____6468 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6466 uu____6468
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6472 =
          let uu____6473 =
            let uu____6474 =
              let uu____6475 = FStar_Ident.text_of_id op  in str uu____6475
               in
            let uu____6476 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6474 uu____6476  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6473  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6472
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6491 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6492 =
          let uu____6493 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6494 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6493 p_tmEq uu____6494  in
        let uu____6501 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6491 uu____6492 uu____6501
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6504 =
          let uu____6505 = p_atomicTermNotQUident e1  in
          let uu____6506 =
            let uu____6507 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6507  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6505 uu____6506
           in
        FStar_Pprint.group uu____6504
    | uu____6508 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6513 = p_quident constr_lid  in
        let uu____6514 =
          let uu____6515 =
            let uu____6516 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6516  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6515  in
        FStar_Pprint.op_Hat_Hat uu____6513 uu____6514
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6518 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6518 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6520 = p_term false false e1  in
        soft_parens_with_nesting uu____6520
    | uu____6521 when is_array e ->
        let es = extract_from_list e  in
        let uu____6525 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6526 =
          let uu____6527 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6527
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6530 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6525 uu____6526 uu____6530
    | uu____6531 when is_list e ->
        let uu____6532 =
          let uu____6533 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6534 = extract_from_list e  in
          separate_map_or_flow_last uu____6533
            (fun ps  -> p_noSeqTerm ps false) uu____6534
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6532 FStar_Pprint.rbracket
    | uu____6539 when is_lex_list e ->
        let uu____6540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6541 =
          let uu____6542 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6543 = extract_from_list e  in
          separate_map_or_flow_last uu____6542
            (fun ps  -> p_noSeqTerm ps false) uu____6543
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6540 uu____6541 FStar_Pprint.rbracket
    | uu____6548 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6552 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6553 =
          let uu____6554 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6554 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6552 uu____6553 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6558 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6559 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6558 uu____6559
    | FStar_Parser_AST.Op (op,args) when
        let uu____6566 = handleable_op op args  in
        Prims.op_Negation uu____6566 ->
        let uu____6567 =
          let uu____6568 =
            let uu____6569 = FStar_Ident.text_of_id op  in
            let uu____6570 =
              let uu____6571 =
                let uu____6572 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6572
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6571  in
            Prims.strcat uu____6569 uu____6570  in
          Prims.strcat "Operation " uu____6568  in
        failwith uu____6567
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6574 = str "u#"  in
        let uu____6575 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6574 uu____6575
    | FStar_Parser_AST.Wild  ->
        let uu____6576 = p_term false false e  in
        soft_parens_with_nesting uu____6576
    | FStar_Parser_AST.Const uu____6577 ->
        let uu____6578 = p_term false false e  in
        soft_parens_with_nesting uu____6578
    | FStar_Parser_AST.Op uu____6579 ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586
    | FStar_Parser_AST.Tvar uu____6587 ->
        let uu____6588 = p_term false false e  in
        soft_parens_with_nesting uu____6588
    | FStar_Parser_AST.Var uu____6589 ->
        let uu____6590 = p_term false false e  in
        soft_parens_with_nesting uu____6590
    | FStar_Parser_AST.Name uu____6591 ->
        let uu____6592 = p_term false false e  in
        soft_parens_with_nesting uu____6592
    | FStar_Parser_AST.Construct uu____6593 ->
        let uu____6604 = p_term false false e  in
        soft_parens_with_nesting uu____6604
    | FStar_Parser_AST.Abs uu____6605 ->
        let uu____6612 = p_term false false e  in
        soft_parens_with_nesting uu____6612
    | FStar_Parser_AST.App uu____6613 ->
        let uu____6620 = p_term false false e  in
        soft_parens_with_nesting uu____6620
    | FStar_Parser_AST.Let uu____6621 ->
        let uu____6642 = p_term false false e  in
        soft_parens_with_nesting uu____6642
    | FStar_Parser_AST.LetOpen uu____6643 ->
        let uu____6648 = p_term false false e  in
        soft_parens_with_nesting uu____6648
    | FStar_Parser_AST.Seq uu____6649 ->
        let uu____6654 = p_term false false e  in
        soft_parens_with_nesting uu____6654
    | FStar_Parser_AST.Bind uu____6655 ->
        let uu____6662 = p_term false false e  in
        soft_parens_with_nesting uu____6662
    | FStar_Parser_AST.If uu____6663 ->
        let uu____6670 = p_term false false e  in
        soft_parens_with_nesting uu____6670
    | FStar_Parser_AST.Match uu____6671 ->
        let uu____6686 = p_term false false e  in
        soft_parens_with_nesting uu____6686
    | FStar_Parser_AST.TryWith uu____6687 ->
        let uu____6702 = p_term false false e  in
        soft_parens_with_nesting uu____6702
    | FStar_Parser_AST.Ascribed uu____6703 ->
        let uu____6712 = p_term false false e  in
        soft_parens_with_nesting uu____6712
    | FStar_Parser_AST.Record uu____6713 ->
        let uu____6726 = p_term false false e  in
        soft_parens_with_nesting uu____6726
    | FStar_Parser_AST.Project uu____6727 ->
        let uu____6732 = p_term false false e  in
        soft_parens_with_nesting uu____6732
    | FStar_Parser_AST.Product uu____6733 ->
        let uu____6740 = p_term false false e  in
        soft_parens_with_nesting uu____6740
    | FStar_Parser_AST.Sum uu____6741 ->
        let uu____6748 = p_term false false e  in
        soft_parens_with_nesting uu____6748
    | FStar_Parser_AST.QForall uu____6749 ->
        let uu____6762 = p_term false false e  in
        soft_parens_with_nesting uu____6762
    | FStar_Parser_AST.QExists uu____6763 ->
        let uu____6776 = p_term false false e  in
        soft_parens_with_nesting uu____6776
    | FStar_Parser_AST.Refine uu____6777 ->
        let uu____6782 = p_term false false e  in
        soft_parens_with_nesting uu____6782
    | FStar_Parser_AST.NamedTyp uu____6783 ->
        let uu____6788 = p_term false false e  in
        soft_parens_with_nesting uu____6788
    | FStar_Parser_AST.Requires uu____6789 ->
        let uu____6796 = p_term false false e  in
        soft_parens_with_nesting uu____6796
    | FStar_Parser_AST.Ensures uu____6797 ->
        let uu____6804 = p_term false false e  in
        soft_parens_with_nesting uu____6804
    | FStar_Parser_AST.Attributes uu____6805 ->
        let uu____6808 = p_term false false e  in
        soft_parens_with_nesting uu____6808
    | FStar_Parser_AST.Quote uu____6809 ->
        let uu____6814 = p_term false false e  in
        soft_parens_with_nesting uu____6814
    | FStar_Parser_AST.VQuote uu____6815 ->
        let uu____6816 = p_term false false e  in
        soft_parens_with_nesting uu____6816
    | FStar_Parser_AST.Antiquote uu____6817 ->
        let uu____6822 = p_term false false e  in
        soft_parens_with_nesting uu____6822

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___115_6823  ->
    match uu___115_6823 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6829) ->
        let uu____6830 = str s  in FStar_Pprint.dquotes uu____6830
    | FStar_Const.Const_bytearray (bytes,uu____6832) ->
        let uu____6837 =
          let uu____6838 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6838  in
        let uu____6839 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6837 uu____6839
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___113_6859 =
          match uu___113_6859 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___114_6865 =
          match uu___114_6865 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6876  ->
               match uu____6876 with
               | (s,w) ->
                   let uu____6883 = signedness s  in
                   let uu____6884 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6883 uu____6884)
            sign_width_opt
           in
        let uu____6885 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6885 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6887 = FStar_Range.string_of_range r  in str uu____6887
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6889 = p_quident lid  in
        let uu____6890 =
          let uu____6891 =
            let uu____6892 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6892  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6891  in
        FStar_Pprint.op_Hat_Hat uu____6889 uu____6890

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6894 = str "u#"  in
    let uu____6895 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6894 uu____6895

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6897;_},u1::u2::[])
        ->
        let uu____6902 =
          let uu____6903 = p_universeFrom u1  in
          let uu____6904 =
            let uu____6905 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6905  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6903 uu____6904  in
        FStar_Pprint.group uu____6902
    | FStar_Parser_AST.App uu____6906 ->
        let uu____6913 = head_and_args u  in
        (match uu____6913 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6939 =
                    let uu____6940 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6941 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6949  ->
                           match uu____6949 with
                           | (u1,uu____6955) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6940 uu____6941  in
                  FStar_Pprint.group uu____6939
              | uu____6956 ->
                  let uu____6957 =
                    let uu____6958 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6958
                     in
                  failwith uu____6957))
    | uu____6959 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6982 = FStar_Ident.text_of_id id1  in str uu____6982
    | FStar_Parser_AST.Paren u1 ->
        let uu____6984 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6984
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6985;_},uu____6986::uu____6987::[])
        ->
        let uu____6990 = p_universeFrom u  in
        soft_parens_with_nesting uu____6990
    | FStar_Parser_AST.App uu____6991 ->
        let uu____6998 = p_universeFrom u  in
        soft_parens_with_nesting uu____6998
    | uu____6999 ->
        let uu____7000 =
          let uu____7001 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7001
           in
        failwith uu____7000

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
       | FStar_Parser_AST.Module (uu____7073,decls) ->
           let uu____7079 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7079
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7088,decls,uu____7090) ->
           let uu____7095 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7095
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7148  ->
         match uu____7148 with | (comment,range) -> str comment) comments
  
let (extract_decl_range :
  FStar_Parser_AST.decl ->
    (FStar_Range.range,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun d  ->
    let qual_lines =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7170)) -> (Prims.parse_int "0")
      | ([],uu____7173) -> (Prims.parse_int "0")
      | uu____7176 -> (Prims.parse_int "1")  in
    let fsdoc =
      if FStar_Util.is_some d.FStar_Parser_AST.doc
      then (Prims.parse_int "1")
      else (Prims.parse_int "0")  in
    ((d.FStar_Parser_AST.drange), qual_lines, fsdoc)
  
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
        | FStar_Parser_AST.Module (uu____7222,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7228,decls,uu____7230) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7275 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7288;
                 FStar_Parser_AST.doc = uu____7289;
                 FStar_Parser_AST.quals = uu____7290;
                 FStar_Parser_AST.attrs = uu____7291;_}::uu____7292 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7298 =
                   let uu____7301 =
                     let uu____7304 = FStar_List.tl ds  in d :: uu____7304
                      in
                   d0 :: uu____7301  in
                 (uu____7298, (d0.FStar_Parser_AST.drange))
             | uu____7309 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7275 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7363 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7363 (Prims.parse_int "0")
                      (Prims.parse_int "0") FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7459 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7459, comments1))))))
  