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
  fun uu___104_1242  ->
    match uu___104_1242 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___105_1267  ->
      match uu___105_1267 with
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
  let levels_from_associativity l uu___106_1454 =
    match uu___106_1454 with
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
type decl_meta =
  {
  r: FStar_Range.range ;
  has_qs: Prims.bool ;
  has_attrs: Prims.bool ;
  has_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;_} ->
        __fname__r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;_} ->
        __fname__has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;_} ->
        __fname__has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;_} ->
        __fname__has_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false
  } 
let with_comment :
  'Auu____2116 .
    ('Auu____2116 -> FStar_Pprint.document) ->
      'Auu____2116 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2157 = FStar_ST.op_Bang comment_stack  in
          match uu____2157 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2216 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2216
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2253 =
                    let uu____2254 =
                      let uu____2255 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2255
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2254  in
                  comments_before_pos uu____2253 print_pos lookahead_pos))
              else
                (let uu____2257 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2257))
           in
        let uu____2258 =
          let uu____2263 =
            let uu____2264 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2264  in
          let uu____2265 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2263 uu____2265  in
        match uu____2258 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2271 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2271
              else comments  in
            let uu____2277 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2277
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun meta_decl  ->
          fun doc1  ->
            let uu____2303 = FStar_ST.op_Bang comment_stack  in
            match uu____2303 with
            | (comment,crange)::cs when
                FStar_Range.range_before_pos crange pos_end ->
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let lnum =
                    let uu____2387 =
                      let uu____2388 =
                        let uu____2389 = FStar_Range.start_of_range crange
                           in
                        FStar_Range.line_of_pos uu____2389  in
                      uu____2388 - lbegin  in
                    max k uu____2387  in
                  let lnum1 = min (Prims.parse_int "2") lnum  in
                  let doc2 =
                    let uu____2392 =
                      let uu____2393 =
                        FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                      let uu____2394 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2393 uu____2394  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____2392  in
                  let uu____2395 =
                    let uu____2396 = FStar_Range.end_of_range crange  in
                    FStar_Range.line_of_pos uu____2396  in
                  place_comments_until_pos (Prims.parse_int "1") uu____2395
                    pos_end meta_decl doc2))
            | uu____2397 ->
                if doc1 = FStar_Pprint.empty
                then FStar_Pprint.empty
                else
                  (let end_correction =
                     if meta_decl.has_qs
                     then (Prims.parse_int "1")
                     else (Prims.parse_int "0")  in
                   let fsdoc_correction =
                     if meta_decl.has_fsdoc
                     then (Prims.parse_int "1")
                     else (Prims.parse_int "0")  in
                   let lnum =
                     let uu____2410 = FStar_Range.line_of_pos pos_end  in
                     uu____2410 - lbegin  in
                   let lnum1 =
                     if lnum >= (Prims.parse_int "2")
                     then lnum - end_correction
                     else lnum  in
                   let lnum2 = min (Prims.parse_int "2") lnum1  in
                   let lnum3 =
                     if lnum2 >= (Prims.parse_int "2")
                     then lnum2 - fsdoc_correction
                     else lnum2  in
                   let uu____2416 =
                     FStar_Pprint.repeat lnum3 FStar_Pprint.hardline  in
                   FStar_Pprint.op_Hat_Hat doc1 uu____2416)
  
let separate_map_with_comments :
  'Auu____2429 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2429 -> FStar_Pprint.document) ->
          'Auu____2429 Prims.list ->
            ('Auu____2429 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2486 x =
              match uu____2486 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2501 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2501 meta_decl doc1
                     in
                  let uu____2502 =
                    let uu____2503 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2503  in
                  let uu____2504 =
                    let uu____2505 =
                      let uu____2506 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2506  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2505  in
                  (uu____2502, uu____2504)
               in
            let uu____2507 =
              let uu____2514 = FStar_List.hd xs  in
              let uu____2515 = FStar_List.tl xs  in (uu____2514, uu____2515)
               in
            match uu____2507 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2532 =
                    let uu____2533 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2533  in
                  let uu____2534 =
                    let uu____2535 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2535  in
                  (uu____2532, uu____2534)  in
                let uu____2536 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2536
  
let separate_map_with_comments_kw :
  'Auu____2559 'Auu____2560 .
    'Auu____2559 ->
      'Auu____2559 ->
        ('Auu____2559 -> 'Auu____2560 -> FStar_Pprint.document) ->
          'Auu____2560 Prims.list ->
            ('Auu____2560 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2622 x =
              match uu____2622 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2637 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2637 meta_decl doc1
                     in
                  let uu____2638 =
                    let uu____2639 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2639  in
                  let uu____2640 =
                    let uu____2641 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2641  in
                  (uu____2638, uu____2640)
               in
            let uu____2642 =
              let uu____2649 = FStar_List.hd xs  in
              let uu____2650 = FStar_List.tl xs  in (uu____2649, uu____2650)
               in
            match uu____2642 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2667 =
                    let uu____2668 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2668  in
                  let uu____2669 = f prefix1 x  in (uu____2667, uu____2669)
                   in
                let uu____2670 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2670
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3380)) ->
          let uu____3383 =
            let uu____3384 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3384 FStar_Util.is_upper  in
          if uu____3383
          then
            let uu____3387 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3387 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3389 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3396 =
      FStar_Pprint.optional
        (fun d1  ->
           let uu____3400 = p_fsdoc d1  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3400)
        d.FStar_Parser_AST.doc
       in
    let uu____3401 =
      let uu____3402 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3403 =
        let uu____3404 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3404  in
      FStar_Pprint.op_Hat_Hat uu____3402 uu____3403  in
    FStar_Pprint.op_Hat_Hat uu____3396 uu____3401

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3406 ->
        let uu____3407 =
          let uu____3408 = str "@ "  in
          let uu____3409 =
            let uu____3410 =
              let uu____3411 =
                let uu____3412 =
                  let uu____3413 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3413  in
                FStar_Pprint.op_Hat_Hat uu____3412 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3411  in
            FStar_Pprint.op_Hat_Hat uu____3410 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3408 uu____3409  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3407

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3416  ->
    match uu____3416 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3452 =
                match uu____3452 with
                | (kwd,arg) ->
                    let uu____3459 = str "@"  in
                    let uu____3460 =
                      let uu____3461 = str kwd  in
                      let uu____3462 =
                        let uu____3463 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3463
                         in
                      FStar_Pprint.op_Hat_Hat uu____3461 uu____3462  in
                    FStar_Pprint.op_Hat_Hat uu____3459 uu____3460
                 in
              let uu____3464 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____3464 FStar_Pprint.hardline
           in
        let uu____3469 =
          let uu____3470 =
            let uu____3471 =
              let uu____3472 = str doc1  in
              let uu____3473 =
                let uu____3474 =
                  let uu____3475 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3475  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3474  in
              FStar_Pprint.op_Hat_Hat uu____3472 uu____3473  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3471  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3470  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3469

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3479 =
          let uu____3480 = str "val"  in
          let uu____3481 =
            let uu____3482 =
              let uu____3483 = p_lident lid  in
              let uu____3484 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3483 uu____3484  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3482  in
          FStar_Pprint.op_Hat_Hat uu____3480 uu____3481  in
        let uu____3485 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3479 uu____3485
    | FStar_Parser_AST.TopLevelLet (uu____3486,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3511 =
               let uu____3512 = str "let"  in p_letlhs uu____3512 lb  in
             FStar_Pprint.group uu____3511) lbs
    | uu____3513 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___107_3528 =
          match uu___107_3528 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3536 = f x  in
              let uu____3537 =
                let uu____3538 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3538  in
              FStar_Pprint.op_Hat_Hat uu____3536 uu____3537
           in
        let uu____3539 = str "["  in
        let uu____3540 =
          let uu____3541 = p_list' l  in
          let uu____3542 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3541 uu____3542  in
        FStar_Pprint.op_Hat_Hat uu____3539 uu____3540

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3545 =
          let uu____3546 = str "open"  in
          let uu____3547 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3546 uu____3547  in
        FStar_Pprint.group uu____3545
    | FStar_Parser_AST.Include uid ->
        let uu____3549 =
          let uu____3550 = str "include"  in
          let uu____3551 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3550 uu____3551  in
        FStar_Pprint.group uu____3549
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3554 =
          let uu____3555 = str "module"  in
          let uu____3556 =
            let uu____3557 =
              let uu____3558 = p_uident uid1  in
              let uu____3559 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3558 uu____3559  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3557  in
          FStar_Pprint.op_Hat_Hat uu____3555 uu____3556  in
        let uu____3560 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3554 uu____3560
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3562 =
          let uu____3563 = str "module"  in
          let uu____3564 =
            let uu____3565 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3565  in
          FStar_Pprint.op_Hat_Hat uu____3563 uu____3564  in
        FStar_Pprint.group uu____3562
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3598 = str "effect"  in
          let uu____3599 =
            let uu____3600 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3600  in
          FStar_Pprint.op_Hat_Hat uu____3598 uu____3599  in
        let uu____3601 =
          let uu____3602 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3602 FStar_Pprint.equals
           in
        let uu____3603 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3601 uu____3603
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3621 =
          let uu____3622 = str "type"  in
          let uu____3623 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3622 uu____3623  in
        let uu____3636 =
          let uu____3637 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3675 =
                    let uu____3676 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3676 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3675)) uu____3637
           in
        FStar_Pprint.op_Hat_Hat uu____3621 uu____3636
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3692 = str "let"  in
          let uu____3693 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3692 uu____3693  in
        let uu____3694 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3694 p_letbinding lbs
          (fun uu____3703  ->
             match uu____3703 with
             | (p,t) ->
                 let uu____3710 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____3710;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc)
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3713 = str "val"  in
        let uu____3714 =
          let uu____3715 =
            let uu____3716 = p_lident lid  in
            let uu____3717 =
              let uu____3718 =
                let uu____3719 =
                  let uu____3720 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3720  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3719  in
              FStar_Pprint.group uu____3718  in
            FStar_Pprint.op_Hat_Hat uu____3716 uu____3717  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3715  in
        FStar_Pprint.op_Hat_Hat uu____3713 uu____3714
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3724 =
            let uu____3725 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3725 FStar_Util.is_upper  in
          if uu____3724
          then FStar_Pprint.empty
          else
            (let uu____3729 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3729 FStar_Pprint.space)
           in
        let uu____3730 =
          let uu____3731 = p_ident id1  in
          let uu____3732 =
            let uu____3733 =
              let uu____3734 =
                let uu____3735 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3735  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3734  in
            FStar_Pprint.group uu____3733  in
          FStar_Pprint.op_Hat_Hat uu____3731 uu____3732  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3730
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3742 = str "exception"  in
        let uu____3743 =
          let uu____3744 =
            let uu____3745 = p_uident uid  in
            let uu____3746 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3750 =
                     let uu____3751 = str "of"  in
                     let uu____3752 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3751 uu____3752  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3750) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3745 uu____3746  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3744  in
        FStar_Pprint.op_Hat_Hat uu____3742 uu____3743
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3754 = str "new_effect"  in
        let uu____3755 =
          let uu____3756 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3756  in
        FStar_Pprint.op_Hat_Hat uu____3754 uu____3755
    | FStar_Parser_AST.SubEffect se ->
        let uu____3758 = str "sub_effect"  in
        let uu____3759 =
          let uu____3760 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3760  in
        FStar_Pprint.op_Hat_Hat uu____3758 uu____3759
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3763 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3763 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3764 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3765) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3788 = str "%splice"  in
        let uu____3789 =
          let uu____3790 =
            let uu____3791 = str ";"  in p_list p_uident uu____3791 ids  in
          let uu____3792 =
            let uu____3793 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3793  in
          FStar_Pprint.op_Hat_Hat uu____3790 uu____3792  in
        FStar_Pprint.op_Hat_Hat uu____3788 uu____3789

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___108_3794  ->
    match uu___108_3794 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3796 = str "#set-options"  in
        let uu____3797 =
          let uu____3798 =
            let uu____3799 = str s  in FStar_Pprint.dquotes uu____3799  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3798  in
        FStar_Pprint.op_Hat_Hat uu____3796 uu____3797
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3803 = str "#reset-options"  in
        let uu____3804 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3808 =
                 let uu____3809 = str s  in FStar_Pprint.dquotes uu____3809
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3808) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3803 uu____3804
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3813 = str "#push-options"  in
        let uu____3814 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3818 =
                 let uu____3819 = str s  in FStar_Pprint.dquotes uu____3819
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3818) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3813 uu____3814
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
    fun uu____3844  ->
      match uu____3844 with
      | (typedecl,fsdoc_opt) ->
          let uu____3857 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3857 with
           | (decl,body) ->
               let uu____3875 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3875)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___109_3877  ->
      match uu___109_3877 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3907 = FStar_Pprint.empty  in
          let uu____3908 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3908, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3929 =
            let uu____3930 = p_typ false false t  in jump2 uu____3930  in
          let uu____3931 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3931, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3985 =
            match uu____3985 with
            | (lid1,t,doc_opt) ->
                let uu____4001 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4001
             in
          let p_fields uu____4017 =
            let uu____4018 =
              let uu____4019 =
                let uu____4020 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4020 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4019  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4018  in
          let uu____4029 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4029, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4090 =
            match uu____4090 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4116 =
                    let uu____4117 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4117  in
                  FStar_Range.extend_to_end_of_line uu____4116  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4143 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4156 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4156,
            ((fun uu____4162  ->
                let uu____4163 = datacon_doc ()  in jump2 uu____4163)))

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
  fun uu____4164  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4164 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4198 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4198  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4200 =
                        let uu____4203 =
                          let uu____4206 = p_fsdoc fsdoc  in
                          let uu____4207 =
                            let uu____4210 = cont lid_doc  in [uu____4210]
                             in
                          uu____4206 :: uu____4207  in
                        kw :: uu____4203  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4200
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4215 =
                        let uu____4216 =
                          let uu____4217 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4217 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4216
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4215
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4232 =
                          let uu____4233 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4233  in
                        prefix2 uu____4232 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4235  ->
      match uu____4235 with
      | (lid,t,doc_opt) ->
          let uu____4251 =
            let uu____4252 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4253 =
              let uu____4254 = p_lident lid  in
              let uu____4255 =
                let uu____4256 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4256  in
              FStar_Pprint.op_Hat_Hat uu____4254 uu____4255  in
            FStar_Pprint.op_Hat_Hat uu____4252 uu____4253  in
          FStar_Pprint.group uu____4251

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4257  ->
    match uu____4257 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4285 =
            let uu____4286 =
              let uu____4287 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4287  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4286  in
          FStar_Pprint.group uu____4285  in
        let uu____4288 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4289 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4293 =
                 let uu____4294 =
                   let uu____4295 =
                     let uu____4296 =
                       let uu____4297 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4297
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4296  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4295  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4294  in
               FStar_Pprint.group uu____4293) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4288 uu____4289

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4299  ->
      match uu____4299 with
      | (pat,uu____4305) ->
          let uu____4306 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4325 =
                  let uu____4326 =
                    let uu____4327 =
                      let uu____4328 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4328
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4327  in
                  FStar_Pprint.group uu____4326  in
                (pat1, uu____4325)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4340 =
                  let uu____4341 =
                    let uu____4342 =
                      let uu____4343 =
                        let uu____4344 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4344
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4343
                       in
                    FStar_Pprint.group uu____4342  in
                  let uu____4345 =
                    let uu____4346 =
                      let uu____4347 = str "by"  in
                      let uu____4348 =
                        let uu____4349 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4349
                         in
                      FStar_Pprint.op_Hat_Hat uu____4347 uu____4348  in
                    FStar_Pprint.group uu____4346  in
                  FStar_Pprint.op_Hat_Hat uu____4341 uu____4345  in
                (pat1, uu____4340)
            | uu____4350 -> (pat, FStar_Pprint.empty)  in
          (match uu____4306 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4354);
                       FStar_Parser_AST.prange = uu____4355;_},pats)
                    ->
                    let uu____4365 =
                      let uu____4366 =
                        let uu____4367 =
                          let uu____4368 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4368  in
                        FStar_Pprint.group uu____4367  in
                      let uu____4369 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4366 uu____4369  in
                    prefix2_nonempty uu____4365 ascr_doc
                | uu____4370 ->
                    let uu____4371 =
                      let uu____4372 =
                        let uu____4373 =
                          let uu____4374 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4374  in
                        FStar_Pprint.group uu____4373  in
                      FStar_Pprint.op_Hat_Hat uu____4372 ascr_doc  in
                    FStar_Pprint.group uu____4371))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4376  ->
      match uu____4376 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4385 =
            let uu____4386 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4386  in
          let uu____4387 =
            let uu____4388 =
              let uu____4389 =
                let uu____4390 =
                  let uu____4391 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4391  in
                FStar_Pprint.group uu____4390  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4389  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4388  in
          FStar_Pprint.ifflat uu____4385 uu____4387

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___110_4392  ->
    match uu___110_4392 with
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
        let uu____4417 = p_uident uid  in
        let uu____4418 = p_binders true bs  in
        let uu____4419 =
          let uu____4420 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4420  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4417 uu____4418 uu____4419

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
          let uu____4430 =
            let uu____4431 =
              let uu____4432 =
                let uu____4433 = p_uident uid  in
                let uu____4434 = p_binders true bs  in
                let uu____4435 =
                  let uu____4436 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4436  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4433 uu____4434 uu____4435
                 in
              FStar_Pprint.group uu____4432  in
            let uu____4437 =
              let uu____4438 = str "with"  in
              let uu____4439 =
                let uu____4440 =
                  let uu____4441 =
                    let uu____4442 =
                      let uu____4443 =
                        let uu____4444 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4444
                         in
                      separate_map_last uu____4443 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4442  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4441  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4440  in
              FStar_Pprint.op_Hat_Hat uu____4438 uu____4439  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4431 uu____4437  in
          braces_with_nesting uu____4430

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
          let uu____4475 =
            let uu____4476 = p_lident lid  in
            let uu____4477 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4476 uu____4477  in
          let uu____4478 = p_simpleTerm ps false e  in
          prefix2 uu____4475 uu____4478
      | uu____4479 ->
          let uu____4480 =
            let uu____4481 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4481
             in
          failwith uu____4480

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4543 =
        match uu____4543 with
        | (kwd,t) ->
            let uu____4550 =
              let uu____4551 = str kwd  in
              let uu____4552 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4551 uu____4552  in
            let uu____4553 = p_simpleTerm ps false t  in
            prefix2 uu____4550 uu____4553
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4558 =
      let uu____4559 =
        let uu____4560 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4561 =
          let uu____4562 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4562  in
        FStar_Pprint.op_Hat_Hat uu____4560 uu____4561  in
      let uu____4563 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4559 uu____4563  in
    let uu____4564 =
      let uu____4565 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4565  in
    FStar_Pprint.op_Hat_Hat uu____4558 uu____4564

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___111_4566  ->
    match uu___111_4566 with
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
        let uu____4569 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4569 FStar_Pprint.hardline
    | uu____4570 ->
        let uu____4571 =
          let uu____4572 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4572  in
        FStar_Pprint.op_Hat_Hat uu____4571 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___112_4575  ->
    match uu___112_4575 with
    | FStar_Parser_AST.Rec  ->
        let uu____4576 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4576
    | FStar_Parser_AST.Mutable  ->
        let uu____4577 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4577
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___113_4578  ->
    match uu___113_4578 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4580 = str "#["  in
        let uu____4581 =
          let uu____4582 = p_term false false t  in
          let uu____4583 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4582 uu____4583  in
        FStar_Pprint.op_Hat_Hat uu____4580 uu____4581

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4588 =
          let uu____4589 =
            let uu____4590 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4590  in
          FStar_Pprint.separate_map uu____4589 p_tuplePattern pats  in
        FStar_Pprint.group uu____4588
    | uu____4591 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4598 =
          let uu____4599 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4599 p_constructorPattern pats  in
        FStar_Pprint.group uu____4598
    | uu____4600 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4603;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4608 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4609 = p_constructorPattern hd1  in
        let uu____4610 = p_constructorPattern tl1  in
        infix0 uu____4608 uu____4609 uu____4610
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4612;_},pats)
        ->
        let uu____4618 = p_quident uid  in
        let uu____4619 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4618 uu____4619
    | uu____4620 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4636;
               FStar_Parser_AST.blevel = uu____4637;
               FStar_Parser_AST.aqual = uu____4638;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4646 =
               let uu____4647 = p_ident lid  in
               p_refinement aqual uu____4647 t1 phi  in
             soft_parens_with_nesting uu____4646
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4649;
               FStar_Parser_AST.blevel = uu____4650;
               FStar_Parser_AST.aqual = uu____4651;_},phi))
             ->
             let uu____4655 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4655
         | uu____4656 ->
             let uu____4661 =
               let uu____4662 = p_tuplePattern pat  in
               let uu____4663 =
                 let uu____4664 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4664
                  in
               FStar_Pprint.op_Hat_Hat uu____4662 uu____4663  in
             soft_parens_with_nesting uu____4661)
    | FStar_Parser_AST.PatList pats ->
        let uu____4668 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4668 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4685 =
          match uu____4685 with
          | (lid,pat) ->
              let uu____4692 = p_qlident lid  in
              let uu____4693 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4692 uu____4693
           in
        let uu____4694 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4694
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4704 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4705 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4706 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4704 uu____4705 uu____4706
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4715 =
          let uu____4716 =
            let uu____4717 =
              let uu____4718 = FStar_Ident.text_of_id op  in str uu____4718
               in
            let uu____4719 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4717 uu____4719  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4716  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4715
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4727 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4728 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4727 uu____4728
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4730 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4733;
           FStar_Parser_AST.prange = uu____4734;_},uu____4735)
        ->
        let uu____4740 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4740
    | FStar_Parser_AST.PatTuple (uu____4741,false ) ->
        let uu____4746 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4746
    | uu____4747 ->
        let uu____4748 =
          let uu____4749 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4749  in
        failwith uu____4748

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4751;_},uu____4752)
        -> true
    | uu____4757 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4761 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4762 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4761 uu____4762
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4769;
                   FStar_Parser_AST.blevel = uu____4770;
                   FStar_Parser_AST.aqual = uu____4771;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4775 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4775 t1 phi
            | uu____4776 ->
                let t' =
                  let uu____4778 = is_typ_tuple t  in
                  if uu____4778
                  then
                    let uu____4779 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4779
                  else p_tmFormula t  in
                let uu____4781 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4782 =
                  let uu____4783 = p_lident lid  in
                  let uu____4784 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4783 uu____4784  in
                FStar_Pprint.op_Hat_Hat uu____4781 uu____4782
             in
          if is_atomic
          then
            let uu____4785 =
              let uu____4786 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4786  in
            FStar_Pprint.group uu____4785
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4788 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4795;
                  FStar_Parser_AST.blevel = uu____4796;
                  FStar_Parser_AST.aqual = uu____4797;_},phi)
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
              let uu____5359 = str "`%"  in
              let uu____5360 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5359 uu____5360  in
            FStar_Pprint.group uu____5358
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5362;
              FStar_Parser_AST.level = uu____5363;_}
            ->
            let uu____5364 =
              let uu____5365 = str "`@"  in
              let uu____5366 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5365 uu____5366  in
            FStar_Pprint.group uu____5364
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5368 =
              let uu____5369 = str "`#"  in
              let uu____5370 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5369 uu____5370  in
            FStar_Pprint.group uu____5368
        | uu____5371 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___114_5372  ->
    match uu___114_5372 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5384 =
          let uu____5385 = str "[@"  in
          let uu____5386 =
            let uu____5387 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5388 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5387 uu____5388  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5385 uu____5386  in
        FStar_Pprint.group uu____5384

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
                 let uu____5414 =
                   let uu____5415 =
                     let uu____5416 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5416 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5415 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5414 term_doc
             | pats ->
                 let uu____5422 =
                   let uu____5423 =
                     let uu____5424 =
                       let uu____5425 =
                         let uu____5426 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5426
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5425 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5427 = p_trigger trigger  in
                     prefix2 uu____5424 uu____5427  in
                   FStar_Pprint.group uu____5423  in
                 prefix2 uu____5422 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5447 =
                   let uu____5448 =
                     let uu____5449 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5449 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5448 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5447 term_doc
             | pats ->
                 let uu____5455 =
                   let uu____5456 =
                     let uu____5457 =
                       let uu____5458 =
                         let uu____5459 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5459
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5458 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5460 = p_trigger trigger  in
                     prefix2 uu____5457 uu____5460  in
                   FStar_Pprint.group uu____5456  in
                 prefix2 uu____5455 term_doc)
        | uu____5461 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5463 -> str "forall"
    | FStar_Parser_AST.QExists uu____5476 -> str "exists"
    | uu____5489 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___115_5490  ->
    match uu___115_5490 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5502 =
          let uu____5503 =
            let uu____5504 =
              let uu____5505 = str "pattern"  in
              let uu____5506 =
                let uu____5507 =
                  let uu____5508 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5508
                   in
                FStar_Pprint.op_Hat_Hat uu____5507 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5505 uu____5506  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5504  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5503  in
        FStar_Pprint.group uu____5502

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5514 = str "\\/"  in
    FStar_Pprint.separate_map uu____5514 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5520 =
      let uu____5521 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5521 p_appTerm pats  in
    FStar_Pprint.group uu____5520

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5531 =
              let uu____5532 =
                let uu____5533 = str "fun"  in
                let uu____5534 =
                  let uu____5535 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5535
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5533 uu____5534  in
              let uu____5536 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5532 uu____5536  in
            let uu____5537 = paren_if ps  in uu____5537 uu____5531
        | uu____5542 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5546  ->
      match uu____5546 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5569 =
                    let uu____5570 =
                      let uu____5571 =
                        let uu____5572 = p_tuplePattern p  in
                        let uu____5573 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5572 uu____5573  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5571
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5570  in
                  FStar_Pprint.group uu____5569
              | FStar_Pervasives_Native.Some f ->
                  let uu____5575 =
                    let uu____5576 =
                      let uu____5577 =
                        let uu____5578 =
                          let uu____5579 =
                            let uu____5580 = p_tuplePattern p  in
                            let uu____5581 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5580
                              uu____5581
                             in
                          FStar_Pprint.group uu____5579  in
                        let uu____5582 =
                          let uu____5583 =
                            let uu____5586 = p_tmFormula f  in
                            [uu____5586; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5583  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5578 uu____5582
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5577
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5576  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5575
               in
            let uu____5587 =
              let uu____5588 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5588  in
            FStar_Pprint.group uu____5587  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5597 =
                      let uu____5598 =
                        let uu____5599 =
                          let uu____5600 =
                            let uu____5601 =
                              let uu____5602 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5602  in
                            FStar_Pprint.separate_map uu____5601
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5600
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5599
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5598  in
                    FStar_Pprint.group uu____5597
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5603 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5605;_},e1::e2::[])
        ->
        let uu____5610 = str "<==>"  in
        let uu____5611 = p_tmImplies e1  in
        let uu____5612 = p_tmIff e2  in
        infix0 uu____5610 uu____5611 uu____5612
    | uu____5613 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5615;_},e1::e2::[])
        ->
        let uu____5620 = str "==>"  in
        let uu____5621 = p_tmArrow p_tmFormula e1  in
        let uu____5622 = p_tmImplies e2  in
        infix0 uu____5620 uu____5621 uu____5622
    | uu____5623 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5631 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5631 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5652 ->
               let uu____5653 =
                 let uu____5654 =
                   let uu____5655 =
                     let uu____5656 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656
                      in
                   FStar_Pprint.separate uu____5655 terms  in
                 let uu____5657 =
                   let uu____5658 =
                     let uu____5659 =
                       let uu____5660 =
                         let uu____5661 =
                           let uu____5662 =
                             let uu____5663 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5663
                              in
                           FStar_Pprint.separate uu____5662 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5661 last_op  in
                       let uu____5664 =
                         let uu____5665 =
                           let uu____5666 =
                             let uu____5667 =
                               let uu____5668 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5668
                                in
                             FStar_Pprint.separate uu____5667 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5666 last_op  in
                         jump2 uu____5665  in
                       FStar_Pprint.ifflat uu____5660 uu____5664  in
                     FStar_Pprint.group uu____5659  in
                   let uu____5669 = FStar_List.hd last1  in
                   prefix2 uu____5658 uu____5669  in
                 FStar_Pprint.ifflat uu____5654 uu____5657  in
               FStar_Pprint.group uu____5653)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5682 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5687 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5682 uu____5687
      | uu____5690 -> let uu____5691 = p_Tm e  in [uu____5691]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5694 =
        let uu____5695 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5695 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5694  in
    let disj =
      let uu____5697 =
        let uu____5698 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5698 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5697  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5717;_},e1::e2::[])
        ->
        let uu____5722 = p_tmDisjunction e1  in
        let uu____5727 = let uu____5732 = p_tmConjunction e2  in [uu____5732]
           in
        FStar_List.append uu____5722 uu____5727
    | uu____5741 -> let uu____5742 = p_tmConjunction e  in [uu____5742]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5752;_},e1::e2::[])
        ->
        let uu____5757 = p_tmConjunction e1  in
        let uu____5760 = let uu____5763 = p_tmTuple e2  in [uu____5763]  in
        FStar_List.append uu____5757 uu____5760
    | uu____5764 -> let uu____5765 = p_tmTuple e  in [uu____5765]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5782 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5782
          (fun uu____5790  ->
             match uu____5790 with | (e1,uu____5796) -> p_tmEq e1) args
    | uu____5797 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5802 =
             let uu____5803 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5803  in
           FStar_Pprint.group uu____5802)

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
               (let uu____5820 = FStar_Ident.text_of_id op  in
                uu____5820 = "="))
              ||
              (let uu____5822 = FStar_Ident.text_of_id op  in
               uu____5822 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5824 = levels op1  in
            (match uu____5824 with
             | (left1,mine,right1) ->
                 let uu____5834 =
                   let uu____5835 = FStar_All.pipe_left str op1  in
                   let uu____5836 = p_tmEqWith' p_X left1 e1  in
                   let uu____5837 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5835 uu____5836 uu____5837  in
                 paren_if_gt curr mine uu____5834)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5838;_},e1::e2::[])
            ->
            let uu____5843 =
              let uu____5844 = p_tmEqWith p_X e1  in
              let uu____5845 =
                let uu____5846 =
                  let uu____5847 =
                    let uu____5848 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5848  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5847  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5846  in
              FStar_Pprint.op_Hat_Hat uu____5844 uu____5845  in
            FStar_Pprint.group uu____5843
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5849;_},e1::[])
            ->
            let uu____5853 = levels "-"  in
            (match uu____5853 with
             | (left1,mine,right1) ->
                 let uu____5863 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5863)
        | uu____5864 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5908)::(e2,uu____5910)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5930 = is_list e  in Prims.op_Negation uu____5930)
              ->
              let op = "::"  in
              let uu____5932 = levels op  in
              (match uu____5932 with
               | (left1,mine,right1) ->
                   let uu____5942 =
                     let uu____5943 = str op  in
                     let uu____5944 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5945 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5943 uu____5944 uu____5945  in
                   paren_if_gt curr mine uu____5942)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5953 = levels op  in
              (match uu____5953 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5969 = p_binder false b  in
                     let uu____5970 =
                       let uu____5971 =
                         let uu____5972 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5972 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5971
                        in
                     FStar_Pprint.op_Hat_Hat uu____5969 uu____5970  in
                   let uu____5973 =
                     let uu____5974 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5975 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5974 uu____5975  in
                   paren_if_gt curr mine uu____5973)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5976;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6001 = levels op  in
              (match uu____6001 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6011 = str op  in
                     let uu____6012 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6013 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6011 uu____6012 uu____6013
                   else
                     (let uu____6015 =
                        let uu____6016 = str op  in
                        let uu____6017 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6018 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6016 uu____6017 uu____6018  in
                      paren_if_gt curr mine uu____6015))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6025 = levels op1  in
              (match uu____6025 with
               | (left1,mine,right1) ->
                   let uu____6035 =
                     let uu____6036 = str op1  in
                     let uu____6037 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6038 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6036 uu____6037 uu____6038  in
                   paren_if_gt curr mine uu____6035)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6057 =
                let uu____6058 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6059 =
                  let uu____6060 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6060 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6058 uu____6059  in
              braces_with_nesting uu____6057
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6065;_},e1::[])
              ->
              let uu____6069 =
                let uu____6070 = str "~"  in
                let uu____6071 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6070 uu____6071  in
              FStar_Pprint.group uu____6069
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6073;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6079 = levels op  in
                   (match uu____6079 with
                    | (left1,mine,right1) ->
                        let uu____6089 =
                          let uu____6090 = str op  in
                          let uu____6091 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6092 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6090 uu____6091 uu____6092  in
                        paren_if_gt curr mine uu____6089)
               | uu____6093 -> p_X e)
          | uu____6094 -> p_X e

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
        let uu____6101 =
          let uu____6102 = p_lident lid  in
          let uu____6103 =
            let uu____6104 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6104  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6102 uu____6103  in
        FStar_Pprint.group uu____6101
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6107 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6109 = p_appTerm e  in
    let uu____6110 =
      let uu____6111 =
        let uu____6112 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6112 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6111  in
    FStar_Pprint.op_Hat_Hat uu____6109 uu____6110

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6117 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6117 t phi
      | FStar_Parser_AST.TAnnotated uu____6118 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6123 ->
          let uu____6124 =
            let uu____6125 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6125
             in
          failwith uu____6124
      | FStar_Parser_AST.TVariable uu____6126 ->
          let uu____6127 =
            let uu____6128 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6128
             in
          failwith uu____6127
      | FStar_Parser_AST.NoName uu____6129 ->
          let uu____6130 =
            let uu____6131 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6131
             in
          failwith uu____6130

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6133  ->
      match uu____6133 with
      | (lid,e) ->
          let uu____6140 =
            let uu____6141 = p_qlident lid  in
            let uu____6142 =
              let uu____6143 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6143
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6141 uu____6142  in
          FStar_Pprint.group uu____6140

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6145 when is_general_application e ->
        let uu____6152 = head_and_args e  in
        (match uu____6152 with
         | (head1,args) ->
             let uu____6177 =
               let uu____6188 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6188
               then
                 let uu____6218 =
                   FStar_Util.take
                     (fun uu____6242  ->
                        match uu____6242 with
                        | (uu____6247,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6218 with
                 | (fs_typ_args,args1) ->
                     let uu____6285 =
                       let uu____6286 = p_indexingTerm head1  in
                       let uu____6287 =
                         let uu____6288 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6288 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6286 uu____6287  in
                     (uu____6285, args1)
               else
                 (let uu____6300 = p_indexingTerm head1  in
                  (uu____6300, args))
                in
             (match uu____6177 with
              | (head_doc,args1) ->
                  let uu____6321 =
                    let uu____6322 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6322 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6321))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6342 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6342)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6360 =
               let uu____6361 = p_quident lid  in
               let uu____6362 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6361 uu____6362  in
             FStar_Pprint.group uu____6360
         | hd1::tl1 ->
             let uu____6379 =
               let uu____6380 =
                 let uu____6381 =
                   let uu____6382 = p_quident lid  in
                   let uu____6383 = p_argTerm hd1  in
                   prefix2 uu____6382 uu____6383  in
                 FStar_Pprint.group uu____6381  in
               let uu____6384 =
                 let uu____6385 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6385  in
               FStar_Pprint.op_Hat_Hat uu____6380 uu____6384  in
             FStar_Pprint.group uu____6379)
    | uu____6390 -> p_indexingTerm e

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
         (let uu____6399 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6399 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6401 = str "#"  in
        let uu____6402 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6401 uu____6402
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6405 = str "#["  in
        let uu____6406 =
          let uu____6407 = p_indexingTerm t  in
          let uu____6408 =
            let uu____6409 = str "]"  in
            let uu____6410 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6409 uu____6410  in
          FStar_Pprint.op_Hat_Hat uu____6407 uu____6408  in
        FStar_Pprint.op_Hat_Hat uu____6405 uu____6406
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6412  ->
    match uu____6412 with | (e,uu____6418) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6423;_},e1::e2::[])
          ->
          let uu____6428 =
            let uu____6429 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6430 =
              let uu____6431 =
                let uu____6432 = p_term false false e2  in
                soft_parens_with_nesting uu____6432  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6431  in
            FStar_Pprint.op_Hat_Hat uu____6429 uu____6430  in
          FStar_Pprint.group uu____6428
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6433;_},e1::e2::[])
          ->
          let uu____6438 =
            let uu____6439 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6440 =
              let uu____6441 =
                let uu____6442 = p_term false false e2  in
                soft_brackets_with_nesting uu____6442  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6441  in
            FStar_Pprint.op_Hat_Hat uu____6439 uu____6440  in
          FStar_Pprint.group uu____6438
      | uu____6443 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6448 = p_quident lid  in
        let uu____6449 =
          let uu____6450 =
            let uu____6451 = p_term false false e1  in
            soft_parens_with_nesting uu____6451  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6450  in
        FStar_Pprint.op_Hat_Hat uu____6448 uu____6449
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6457 =
          let uu____6458 = FStar_Ident.text_of_id op  in str uu____6458  in
        let uu____6459 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6457 uu____6459
    | uu____6460 -> p_atomicTermNotQUident e

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
         | uu____6469 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6476 =
          let uu____6477 = FStar_Ident.text_of_id op  in str uu____6477  in
        let uu____6478 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6476 uu____6478
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6482 =
          let uu____6483 =
            let uu____6484 =
              let uu____6485 = FStar_Ident.text_of_id op  in str uu____6485
               in
            let uu____6486 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6484 uu____6486  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6483  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6482
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6501 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6502 =
          let uu____6503 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6504 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6503 p_tmEq uu____6504  in
        let uu____6511 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6501 uu____6502 uu____6511
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6514 =
          let uu____6515 = p_atomicTermNotQUident e1  in
          let uu____6516 =
            let uu____6517 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6517  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6515 uu____6516
           in
        FStar_Pprint.group uu____6514
    | uu____6518 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6523 = p_quident constr_lid  in
        let uu____6524 =
          let uu____6525 =
            let uu____6526 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6526  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6525  in
        FStar_Pprint.op_Hat_Hat uu____6523 uu____6524
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6528 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6528 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6530 = p_term false false e1  in
        soft_parens_with_nesting uu____6530
    | uu____6531 when is_array e ->
        let es = extract_from_list e  in
        let uu____6535 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6536 =
          let uu____6537 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6537
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6535 uu____6536 uu____6540
    | uu____6541 when is_list e ->
        let uu____6542 =
          let uu____6543 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6544 = extract_from_list e  in
          separate_map_or_flow_last uu____6543
            (fun ps  -> p_noSeqTerm ps false) uu____6544
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6542 FStar_Pprint.rbracket
    | uu____6549 when is_lex_list e ->
        let uu____6550 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6551 =
          let uu____6552 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6553 = extract_from_list e  in
          separate_map_or_flow_last uu____6552
            (fun ps  -> p_noSeqTerm ps false) uu____6553
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6550 uu____6551 FStar_Pprint.rbracket
    | uu____6558 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6562 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6563 =
          let uu____6564 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6564 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6562 uu____6563 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6568 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6569 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6568 uu____6569
    | FStar_Parser_AST.Op (op,args) when
        let uu____6576 = handleable_op op args  in
        Prims.op_Negation uu____6576 ->
        let uu____6577 =
          let uu____6578 =
            let uu____6579 = FStar_Ident.text_of_id op  in
            let uu____6580 =
              let uu____6581 =
                let uu____6582 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6582
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6581  in
            Prims.strcat uu____6579 uu____6580  in
          Prims.strcat "Operation " uu____6578  in
        failwith uu____6577
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6584 = str "u#"  in
        let uu____6585 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6584 uu____6585
    | FStar_Parser_AST.Wild  ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586
    | FStar_Parser_AST.Const uu____6587 ->
        let uu____6588 = p_term false false e  in
        soft_parens_with_nesting uu____6588
    | FStar_Parser_AST.Op uu____6589 ->
        let uu____6596 = p_term false false e  in
        soft_parens_with_nesting uu____6596
    | FStar_Parser_AST.Tvar uu____6597 ->
        let uu____6598 = p_term false false e  in
        soft_parens_with_nesting uu____6598
    | FStar_Parser_AST.Var uu____6599 ->
        let uu____6600 = p_term false false e  in
        soft_parens_with_nesting uu____6600
    | FStar_Parser_AST.Name uu____6601 ->
        let uu____6602 = p_term false false e  in
        soft_parens_with_nesting uu____6602
    | FStar_Parser_AST.Construct uu____6603 ->
        let uu____6614 = p_term false false e  in
        soft_parens_with_nesting uu____6614
    | FStar_Parser_AST.Abs uu____6615 ->
        let uu____6622 = p_term false false e  in
        soft_parens_with_nesting uu____6622
    | FStar_Parser_AST.App uu____6623 ->
        let uu____6630 = p_term false false e  in
        soft_parens_with_nesting uu____6630
    | FStar_Parser_AST.Let uu____6631 ->
        let uu____6652 = p_term false false e  in
        soft_parens_with_nesting uu____6652
    | FStar_Parser_AST.LetOpen uu____6653 ->
        let uu____6658 = p_term false false e  in
        soft_parens_with_nesting uu____6658
    | FStar_Parser_AST.Seq uu____6659 ->
        let uu____6664 = p_term false false e  in
        soft_parens_with_nesting uu____6664
    | FStar_Parser_AST.Bind uu____6665 ->
        let uu____6672 = p_term false false e  in
        soft_parens_with_nesting uu____6672
    | FStar_Parser_AST.If uu____6673 ->
        let uu____6680 = p_term false false e  in
        soft_parens_with_nesting uu____6680
    | FStar_Parser_AST.Match uu____6681 ->
        let uu____6696 = p_term false false e  in
        soft_parens_with_nesting uu____6696
    | FStar_Parser_AST.TryWith uu____6697 ->
        let uu____6712 = p_term false false e  in
        soft_parens_with_nesting uu____6712
    | FStar_Parser_AST.Ascribed uu____6713 ->
        let uu____6722 = p_term false false e  in
        soft_parens_with_nesting uu____6722
    | FStar_Parser_AST.Record uu____6723 ->
        let uu____6736 = p_term false false e  in
        soft_parens_with_nesting uu____6736
    | FStar_Parser_AST.Project uu____6737 ->
        let uu____6742 = p_term false false e  in
        soft_parens_with_nesting uu____6742
    | FStar_Parser_AST.Product uu____6743 ->
        let uu____6750 = p_term false false e  in
        soft_parens_with_nesting uu____6750
    | FStar_Parser_AST.Sum uu____6751 ->
        let uu____6758 = p_term false false e  in
        soft_parens_with_nesting uu____6758
    | FStar_Parser_AST.QForall uu____6759 ->
        let uu____6772 = p_term false false e  in
        soft_parens_with_nesting uu____6772
    | FStar_Parser_AST.QExists uu____6773 ->
        let uu____6786 = p_term false false e  in
        soft_parens_with_nesting uu____6786
    | FStar_Parser_AST.Refine uu____6787 ->
        let uu____6792 = p_term false false e  in
        soft_parens_with_nesting uu____6792
    | FStar_Parser_AST.NamedTyp uu____6793 ->
        let uu____6798 = p_term false false e  in
        soft_parens_with_nesting uu____6798
    | FStar_Parser_AST.Requires uu____6799 ->
        let uu____6806 = p_term false false e  in
        soft_parens_with_nesting uu____6806
    | FStar_Parser_AST.Ensures uu____6807 ->
        let uu____6814 = p_term false false e  in
        soft_parens_with_nesting uu____6814
    | FStar_Parser_AST.Attributes uu____6815 ->
        let uu____6818 = p_term false false e  in
        soft_parens_with_nesting uu____6818
    | FStar_Parser_AST.Quote uu____6819 ->
        let uu____6824 = p_term false false e  in
        soft_parens_with_nesting uu____6824
    | FStar_Parser_AST.VQuote uu____6825 ->
        let uu____6826 = p_term false false e  in
        soft_parens_with_nesting uu____6826
    | FStar_Parser_AST.Antiquote uu____6827 ->
        let uu____6828 = p_term false false e  in
        soft_parens_with_nesting uu____6828

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___118_6829  ->
    match uu___118_6829 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6835) ->
        let uu____6836 = str s  in FStar_Pprint.dquotes uu____6836
    | FStar_Const.Const_bytearray (bytes,uu____6838) ->
        let uu____6845 =
          let uu____6846 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6846  in
        let uu____6847 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6845 uu____6847
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___116_6867 =
          match uu___116_6867 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___117_6873 =
          match uu___117_6873 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6884  ->
               match uu____6884 with
               | (s,w) ->
                   let uu____6891 = signedness s  in
                   let uu____6892 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6891 uu____6892)
            sign_width_opt
           in
        let uu____6893 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6893 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6895 = FStar_Range.string_of_range r  in str uu____6895
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6897 = p_quident lid  in
        let uu____6898 =
          let uu____6899 =
            let uu____6900 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6900  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6899  in
        FStar_Pprint.op_Hat_Hat uu____6897 uu____6898

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6902 = str "u#"  in
    let uu____6903 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6902 uu____6903

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6905;_},u1::u2::[])
        ->
        let uu____6910 =
          let uu____6911 = p_universeFrom u1  in
          let uu____6912 =
            let uu____6913 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6913  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6911 uu____6912  in
        FStar_Pprint.group uu____6910
    | FStar_Parser_AST.App uu____6914 ->
        let uu____6921 = head_and_args u  in
        (match uu____6921 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6947 =
                    let uu____6948 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6949 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6957  ->
                           match uu____6957 with
                           | (u1,uu____6963) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6948 uu____6949  in
                  FStar_Pprint.group uu____6947
              | uu____6964 ->
                  let uu____6965 =
                    let uu____6966 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6966
                     in
                  failwith uu____6965))
    | uu____6967 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6990 = FStar_Ident.text_of_id id1  in str uu____6990
    | FStar_Parser_AST.Paren u1 ->
        let uu____6992 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6992
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6993;_},uu____6994::uu____6995::[])
        ->
        let uu____6998 = p_universeFrom u  in
        soft_parens_with_nesting uu____6998
    | FStar_Parser_AST.App uu____6999 ->
        let uu____7006 = p_universeFrom u  in
        soft_parens_with_nesting uu____7006
    | uu____7007 ->
        let uu____7008 =
          let uu____7009 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7009
           in
        failwith uu____7008

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
       | FStar_Parser_AST.Module (uu____7081,decls) ->
           let uu____7087 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7087
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7096,decls,uu____7098) ->
           let uu____7103 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7103
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7156  ->
         match uu____7156 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7172)) -> false
      | ([],uu____7175) -> false
      | uu____7178 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc)
    }
  
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
                      (Prims.parse_int "1") uu____7363 dummy_meta
                      FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7459 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7459, comments1))))))
  