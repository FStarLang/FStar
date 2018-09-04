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
  fun uu___105_1242  ->
    match uu___105_1242 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___106_1267  ->
      match uu___106_1267 with
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
  let levels_from_associativity l uu___107_1454 =
    match uu___107_1454 with
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
                     if lnum2 = (Prims.parse_int "2")
                     then lnum2 - fsdoc_correction
                     else lnum2  in
                   let lnum4 =
                     if meta_decl.has_qs && meta_decl.has_attrs
                     then (Prims.parse_int "3")
                     else lnum3  in
                   let uu____2418 =
                     FStar_Pprint.repeat lnum4 FStar_Pprint.hardline  in
                   FStar_Pprint.op_Hat_Hat doc1 uu____2418)
  
let separate_map_with_comments :
  'Auu____2431 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2431 -> FStar_Pprint.document) ->
          'Auu____2431 Prims.list ->
            ('Auu____2431 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2488 x =
              match uu____2488 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2503 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2503 meta_decl doc1
                     in
                  let uu____2504 =
                    let uu____2505 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2505  in
                  let uu____2506 =
                    let uu____2507 =
                      let uu____2508 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2508  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2507  in
                  (uu____2504, uu____2506)
               in
            let uu____2509 =
              let uu____2516 = FStar_List.hd xs  in
              let uu____2517 = FStar_List.tl xs  in (uu____2516, uu____2517)
               in
            match uu____2509 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2534 =
                    let uu____2535 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2535  in
                  let uu____2536 =
                    let uu____2537 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2537  in
                  (uu____2534, uu____2536)  in
                let uu____2538 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2538
  
let separate_map_with_comments_kw :
  'Auu____2561 'Auu____2562 .
    'Auu____2561 ->
      'Auu____2561 ->
        ('Auu____2561 -> 'Auu____2562 -> FStar_Pprint.document) ->
          'Auu____2562 Prims.list ->
            ('Auu____2562 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2624 x =
              match uu____2624 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2639 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2639 meta_decl doc1
                     in
                  let uu____2640 =
                    let uu____2641 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2641  in
                  let uu____2642 =
                    let uu____2643 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2643  in
                  (uu____2640, uu____2642)
               in
            let uu____2644 =
              let uu____2651 = FStar_List.hd xs  in
              let uu____2652 = FStar_List.tl xs  in (uu____2651, uu____2652)
               in
            match uu____2644 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2669 =
                    let uu____2670 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2670  in
                  let uu____2671 = f prefix1 x  in (uu____2669, uu____2671)
                   in
                let uu____2672 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2672
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3388)) ->
          let uu____3391 =
            let uu____3392 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3392 FStar_Util.is_upper  in
          if uu____3391
          then
            let uu____3395 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3395 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3397 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3404 =
      FStar_Pprint.optional
        (fun d1  ->
           let uu____3408 = p_fsdoc d1  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3408)
        d.FStar_Parser_AST.doc
       in
    let uu____3409 =
      let uu____3410 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3411 =
        let uu____3412 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3412  in
      FStar_Pprint.op_Hat_Hat uu____3410 uu____3411  in
    FStar_Pprint.op_Hat_Hat uu____3404 uu____3409

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3414 ->
        let uu____3415 =
          let uu____3416 = str "@ "  in
          let uu____3417 =
            let uu____3418 =
              let uu____3419 =
                let uu____3420 =
                  let uu____3421 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3421  in
                FStar_Pprint.op_Hat_Hat uu____3420 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3419  in
            FStar_Pprint.op_Hat_Hat uu____3418 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3416 uu____3417  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3415

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3424  ->
    match uu____3424 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3460 =
                match uu____3460 with
                | (kwd,arg) ->
                    let uu____3467 = str "@"  in
                    let uu____3468 =
                      let uu____3469 = str kwd  in
                      let uu____3470 =
                        let uu____3471 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3471
                         in
                      FStar_Pprint.op_Hat_Hat uu____3469 uu____3470  in
                    FStar_Pprint.op_Hat_Hat uu____3467 uu____3468
                 in
              let uu____3472 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____3472 FStar_Pprint.hardline
           in
        let uu____3477 =
          let uu____3478 =
            let uu____3479 =
              let uu____3480 = str doc1  in
              let uu____3481 =
                let uu____3482 =
                  let uu____3483 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3483  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3482  in
              FStar_Pprint.op_Hat_Hat uu____3480 uu____3481  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3479  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3478  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3477

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3487 =
          let uu____3488 = str "val"  in
          let uu____3489 =
            let uu____3490 =
              let uu____3491 = p_lident lid  in
              let uu____3492 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3491 uu____3492  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3490  in
          FStar_Pprint.op_Hat_Hat uu____3488 uu____3489  in
        let uu____3493 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3487 uu____3493
    | FStar_Parser_AST.TopLevelLet (uu____3494,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3519 =
               let uu____3520 = str "let"  in p_letlhs uu____3520 lb  in
             FStar_Pprint.group uu____3519) lbs
    | uu____3521 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___108_3536 =
          match uu___108_3536 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3544 = f x  in
              let uu____3545 =
                let uu____3546 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3546  in
              FStar_Pprint.op_Hat_Hat uu____3544 uu____3545
           in
        let uu____3547 = str "["  in
        let uu____3548 =
          let uu____3549 = p_list' l  in
          let uu____3550 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3549 uu____3550  in
        FStar_Pprint.op_Hat_Hat uu____3547 uu____3548

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3553 =
          let uu____3554 = str "open"  in
          let uu____3555 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3554 uu____3555  in
        FStar_Pprint.group uu____3553
    | FStar_Parser_AST.Include uid ->
        let uu____3557 =
          let uu____3558 = str "include"  in
          let uu____3559 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3558 uu____3559  in
        FStar_Pprint.group uu____3557
    | FStar_Parser_AST.Friend uid ->
        let uu____3561 =
          let uu____3562 = str "friend"  in
          let uu____3563 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3562 uu____3563  in
        FStar_Pprint.group uu____3561
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3566 =
          let uu____3567 = str "module"  in
          let uu____3568 =
            let uu____3569 =
              let uu____3570 = p_uident uid1  in
              let uu____3571 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3570 uu____3571  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3569  in
          FStar_Pprint.op_Hat_Hat uu____3567 uu____3568  in
        let uu____3572 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3566 uu____3572
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3574 =
          let uu____3575 = str "module"  in
          let uu____3576 =
            let uu____3577 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3577  in
          FStar_Pprint.op_Hat_Hat uu____3575 uu____3576  in
        FStar_Pprint.group uu____3574
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3578,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3611 = str "effect"  in
          let uu____3612 =
            let uu____3613 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3613  in
          FStar_Pprint.op_Hat_Hat uu____3611 uu____3612  in
        let uu____3614 =
          let uu____3615 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3615 FStar_Pprint.equals
           in
        let uu____3616 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3614 uu____3616
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3637 =
          let uu____3638 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3638  in
        let uu____3651 =
          let uu____3652 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3690 =
                    let uu____3691 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3691 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3690)) uu____3652
           in
        FStar_Pprint.op_Hat_Hat uu____3637 uu____3651
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3707 = str "let"  in
          let uu____3708 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3707 uu____3708  in
        let uu____3709 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3709 p_letbinding lbs
          (fun uu____3718  ->
             match uu____3718 with
             | (p,t) ->
                 let uu____3725 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____3725;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc)
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3728 = str "val"  in
        let uu____3729 =
          let uu____3730 =
            let uu____3731 = p_lident lid  in
            let uu____3732 =
              let uu____3733 =
                let uu____3734 =
                  let uu____3735 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3735  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3734  in
              FStar_Pprint.group uu____3733  in
            FStar_Pprint.op_Hat_Hat uu____3731 uu____3732  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3730  in
        FStar_Pprint.op_Hat_Hat uu____3728 uu____3729
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3739 =
            let uu____3740 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3740 FStar_Util.is_upper  in
          if uu____3739
          then FStar_Pprint.empty
          else
            (let uu____3744 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3744 FStar_Pprint.space)
           in
        let uu____3745 =
          let uu____3746 = p_ident id1  in
          let uu____3747 =
            let uu____3748 =
              let uu____3749 =
                let uu____3750 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3750  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3749  in
            FStar_Pprint.group uu____3748  in
          FStar_Pprint.op_Hat_Hat uu____3746 uu____3747  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3745
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3757 = str "exception"  in
        let uu____3758 =
          let uu____3759 =
            let uu____3760 = p_uident uid  in
            let uu____3761 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3765 =
                     let uu____3766 = str "of"  in
                     let uu____3767 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3766 uu____3767  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3765) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3760 uu____3761  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3759  in
        FStar_Pprint.op_Hat_Hat uu____3757 uu____3758
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3769 = str "new_effect"  in
        let uu____3770 =
          let uu____3771 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3771  in
        FStar_Pprint.op_Hat_Hat uu____3769 uu____3770
    | FStar_Parser_AST.SubEffect se ->
        let uu____3773 = str "sub_effect"  in
        let uu____3774 =
          let uu____3775 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3775  in
        FStar_Pprint.op_Hat_Hat uu____3773 uu____3774
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3778 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3778 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3779 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3780,uu____3781) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3804 = str "%splice"  in
        let uu____3805 =
          let uu____3806 =
            let uu____3807 = str ";"  in p_list p_uident uu____3807 ids  in
          let uu____3808 =
            let uu____3809 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3809  in
          FStar_Pprint.op_Hat_Hat uu____3806 uu____3808  in
        FStar_Pprint.op_Hat_Hat uu____3804 uu____3805

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___109_3810  ->
    match uu___109_3810 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3812 = str "#set-options"  in
        let uu____3813 =
          let uu____3814 =
            let uu____3815 = str s  in FStar_Pprint.dquotes uu____3815  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3814  in
        FStar_Pprint.op_Hat_Hat uu____3812 uu____3813
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3819 = str "#reset-options"  in
        let uu____3820 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3824 =
                 let uu____3825 = str s  in FStar_Pprint.dquotes uu____3825
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3824) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3819 uu____3820
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3829 = str "#push-options"  in
        let uu____3830 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3834 =
                 let uu____3835 = str s  in FStar_Pprint.dquotes uu____3835
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3834) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3829 uu____3830
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
    fun uu____3860  ->
      match uu____3860 with
      | (typedecl,fsdoc_opt) ->
          let uu____3873 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3873 with
           | (decl,body) ->
               let uu____3891 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3891)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___110_3893  ->
      match uu___110_3893 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3923 = FStar_Pprint.empty  in
          let uu____3924 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3924, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3945 =
            let uu____3946 = p_typ false false t  in jump2 uu____3946  in
          let uu____3947 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3947, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4001 =
            match uu____4001 with
            | (lid1,t,doc_opt) ->
                let uu____4017 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4017
             in
          let p_fields uu____4033 =
            let uu____4034 =
              let uu____4035 =
                let uu____4036 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4036 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4035  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4034  in
          let uu____4045 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4045, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4106 =
            match uu____4106 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4132 =
                    let uu____4133 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4133  in
                  FStar_Range.extend_to_end_of_line uu____4132  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4159 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4172 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4172,
            ((fun uu____4178  ->
                let uu____4179 = datacon_doc ()  in jump2 uu____4179)))

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
  fun uu____4180  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4180 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4214 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4214  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4216 =
                        let uu____4219 =
                          let uu____4222 = p_fsdoc fsdoc  in
                          let uu____4223 =
                            let uu____4226 = cont lid_doc  in [uu____4226]
                             in
                          uu____4222 :: uu____4223  in
                        kw :: uu____4219  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4216
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4231 =
                        let uu____4232 =
                          let uu____4233 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4233 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4232
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4231
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4248 =
                          let uu____4249 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4249  in
                        prefix2 uu____4248 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4251  ->
      match uu____4251 with
      | (lid,t,doc_opt) ->
          let uu____4267 =
            let uu____4268 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4269 =
              let uu____4270 = p_lident lid  in
              let uu____4271 =
                let uu____4272 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4272  in
              FStar_Pprint.op_Hat_Hat uu____4270 uu____4271  in
            FStar_Pprint.op_Hat_Hat uu____4268 uu____4269  in
          FStar_Pprint.group uu____4267

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4273  ->
    match uu____4273 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4301 =
            let uu____4302 =
              let uu____4303 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4303  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4302  in
          FStar_Pprint.group uu____4301  in
        let uu____4304 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4305 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4309 =
                 let uu____4310 =
                   let uu____4311 =
                     let uu____4312 =
                       let uu____4313 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4313
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4312  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4311  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4310  in
               FStar_Pprint.group uu____4309) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4304 uu____4305

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4315  ->
      match uu____4315 with
      | (pat,uu____4321) ->
          let uu____4322 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4341 =
                  let uu____4342 =
                    let uu____4343 =
                      let uu____4344 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4344
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4343  in
                  FStar_Pprint.group uu____4342  in
                (pat1, uu____4341)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4356 =
                  let uu____4357 =
                    let uu____4358 =
                      let uu____4359 =
                        let uu____4360 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4360
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4359
                       in
                    FStar_Pprint.group uu____4358  in
                  let uu____4361 =
                    let uu____4362 =
                      let uu____4363 = str "by"  in
                      let uu____4364 =
                        let uu____4365 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4365
                         in
                      FStar_Pprint.op_Hat_Hat uu____4363 uu____4364  in
                    FStar_Pprint.group uu____4362  in
                  FStar_Pprint.op_Hat_Hat uu____4357 uu____4361  in
                (pat1, uu____4356)
            | uu____4366 -> (pat, FStar_Pprint.empty)  in
          (match uu____4322 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4370);
                       FStar_Parser_AST.prange = uu____4371;_},pats)
                    ->
                    let uu____4381 =
                      let uu____4382 =
                        let uu____4383 =
                          let uu____4384 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4384  in
                        FStar_Pprint.group uu____4383  in
                      let uu____4385 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4382 uu____4385  in
                    prefix2_nonempty uu____4381 ascr_doc
                | uu____4386 ->
                    let uu____4387 =
                      let uu____4388 =
                        let uu____4389 =
                          let uu____4390 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4390  in
                        FStar_Pprint.group uu____4389  in
                      FStar_Pprint.op_Hat_Hat uu____4388 ascr_doc  in
                    FStar_Pprint.group uu____4387))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4392  ->
      match uu____4392 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4401 =
            let uu____4402 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4402  in
          let uu____4403 =
            let uu____4404 =
              let uu____4405 =
                let uu____4406 =
                  let uu____4407 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4407  in
                FStar_Pprint.group uu____4406  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4405  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4404  in
          FStar_Pprint.ifflat uu____4401 uu____4403

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___111_4408  ->
    match uu___111_4408 with
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
        let uu____4433 = p_uident uid  in
        let uu____4434 = p_binders true bs  in
        let uu____4435 =
          let uu____4436 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4436  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4433 uu____4434 uu____4435

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
          let uu____4446 =
            let uu____4447 =
              let uu____4448 =
                let uu____4449 = p_uident uid  in
                let uu____4450 = p_binders true bs  in
                let uu____4451 =
                  let uu____4452 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4452  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4449 uu____4450 uu____4451
                 in
              FStar_Pprint.group uu____4448  in
            let uu____4453 =
              let uu____4454 = str "with"  in
              let uu____4455 =
                let uu____4456 =
                  let uu____4457 =
                    let uu____4458 =
                      let uu____4459 =
                        let uu____4460 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4460
                         in
                      separate_map_last uu____4459 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4458  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4457  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4456  in
              FStar_Pprint.op_Hat_Hat uu____4454 uu____4455  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4447 uu____4453  in
          braces_with_nesting uu____4446

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4463,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4492 =
            let uu____4493 = p_lident lid  in
            let uu____4494 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4493 uu____4494  in
          let uu____4495 = p_simpleTerm ps false e  in
          prefix2 uu____4492 uu____4495
      | uu____4496 ->
          let uu____4497 =
            let uu____4498 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4498
             in
          failwith uu____4497

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4560 =
        match uu____4560 with
        | (kwd,t) ->
            let uu____4567 =
              let uu____4568 = str kwd  in
              let uu____4569 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4568 uu____4569  in
            let uu____4570 = p_simpleTerm ps false t  in
            prefix2 uu____4567 uu____4570
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4575 =
      let uu____4576 =
        let uu____4577 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4578 =
          let uu____4579 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4579  in
        FStar_Pprint.op_Hat_Hat uu____4577 uu____4578  in
      let uu____4580 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4576 uu____4580  in
    let uu____4581 =
      let uu____4582 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4582  in
    FStar_Pprint.op_Hat_Hat uu____4575 uu____4581

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___112_4583  ->
    match uu___112_4583 with
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
        let uu____4586 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4586 FStar_Pprint.hardline
    | uu____4587 ->
        let uu____4588 =
          let uu____4589 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4589  in
        FStar_Pprint.op_Hat_Hat uu____4588 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___113_4592  ->
    match uu___113_4592 with
    | FStar_Parser_AST.Rec  ->
        let uu____4593 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4593
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___114_4594  ->
    match uu___114_4594 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____4596,e) ->
             let uu____4602 = str "#["  in
             let uu____4603 =
               let uu____4604 = p_term false false e  in
               let uu____4605 =
                 let uu____4606 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____4606 break1  in
               FStar_Pprint.op_Hat_Hat uu____4604 uu____4605  in
             FStar_Pprint.op_Hat_Hat uu____4602 uu____4603
         | uu____4607 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4612 =
          let uu____4613 =
            let uu____4614 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4614  in
          FStar_Pprint.separate_map uu____4613 p_tuplePattern pats  in
        FStar_Pprint.group uu____4612
    | uu____4615 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4622 =
          let uu____4623 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4623 p_constructorPattern pats  in
        FStar_Pprint.group uu____4622
    | uu____4624 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4627;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4632 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4633 = p_constructorPattern hd1  in
        let uu____4634 = p_constructorPattern tl1  in
        infix0 uu____4632 uu____4633 uu____4634
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4636;_},pats)
        ->
        let uu____4642 = p_quident uid  in
        let uu____4643 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4642 uu____4643
    | uu____4644 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4660;
               FStar_Parser_AST.blevel = uu____4661;
               FStar_Parser_AST.aqual = uu____4662;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4670 =
               let uu____4671 = p_ident lid  in
               p_refinement aqual uu____4671 t1 phi  in
             soft_parens_with_nesting uu____4670
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4674;
               FStar_Parser_AST.blevel = uu____4675;
               FStar_Parser_AST.aqual = uu____4676;_},phi))
             ->
             let uu____4682 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4682
         | uu____4683 ->
             let uu____4688 =
               let uu____4689 = p_tuplePattern pat  in
               let uu____4690 =
                 let uu____4691 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4691
                  in
               FStar_Pprint.op_Hat_Hat uu____4689 uu____4690  in
             soft_parens_with_nesting uu____4688)
    | FStar_Parser_AST.PatList pats ->
        let uu____4695 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4695 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4712 =
          match uu____4712 with
          | (lid,pat) ->
              let uu____4719 = p_qlident lid  in
              let uu____4720 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4719 uu____4720
           in
        let uu____4721 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4721
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4731 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4732 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4733 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4731 uu____4732 uu____4733
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4742 =
          let uu____4743 =
            let uu____4744 =
              let uu____4745 = FStar_Ident.text_of_id op  in str uu____4745
               in
            let uu____4746 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4744 uu____4746  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4743  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4742
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4750 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4750 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4758 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4759 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4758 uu____4759
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4761 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4764;
           FStar_Parser_AST.prange = uu____4765;_},uu____4766)
        ->
        let uu____4771 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4771
    | FStar_Parser_AST.PatTuple (uu____4772,false ) ->
        let uu____4777 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4777
    | uu____4778 ->
        let uu____4779 =
          let uu____4780 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4780  in
        failwith uu____4779

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4782;_},uu____4783)
        -> true
    | uu____4788 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____4792) -> true
    | uu____4793 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4799 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4800 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4799 uu____4800
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4807;
                   FStar_Parser_AST.blevel = uu____4808;
                   FStar_Parser_AST.aqual = uu____4809;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4813 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4813 t1 phi
            | uu____4814 ->
                let t' =
                  let uu____4816 = is_typ_tuple t  in
                  if uu____4816
                  then
                    let uu____4817 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4817
                  else p_tmFormula t  in
                let uu____4819 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4820 =
                  let uu____4821 = p_lident lid  in
                  let uu____4822 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4821 uu____4822  in
                FStar_Pprint.op_Hat_Hat uu____4819 uu____4820
             in
          let uu____4823 =
            is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)  in
          if uu____4823
          then
            let uu____4824 =
              let uu____4825 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4825  in
            FStar_Pprint.group uu____4824
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4827 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4834;
                  FStar_Parser_AST.blevel = uu____4835;
                  FStar_Parser_AST.aqual = uu____4836;_},phi)
               ->
               if is_atomic
               then
                 let uu____4840 =
                   let uu____4841 =
                     let uu____4842 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4842 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4841  in
                 FStar_Pprint.group uu____4840
               else
                 (let uu____4844 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4844)
           | uu____4845 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4854 -> false
            | FStar_Parser_AST.App uu____4865 -> false
            | FStar_Parser_AST.Op uu____4872 -> false
            | uu____4879 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4883 =
            let uu____4884 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4885 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4884 uu____4885  in
          let uu____4886 =
            let uu____4887 = p_appTerm t  in
            let uu____4888 =
              let uu____4889 =
                let uu____4890 =
                  let uu____4891 = soft_braces_with_nesting_tight phi1  in
                  let uu____4892 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4891 uu____4892  in
                FStar_Pprint.group uu____4890  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4889
               in
            FStar_Pprint.op_Hat_Hat uu____4887 uu____4888  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4883 uu____4886

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4903 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4903

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4908 = FStar_Ident.text_of_id lid  in str uu____4908)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4911 = FStar_Ident.text_of_lid lid  in str uu____4911)

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
            let uu____4929 =
              let uu____4930 =
                let uu____4931 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4931 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4930  in
            let uu____4932 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4929 uu____4932
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4936 =
              let uu____4937 =
                let uu____4938 =
                  let uu____4939 = p_lident x  in
                  let uu____4940 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4939 uu____4940  in
                let uu____4941 =
                  let uu____4942 = p_noSeqTerm true false e1  in
                  let uu____4943 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4942 uu____4943  in
                op_Hat_Slash_Plus_Hat uu____4938 uu____4941  in
              FStar_Pprint.group uu____4937  in
            let uu____4944 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4936 uu____4944
        | uu____4945 ->
            let uu____4946 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4946

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
            let uu____4957 =
              let uu____4958 = p_tmIff e1  in
              let uu____4959 =
                let uu____4960 =
                  let uu____4961 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4961
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4960  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4958 uu____4959  in
            FStar_Pprint.group uu____4957
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4967 =
              let uu____4968 = p_tmIff e1  in
              let uu____4969 =
                let uu____4970 =
                  let uu____4971 =
                    let uu____4972 = p_typ false false t  in
                    let uu____4973 =
                      let uu____4974 = str "by"  in
                      let uu____4975 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4974 uu____4975  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4972 uu____4973  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4971
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4970  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4968 uu____4969  in
            FStar_Pprint.group uu____4967
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4976;_},e1::e2::e3::[])
            ->
            let uu____4982 =
              let uu____4983 =
                let uu____4984 =
                  let uu____4985 = p_atomicTermNotQUident e1  in
                  let uu____4986 =
                    let uu____4987 =
                      let uu____4988 =
                        let uu____4989 = p_term false false e2  in
                        soft_parens_with_nesting uu____4989  in
                      let uu____4990 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4988 uu____4990  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4987  in
                  FStar_Pprint.op_Hat_Hat uu____4985 uu____4986  in
                FStar_Pprint.group uu____4984  in
              let uu____4991 =
                let uu____4992 = p_noSeqTerm ps pb e3  in jump2 uu____4992
                 in
              FStar_Pprint.op_Hat_Hat uu____4983 uu____4991  in
            FStar_Pprint.group uu____4982
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4993;_},e1::e2::e3::[])
            ->
            let uu____4999 =
              let uu____5000 =
                let uu____5001 =
                  let uu____5002 = p_atomicTermNotQUident e1  in
                  let uu____5003 =
                    let uu____5004 =
                      let uu____5005 =
                        let uu____5006 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5006  in
                      let uu____5007 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5005 uu____5007  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5004  in
                  FStar_Pprint.op_Hat_Hat uu____5002 uu____5003  in
                FStar_Pprint.group uu____5001  in
              let uu____5008 =
                let uu____5009 = p_noSeqTerm ps pb e3  in jump2 uu____5009
                 in
              FStar_Pprint.op_Hat_Hat uu____5000 uu____5008  in
            FStar_Pprint.group uu____4999
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5017 =
              let uu____5018 = str "requires"  in
              let uu____5019 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5019  in
            FStar_Pprint.group uu____5017
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5027 =
              let uu____5028 = str "ensures"  in
              let uu____5029 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5028 uu____5029  in
            FStar_Pprint.group uu____5027
        | FStar_Parser_AST.Attributes es ->
            let uu____5033 =
              let uu____5034 = str "attributes"  in
              let uu____5035 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5034 uu____5035  in
            FStar_Pprint.group uu____5033
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5039 =
                let uu____5040 =
                  let uu____5041 = str "if"  in
                  let uu____5042 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5041 uu____5042  in
                let uu____5043 =
                  let uu____5044 = str "then"  in
                  let uu____5045 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5044 uu____5045  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5040 uu____5043  in
              FStar_Pprint.group uu____5039
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5048,uu____5049,e31) when
                     is_unit e31 ->
                     let uu____5051 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5051
                 | uu____5052 -> p_noSeqTerm false false e2  in
               let uu____5053 =
                 let uu____5054 =
                   let uu____5055 = str "if"  in
                   let uu____5056 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5055 uu____5056  in
                 let uu____5057 =
                   let uu____5058 =
                     let uu____5059 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5059 e2_doc  in
                   let uu____5060 =
                     let uu____5061 = str "else"  in
                     let uu____5062 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5061 uu____5062  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5058 uu____5060  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5054 uu____5057  in
               FStar_Pprint.group uu____5053)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5085 =
              let uu____5086 =
                let uu____5087 =
                  let uu____5088 = str "try"  in
                  let uu____5089 = p_noSeqTerm false false e1  in
                  prefix2 uu____5088 uu____5089  in
                let uu____5090 =
                  let uu____5091 = str "with"  in
                  let uu____5092 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5091 uu____5092  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5087 uu____5090  in
              FStar_Pprint.group uu____5086  in
            let uu____5101 = paren_if (ps || pb)  in uu____5101 uu____5085
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5128 =
              let uu____5129 =
                let uu____5130 =
                  let uu____5131 = str "match"  in
                  let uu____5132 = p_noSeqTerm false false e1  in
                  let uu____5133 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5131 uu____5132 uu____5133
                   in
                let uu____5134 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5130 uu____5134  in
              FStar_Pprint.group uu____5129  in
            let uu____5143 = paren_if (ps || pb)  in uu____5143 uu____5128
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5150 =
              let uu____5151 =
                let uu____5152 =
                  let uu____5153 = str "let open"  in
                  let uu____5154 = p_quident uid  in
                  let uu____5155 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5153 uu____5154 uu____5155
                   in
                let uu____5156 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5152 uu____5156  in
              FStar_Pprint.group uu____5151  in
            let uu____5157 = paren_if ps  in uu____5157 uu____5150
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5221 is_last =
              match uu____5221 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5254 =
                          let uu____5255 = str "let"  in
                          let uu____5256 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5255 uu____5256
                           in
                        FStar_Pprint.group uu____5254
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5257 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5262 =
                    if is_last
                    then
                      let uu____5263 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5264 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5263 doc_expr uu____5264
                    else
                      (let uu____5266 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5266)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5262
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5312 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5312
                     else
                       (let uu____5320 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5320)) lbs
               in
            let lbs_doc =
              let uu____5328 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5328  in
            let uu____5329 =
              let uu____5330 =
                let uu____5331 =
                  let uu____5332 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5332
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5331  in
              FStar_Pprint.group uu____5330  in
            let uu____5333 = paren_if ps  in uu____5333 uu____5329
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5340;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5343;
                                                             FStar_Parser_AST.level
                                                               = uu____5344;_})
            when matches_var maybe_x x ->
            let uu____5371 =
              let uu____5372 =
                let uu____5373 = str "function"  in
                let uu____5374 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5373 uu____5374  in
              FStar_Pprint.group uu____5372  in
            let uu____5383 = paren_if (ps || pb)  in uu____5383 uu____5371
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5389 =
              let uu____5390 = str "quote"  in
              let uu____5391 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5390 uu____5391  in
            FStar_Pprint.group uu____5389
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5393 =
              let uu____5394 = str "`"  in
              let uu____5395 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5394 uu____5395  in
            FStar_Pprint.group uu____5393
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5397 =
              let uu____5398 = str "`%"  in
              let uu____5399 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5398 uu____5399  in
            FStar_Pprint.group uu____5397
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5401;
              FStar_Parser_AST.level = uu____5402;_}
            ->
            let uu____5403 =
              let uu____5404 = str "`@"  in
              let uu____5405 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5404 uu____5405  in
            FStar_Pprint.group uu____5403
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5407 =
              let uu____5408 = str "`#"  in
              let uu____5409 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5408 uu____5409  in
            FStar_Pprint.group uu____5407
        | uu____5410 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___115_5411  ->
    match uu___115_5411 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5423 =
          let uu____5424 = str "[@"  in
          let uu____5425 =
            let uu____5426 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5427 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5426 uu____5427  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5424 uu____5425  in
        FStar_Pprint.group uu____5423

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
                 let uu____5453 =
                   let uu____5454 =
                     let uu____5455 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5455 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5454 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5453 term_doc
             | pats ->
                 let uu____5461 =
                   let uu____5462 =
                     let uu____5463 =
                       let uu____5464 =
                         let uu____5465 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5465
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5464 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5466 = p_trigger trigger  in
                     prefix2 uu____5463 uu____5466  in
                   FStar_Pprint.group uu____5462  in
                 prefix2 uu____5461 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5486 =
                   let uu____5487 =
                     let uu____5488 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5488 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5487 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5486 term_doc
             | pats ->
                 let uu____5494 =
                   let uu____5495 =
                     let uu____5496 =
                       let uu____5497 =
                         let uu____5498 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5498
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5497 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5499 = p_trigger trigger  in
                     prefix2 uu____5496 uu____5499  in
                   FStar_Pprint.group uu____5495  in
                 prefix2 uu____5494 term_doc)
        | uu____5500 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5502 -> str "forall"
    | FStar_Parser_AST.QExists uu____5515 -> str "exists"
    | uu____5528 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___116_5529  ->
    match uu___116_5529 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5541 =
          let uu____5542 =
            let uu____5543 =
              let uu____5544 = str "pattern"  in
              let uu____5545 =
                let uu____5546 =
                  let uu____5547 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5547
                   in
                FStar_Pprint.op_Hat_Hat uu____5546 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5544 uu____5545  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5543  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5542  in
        FStar_Pprint.group uu____5541

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5553 = str "\\/"  in
    FStar_Pprint.separate_map uu____5553 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5559 =
      let uu____5560 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5560 p_appTerm pats  in
    FStar_Pprint.group uu____5559

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5570 =
              let uu____5571 =
                let uu____5572 = str "fun"  in
                let uu____5573 =
                  let uu____5574 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5574
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5572 uu____5573  in
              let uu____5575 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5571 uu____5575  in
            let uu____5576 = paren_if ps  in uu____5576 uu____5570
        | uu____5581 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5585  ->
      match uu____5585 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5608 =
                    let uu____5609 =
                      let uu____5610 =
                        let uu____5611 = p_tuplePattern p  in
                        let uu____5612 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5611 uu____5612  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5610
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5609  in
                  FStar_Pprint.group uu____5608
              | FStar_Pervasives_Native.Some f ->
                  let uu____5614 =
                    let uu____5615 =
                      let uu____5616 =
                        let uu____5617 =
                          let uu____5618 =
                            let uu____5619 = p_tuplePattern p  in
                            let uu____5620 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5619
                              uu____5620
                             in
                          FStar_Pprint.group uu____5618  in
                        let uu____5621 =
                          let uu____5622 =
                            let uu____5625 = p_tmFormula f  in
                            [uu____5625; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5622  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5617 uu____5621
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5616
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5615  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5614
               in
            let uu____5626 =
              let uu____5627 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5627  in
            FStar_Pprint.group uu____5626  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5636 =
                      let uu____5637 =
                        let uu____5638 =
                          let uu____5639 =
                            let uu____5640 =
                              let uu____5641 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5641  in
                            FStar_Pprint.separate_map uu____5640
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5639
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5638
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5637  in
                    FStar_Pprint.group uu____5636
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5642 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5644;_},e1::e2::[])
        ->
        let uu____5649 = str "<==>"  in
        let uu____5650 = p_tmImplies e1  in
        let uu____5651 = p_tmIff e2  in
        infix0 uu____5649 uu____5650 uu____5651
    | uu____5652 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5654;_},e1::e2::[])
        ->
        let uu____5659 = str "==>"  in
        let uu____5660 = p_tmArrow p_tmFormula e1  in
        let uu____5661 = p_tmImplies e2  in
        infix0 uu____5659 uu____5660 uu____5661
    | uu____5662 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5670 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5670 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5691 ->
               let uu____5692 =
                 let uu____5693 =
                   let uu____5694 =
                     let uu____5695 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5695
                      in
                   FStar_Pprint.separate uu____5694 terms  in
                 let uu____5696 =
                   let uu____5697 =
                     let uu____5698 =
                       let uu____5699 =
                         let uu____5700 =
                           let uu____5701 =
                             let uu____5702 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5702
                              in
                           FStar_Pprint.separate uu____5701 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5700 last_op  in
                       let uu____5703 =
                         let uu____5704 =
                           let uu____5705 =
                             let uu____5706 =
                               let uu____5707 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5707
                                in
                             FStar_Pprint.separate uu____5706 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5705 last_op  in
                         jump2 uu____5704  in
                       FStar_Pprint.ifflat uu____5699 uu____5703  in
                     FStar_Pprint.group uu____5698  in
                   let uu____5708 = FStar_List.hd last1  in
                   prefix2 uu____5697 uu____5708  in
                 FStar_Pprint.ifflat uu____5693 uu____5696  in
               FStar_Pprint.group uu____5692)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5721 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5726 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5721 uu____5726
      | uu____5729 -> let uu____5730 = p_Tm e  in [uu____5730]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5733 =
        let uu____5734 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5734 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5733  in
    let disj =
      let uu____5736 =
        let uu____5737 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5737 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5736  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5756;_},e1::e2::[])
        ->
        let uu____5761 = p_tmDisjunction e1  in
        let uu____5766 = let uu____5771 = p_tmConjunction e2  in [uu____5771]
           in
        FStar_List.append uu____5761 uu____5766
    | uu____5780 -> let uu____5781 = p_tmConjunction e  in [uu____5781]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5791;_},e1::e2::[])
        ->
        let uu____5796 = p_tmConjunction e1  in
        let uu____5799 = let uu____5802 = p_tmTuple e2  in [uu____5802]  in
        FStar_List.append uu____5796 uu____5799
    | uu____5803 -> let uu____5804 = p_tmTuple e  in [uu____5804]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5821 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5821
          (fun uu____5829  ->
             match uu____5829 with | (e1,uu____5835) -> p_tmEq e1) args
    | uu____5836 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5841 =
             let uu____5842 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5842  in
           FStar_Pprint.group uu____5841)

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
               (let uu____5859 = FStar_Ident.text_of_id op  in
                uu____5859 = "="))
              ||
              (let uu____5861 = FStar_Ident.text_of_id op  in
               uu____5861 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5863 = levels op1  in
            (match uu____5863 with
             | (left1,mine,right1) ->
                 let uu____5873 =
                   let uu____5874 = FStar_All.pipe_left str op1  in
                   let uu____5875 = p_tmEqWith' p_X left1 e1  in
                   let uu____5876 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5874 uu____5875 uu____5876  in
                 paren_if_gt curr mine uu____5873)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5877;_},e1::e2::[])
            ->
            let uu____5882 =
              let uu____5883 = p_tmEqWith p_X e1  in
              let uu____5884 =
                let uu____5885 =
                  let uu____5886 =
                    let uu____5887 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5887  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5886  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5885  in
              FStar_Pprint.op_Hat_Hat uu____5883 uu____5884  in
            FStar_Pprint.group uu____5882
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5888;_},e1::[])
            ->
            let uu____5892 = levels "-"  in
            (match uu____5892 with
             | (left1,mine,right1) ->
                 let uu____5902 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5902)
        | uu____5903 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5947)::(e2,uu____5949)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5969 = is_list e  in Prims.op_Negation uu____5969)
              ->
              let op = "::"  in
              let uu____5971 = levels op  in
              (match uu____5971 with
               | (left1,mine,right1) ->
                   let uu____5981 =
                     let uu____5982 = str op  in
                     let uu____5983 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5984 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5982 uu____5983 uu____5984  in
                   paren_if_gt curr mine uu____5981)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5992 = levels op  in
              (match uu____5992 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6008 = p_binder false b  in
                     let uu____6009 =
                       let uu____6010 =
                         let uu____6011 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6011 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6010
                        in
                     FStar_Pprint.op_Hat_Hat uu____6008 uu____6009  in
                   let uu____6012 =
                     let uu____6013 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6014 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6013 uu____6014  in
                   paren_if_gt curr mine uu____6012)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6015;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6040 = levels op  in
              (match uu____6040 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6050 = str op  in
                     let uu____6051 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6052 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6050 uu____6051 uu____6052
                   else
                     (let uu____6054 =
                        let uu____6055 = str op  in
                        let uu____6056 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6057 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6055 uu____6056 uu____6057  in
                      paren_if_gt curr mine uu____6054))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6064 = levels op1  in
              (match uu____6064 with
               | (left1,mine,right1) ->
                   let uu____6074 =
                     let uu____6075 = str op1  in
                     let uu____6076 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6077 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6075 uu____6076 uu____6077  in
                   paren_if_gt curr mine uu____6074)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6096 =
                let uu____6097 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6098 =
                  let uu____6099 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6099 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6097 uu____6098  in
              braces_with_nesting uu____6096
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6104;_},e1::[])
              ->
              let uu____6108 =
                let uu____6109 = str "~"  in
                let uu____6110 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6109 uu____6110  in
              FStar_Pprint.group uu____6108
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6112;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6118 = levels op  in
                   (match uu____6118 with
                    | (left1,mine,right1) ->
                        let uu____6128 =
                          let uu____6129 = str op  in
                          let uu____6130 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6131 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6129 uu____6130 uu____6131  in
                        paren_if_gt curr mine uu____6128)
               | uu____6132 -> p_X e)
          | uu____6133 -> p_X e

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
        let uu____6140 =
          let uu____6141 = p_lident lid  in
          let uu____6142 =
            let uu____6143 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6143  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6141 uu____6142  in
        FStar_Pprint.group uu____6140
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6146 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6148 = p_appTerm e  in
    let uu____6149 =
      let uu____6150 =
        let uu____6151 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6151 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6150  in
    FStar_Pprint.op_Hat_Hat uu____6148 uu____6149

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6156 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6156 t phi
      | FStar_Parser_AST.TAnnotated uu____6157 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6162 ->
          let uu____6163 =
            let uu____6164 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6164
             in
          failwith uu____6163
      | FStar_Parser_AST.TVariable uu____6165 ->
          let uu____6166 =
            let uu____6167 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6167
             in
          failwith uu____6166
      | FStar_Parser_AST.NoName uu____6168 ->
          let uu____6169 =
            let uu____6170 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6170
             in
          failwith uu____6169

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6172  ->
      match uu____6172 with
      | (lid,e) ->
          let uu____6179 =
            let uu____6180 = p_qlident lid  in
            let uu____6181 =
              let uu____6182 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6182
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6180 uu____6181  in
          FStar_Pprint.group uu____6179

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6184 when is_general_application e ->
        let uu____6191 = head_and_args e  in
        (match uu____6191 with
         | (head1,args) ->
             let uu____6216 =
               let uu____6227 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6227
               then
                 let uu____6257 =
                   FStar_Util.take
                     (fun uu____6281  ->
                        match uu____6281 with
                        | (uu____6286,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6257 with
                 | (fs_typ_args,args1) ->
                     let uu____6324 =
                       let uu____6325 = p_indexingTerm head1  in
                       let uu____6326 =
                         let uu____6327 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6327 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6325 uu____6326  in
                     (uu____6324, args1)
               else
                 (let uu____6339 = p_indexingTerm head1  in
                  (uu____6339, args))
                in
             (match uu____6216 with
              | (head_doc,args1) ->
                  let uu____6360 =
                    let uu____6361 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6361 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6360))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6381 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6381)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6399 =
               let uu____6400 = p_quident lid  in
               let uu____6401 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6400 uu____6401  in
             FStar_Pprint.group uu____6399
         | hd1::tl1 ->
             let uu____6418 =
               let uu____6419 =
                 let uu____6420 =
                   let uu____6421 = p_quident lid  in
                   let uu____6422 = p_argTerm hd1  in
                   prefix2 uu____6421 uu____6422  in
                 FStar_Pprint.group uu____6420  in
               let uu____6423 =
                 let uu____6424 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6424  in
               FStar_Pprint.op_Hat_Hat uu____6419 uu____6423  in
             FStar_Pprint.group uu____6418)
    | uu____6429 -> p_indexingTerm e

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
         (let uu____6438 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6438 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6440 = str "#"  in
        let uu____6441 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6440 uu____6441
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6444 = str "#["  in
        let uu____6445 =
          let uu____6446 = p_indexingTerm t  in
          let uu____6447 =
            let uu____6448 = str "]"  in
            let uu____6449 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6448 uu____6449  in
          FStar_Pprint.op_Hat_Hat uu____6446 uu____6447  in
        FStar_Pprint.op_Hat_Hat uu____6444 uu____6445
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6451  ->
    match uu____6451 with | (e,uu____6457) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6462;_},e1::e2::[])
          ->
          let uu____6467 =
            let uu____6468 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6469 =
              let uu____6470 =
                let uu____6471 = p_term false false e2  in
                soft_parens_with_nesting uu____6471  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6470  in
            FStar_Pprint.op_Hat_Hat uu____6468 uu____6469  in
          FStar_Pprint.group uu____6467
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6472;_},e1::e2::[])
          ->
          let uu____6477 =
            let uu____6478 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6479 =
              let uu____6480 =
                let uu____6481 = p_term false false e2  in
                soft_brackets_with_nesting uu____6481  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6480  in
            FStar_Pprint.op_Hat_Hat uu____6478 uu____6479  in
          FStar_Pprint.group uu____6477
      | uu____6482 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6487 = p_quident lid  in
        let uu____6488 =
          let uu____6489 =
            let uu____6490 = p_term false false e1  in
            soft_parens_with_nesting uu____6490  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6489  in
        FStar_Pprint.op_Hat_Hat uu____6487 uu____6488
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6496 =
          let uu____6497 = FStar_Ident.text_of_id op  in str uu____6497  in
        let uu____6498 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6496 uu____6498
    | uu____6499 -> p_atomicTermNotQUident e

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
         | uu____6508 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6515 =
          let uu____6516 = FStar_Ident.text_of_id op  in str uu____6516  in
        let uu____6517 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6515 uu____6517
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6521 =
          let uu____6522 =
            let uu____6523 =
              let uu____6524 = FStar_Ident.text_of_id op  in str uu____6524
               in
            let uu____6525 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6523 uu____6525  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6522  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6521
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6540 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6541 =
          let uu____6542 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6543 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6542 p_tmEq uu____6543  in
        let uu____6550 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6540 uu____6541 uu____6550
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6553 =
          let uu____6554 = p_atomicTermNotQUident e1  in
          let uu____6555 =
            let uu____6556 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6556  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6554 uu____6555
           in
        FStar_Pprint.group uu____6553
    | uu____6557 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6562 = p_quident constr_lid  in
        let uu____6563 =
          let uu____6564 =
            let uu____6565 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6565  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6564  in
        FStar_Pprint.op_Hat_Hat uu____6562 uu____6563
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6567 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6567 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6569 = p_term false false e1  in
        soft_parens_with_nesting uu____6569
    | uu____6570 when is_array e ->
        let es = extract_from_list e  in
        let uu____6574 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6575 =
          let uu____6576 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6576
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6579 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6574 uu____6575 uu____6579
    | uu____6580 when is_list e ->
        let uu____6581 =
          let uu____6582 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6583 = extract_from_list e  in
          separate_map_or_flow_last uu____6582
            (fun ps  -> p_noSeqTerm ps false) uu____6583
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6581 FStar_Pprint.rbracket
    | uu____6588 when is_lex_list e ->
        let uu____6589 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6590 =
          let uu____6591 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6592 = extract_from_list e  in
          separate_map_or_flow_last uu____6591
            (fun ps  -> p_noSeqTerm ps false) uu____6592
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6589 uu____6590 FStar_Pprint.rbracket
    | uu____6597 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6601 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6602 =
          let uu____6603 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6603 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6601 uu____6602 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6607 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6608 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6607 uu____6608
    | FStar_Parser_AST.Op (op,args) when
        let uu____6615 = handleable_op op args  in
        Prims.op_Negation uu____6615 ->
        let uu____6616 =
          let uu____6617 =
            let uu____6618 = FStar_Ident.text_of_id op  in
            let uu____6619 =
              let uu____6620 =
                let uu____6621 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6621
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6620  in
            Prims.strcat uu____6618 uu____6619  in
          Prims.strcat "Operation " uu____6617  in
        failwith uu____6616
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6623 = str "u#"  in
        let uu____6624 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6623 uu____6624
    | FStar_Parser_AST.Wild  ->
        let uu____6625 = p_term false false e  in
        soft_parens_with_nesting uu____6625
    | FStar_Parser_AST.Const uu____6626 ->
        let uu____6627 = p_term false false e  in
        soft_parens_with_nesting uu____6627
    | FStar_Parser_AST.Op uu____6628 ->
        let uu____6635 = p_term false false e  in
        soft_parens_with_nesting uu____6635
    | FStar_Parser_AST.Tvar uu____6636 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Var uu____6638 ->
        let uu____6639 = p_term false false e  in
        soft_parens_with_nesting uu____6639
    | FStar_Parser_AST.Name uu____6640 ->
        let uu____6641 = p_term false false e  in
        soft_parens_with_nesting uu____6641
    | FStar_Parser_AST.Construct uu____6642 ->
        let uu____6653 = p_term false false e  in
        soft_parens_with_nesting uu____6653
    | FStar_Parser_AST.Abs uu____6654 ->
        let uu____6661 = p_term false false e  in
        soft_parens_with_nesting uu____6661
    | FStar_Parser_AST.App uu____6662 ->
        let uu____6669 = p_term false false e  in
        soft_parens_with_nesting uu____6669
    | FStar_Parser_AST.Let uu____6670 ->
        let uu____6691 = p_term false false e  in
        soft_parens_with_nesting uu____6691
    | FStar_Parser_AST.LetOpen uu____6692 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.Seq uu____6698 ->
        let uu____6703 = p_term false false e  in
        soft_parens_with_nesting uu____6703
    | FStar_Parser_AST.Bind uu____6704 ->
        let uu____6711 = p_term false false e  in
        soft_parens_with_nesting uu____6711
    | FStar_Parser_AST.If uu____6712 ->
        let uu____6719 = p_term false false e  in
        soft_parens_with_nesting uu____6719
    | FStar_Parser_AST.Match uu____6720 ->
        let uu____6735 = p_term false false e  in
        soft_parens_with_nesting uu____6735
    | FStar_Parser_AST.TryWith uu____6736 ->
        let uu____6751 = p_term false false e  in
        soft_parens_with_nesting uu____6751
    | FStar_Parser_AST.Ascribed uu____6752 ->
        let uu____6761 = p_term false false e  in
        soft_parens_with_nesting uu____6761
    | FStar_Parser_AST.Record uu____6762 ->
        let uu____6775 = p_term false false e  in
        soft_parens_with_nesting uu____6775
    | FStar_Parser_AST.Project uu____6776 ->
        let uu____6781 = p_term false false e  in
        soft_parens_with_nesting uu____6781
    | FStar_Parser_AST.Product uu____6782 ->
        let uu____6789 = p_term false false e  in
        soft_parens_with_nesting uu____6789
    | FStar_Parser_AST.Sum uu____6790 ->
        let uu____6797 = p_term false false e  in
        soft_parens_with_nesting uu____6797
    | FStar_Parser_AST.QForall uu____6798 ->
        let uu____6811 = p_term false false e  in
        soft_parens_with_nesting uu____6811
    | FStar_Parser_AST.QExists uu____6812 ->
        let uu____6825 = p_term false false e  in
        soft_parens_with_nesting uu____6825
    | FStar_Parser_AST.Refine uu____6826 ->
        let uu____6831 = p_term false false e  in
        soft_parens_with_nesting uu____6831
    | FStar_Parser_AST.NamedTyp uu____6832 ->
        let uu____6837 = p_term false false e  in
        soft_parens_with_nesting uu____6837
    | FStar_Parser_AST.Requires uu____6838 ->
        let uu____6845 = p_term false false e  in
        soft_parens_with_nesting uu____6845
    | FStar_Parser_AST.Ensures uu____6846 ->
        let uu____6853 = p_term false false e  in
        soft_parens_with_nesting uu____6853
    | FStar_Parser_AST.Attributes uu____6854 ->
        let uu____6857 = p_term false false e  in
        soft_parens_with_nesting uu____6857
    | FStar_Parser_AST.Quote uu____6858 ->
        let uu____6863 = p_term false false e  in
        soft_parens_with_nesting uu____6863
    | FStar_Parser_AST.VQuote uu____6864 ->
        let uu____6865 = p_term false false e  in
        soft_parens_with_nesting uu____6865
    | FStar_Parser_AST.Antiquote uu____6866 ->
        let uu____6867 = p_term false false e  in
        soft_parens_with_nesting uu____6867

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___119_6868  ->
    match uu___119_6868 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6874) ->
        let uu____6875 = str s  in FStar_Pprint.dquotes uu____6875
    | FStar_Const.Const_bytearray (bytes,uu____6877) ->
        let uu____6882 =
          let uu____6883 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6883  in
        let uu____6884 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6882 uu____6884
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___117_6904 =
          match uu___117_6904 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___118_6910 =
          match uu___118_6910 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6921  ->
               match uu____6921 with
               | (s,w) ->
                   let uu____6928 = signedness s  in
                   let uu____6929 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6928 uu____6929)
            sign_width_opt
           in
        let uu____6930 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6930 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6932 = FStar_Range.string_of_range r  in str uu____6932
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6934 = p_quident lid  in
        let uu____6935 =
          let uu____6936 =
            let uu____6937 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6937  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6936  in
        FStar_Pprint.op_Hat_Hat uu____6934 uu____6935

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6939 = str "u#"  in
    let uu____6940 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6939 uu____6940

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6942;_},u1::u2::[])
        ->
        let uu____6947 =
          let uu____6948 = p_universeFrom u1  in
          let uu____6949 =
            let uu____6950 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6950  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6948 uu____6949  in
        FStar_Pprint.group uu____6947
    | FStar_Parser_AST.App uu____6951 ->
        let uu____6958 = head_and_args u  in
        (match uu____6958 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6984 =
                    let uu____6985 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6986 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6994  ->
                           match uu____6994 with
                           | (u1,uu____7000) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6985 uu____6986  in
                  FStar_Pprint.group uu____6984
              | uu____7001 ->
                  let uu____7002 =
                    let uu____7003 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7003
                     in
                  failwith uu____7002))
    | uu____7004 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7027 = FStar_Ident.text_of_id id1  in str uu____7027
    | FStar_Parser_AST.Paren u1 ->
        let uu____7029 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7029
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7030;_},uu____7031::uu____7032::[])
        ->
        let uu____7035 = p_universeFrom u  in
        soft_parens_with_nesting uu____7035
    | FStar_Parser_AST.App uu____7036 ->
        let uu____7043 = p_universeFrom u  in
        soft_parens_with_nesting uu____7043
    | uu____7044 ->
        let uu____7045 =
          let uu____7046 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7046
           in
        failwith uu____7045

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
       | FStar_Parser_AST.Module (uu____7118,decls) ->
           let uu____7124 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7124
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7133,decls,uu____7135) ->
           let uu____7140 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7140
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7193  ->
         match uu____7193 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7209)) -> false
      | ([],uu____7212) -> false
      | uu____7215 -> true  in
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
        | FStar_Parser_AST.Module (uu____7259,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7265,decls,uu____7267) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7312 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7325;
                 FStar_Parser_AST.doc = uu____7326;
                 FStar_Parser_AST.quals = uu____7327;
                 FStar_Parser_AST.attrs = uu____7328;_}::uu____7329 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7335 =
                   let uu____7338 =
                     let uu____7341 = FStar_List.tl ds  in d :: uu____7341
                      in
                   d0 :: uu____7338  in
                 (uu____7335, (d0.FStar_Parser_AST.drange))
             | uu____7346 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7312 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7400 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7400 dummy_meta
                      FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7496 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7496, comments1))))))
  