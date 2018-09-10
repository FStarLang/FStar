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
  has_fsdoc: Prims.bool ;
  is_fsdoc: Prims.bool }
let (__proj__Mkdecl_meta__item__r : decl_meta -> FStar_Range.range) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;
        is_fsdoc = __fname__is_fsdoc;_} -> __fname__r
  
let (__proj__Mkdecl_meta__item__has_qs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;
        is_fsdoc = __fname__is_fsdoc;_} -> __fname__has_qs
  
let (__proj__Mkdecl_meta__item__has_attrs : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;
        is_fsdoc = __fname__is_fsdoc;_} -> __fname__has_attrs
  
let (__proj__Mkdecl_meta__item__has_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;
        is_fsdoc = __fname__is_fsdoc;_} -> __fname__has_fsdoc
  
let (__proj__Mkdecl_meta__item__is_fsdoc : decl_meta -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { r = __fname__r; has_qs = __fname__has_qs;
        has_attrs = __fname__has_attrs; has_fsdoc = __fname__has_fsdoc;
        is_fsdoc = __fname__is_fsdoc;_} -> __fname__is_fsdoc
  
let (dummy_meta : decl_meta) =
  {
    r = FStar_Range.dummyRange;
    has_qs = false;
    has_attrs = false;
    has_fsdoc = false;
    is_fsdoc = false
  } 
let with_comment :
  'Auu____2135 .
    ('Auu____2135 -> FStar_Pprint.document) ->
      'Auu____2135 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2176 = FStar_ST.op_Bang comment_stack  in
          match uu____2176 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2235 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2235
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2272 =
                    let uu____2273 =
                      let uu____2274 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2274
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2273  in
                  comments_before_pos uu____2272 print_pos lookahead_pos))
              else
                (let uu____2276 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2276))
           in
        let uu____2277 =
          let uu____2282 =
            let uu____2283 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2283  in
          let uu____2284 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2282 uu____2284  in
        match uu____2277 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2290 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2290
              else comments  in
            let uu____2296 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2296
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos ->
        decl_meta ->
          FStar_Pprint.document ->
            Prims.bool -> Prims.bool -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos  ->
        fun meta_decl  ->
          fun doc1  ->
            fun r  ->
              fun init1  ->
                let uu____2332 = FStar_ST.op_Bang comment_stack  in
                match uu____2332 with
                | (comment,crange)::cs when
                    FStar_Range.range_before_pos crange pos ->
                    (FStar_ST.op_Colon_Equals comment_stack cs;
                     (let lnum =
                        let uu____2416 =
                          let uu____2417 =
                            let uu____2418 =
                              FStar_Range.start_of_range crange  in
                            FStar_Range.line_of_pos uu____2418  in
                          uu____2417 - lbegin  in
                        max k uu____2416  in
                      let lnum1 = min (Prims.parse_int "2") lnum  in
                      let doc2 =
                        let uu____2421 =
                          let uu____2422 =
                            FStar_Pprint.repeat lnum1 FStar_Pprint.hardline
                             in
                          let uu____2423 = str comment  in
                          FStar_Pprint.op_Hat_Hat uu____2422 uu____2423  in
                        FStar_Pprint.op_Hat_Hat doc1 uu____2421  in
                      let uu____2424 =
                        let uu____2425 = FStar_Range.end_of_range crange  in
                        FStar_Range.line_of_pos uu____2425  in
                      place_comments_until_pos (Prims.parse_int "1")
                        uu____2424 pos meta_decl doc2 true init1))
                | uu____2426 ->
                    if doc1 = FStar_Pprint.empty
                    then FStar_Pprint.empty
                    else
                      (let lnum =
                         let uu____2435 = FStar_Range.line_of_pos pos  in
                         uu____2435 - lbegin  in
                       let lnum1 = min (Prims.parse_int "3") lnum  in
                       let lnum2 =
                         if meta_decl.has_qs || meta_decl.has_attrs
                         then lnum1 - (Prims.parse_int "1")
                         else lnum1  in
                       let lnum3 = max k lnum2  in
                       let lnum4 =
                         if meta_decl.has_qs && meta_decl.has_attrs
                         then (Prims.parse_int "2")
                         else lnum3  in
                       let lnum5 =
                         if (Prims.op_Negation r) && meta_decl.has_fsdoc
                         then min (Prims.parse_int "2") lnum4
                         else lnum4  in
                       let lnum6 =
                         if r && (meta_decl.is_fsdoc || meta_decl.has_fsdoc)
                         then (Prims.parse_int "1")
                         else lnum5  in
                       let lnum7 =
                         if init1 then (Prims.parse_int "2") else lnum6  in
                       let uu____2448 =
                         FStar_Pprint.repeat lnum7 FStar_Pprint.hardline  in
                       FStar_Pprint.op_Hat_Hat doc1 uu____2448)
  
let separate_map_with_comments :
  'Auu____2461 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2461 -> FStar_Pprint.document) ->
          'Auu____2461 Prims.list ->
            ('Auu____2461 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2518 x =
              match uu____2518 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2533 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2533 meta_decl doc1 false false
                     in
                  let uu____2534 =
                    let uu____2535 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2535  in
                  let uu____2536 =
                    let uu____2537 =
                      let uu____2538 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2538  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2537  in
                  (uu____2534, uu____2536)
               in
            let uu____2539 =
              let uu____2546 = FStar_List.hd xs  in
              let uu____2547 = FStar_List.tl xs  in (uu____2546, uu____2547)
               in
            match uu____2539 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2564 =
                    let uu____2565 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2565  in
                  let uu____2566 =
                    let uu____2567 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2567  in
                  (uu____2564, uu____2566)  in
                let uu____2568 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2568
  
let separate_map_with_comments_kw :
  'Auu____2591 'Auu____2592 .
    'Auu____2591 ->
      'Auu____2591 ->
        ('Auu____2591 -> 'Auu____2592 -> FStar_Pprint.document) ->
          'Auu____2592 Prims.list ->
            ('Auu____2592 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2654 x =
              match uu____2654 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2669 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2669 meta_decl doc1 false false
                     in
                  let uu____2670 =
                    let uu____2671 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2671  in
                  let uu____2672 =
                    let uu____2673 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2673  in
                  (uu____2670, uu____2672)
               in
            let uu____2674 =
              let uu____2681 = FStar_List.hd xs  in
              let uu____2682 = FStar_List.tl xs  in (uu____2681, uu____2682)
               in
            match uu____2674 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2699 =
                    let uu____2700 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2700  in
                  let uu____2701 = f prefix1 x  in (uu____2699, uu____2701)
                   in
                let uu____2702 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2702
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3418)) ->
          let uu____3421 =
            let uu____3422 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3422 FStar_Util.is_upper  in
          if uu____3421
          then
            let uu____3425 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3425 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3427 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3434 =
      FStar_Pprint.optional (fun d1  -> p_fsdoc d1) d.FStar_Parser_AST.doc
       in
    let uu____3437 =
      let uu____3438 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3439 =
        let uu____3440 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3440  in
      FStar_Pprint.op_Hat_Hat uu____3438 uu____3439  in
    FStar_Pprint.op_Hat_Hat uu____3434 uu____3437

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3442 ->
        let uu____3443 =
          let uu____3444 = str "@ "  in
          let uu____3445 =
            let uu____3446 =
              let uu____3447 =
                let uu____3448 =
                  let uu____3449 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3449  in
                FStar_Pprint.op_Hat_Hat uu____3448 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3447  in
            FStar_Pprint.op_Hat_Hat uu____3446 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3444 uu____3445  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3443

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3452  ->
    match uu____3452 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3488 =
                match uu____3488 with
                | (kwd,arg) ->
                    let uu____3495 = str "@"  in
                    let uu____3496 =
                      let uu____3497 = str kwd  in
                      let uu____3498 =
                        let uu____3499 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3499
                         in
                      FStar_Pprint.op_Hat_Hat uu____3497 uu____3498  in
                    FStar_Pprint.op_Hat_Hat uu____3495 uu____3496
                 in
              let uu____3500 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____3500 FStar_Pprint.hardline
           in
        let uu____3505 =
          let uu____3506 =
            let uu____3507 =
              let uu____3508 = str doc1  in
              let uu____3509 =
                let uu____3510 =
                  let uu____3511 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3511  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3510  in
              FStar_Pprint.op_Hat_Hat uu____3508 uu____3509  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3507  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3506  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3505

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3515 =
          let uu____3516 = str "val"  in
          let uu____3517 =
            let uu____3518 =
              let uu____3519 = p_lident lid  in
              let uu____3520 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3519 uu____3520  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3518  in
          FStar_Pprint.op_Hat_Hat uu____3516 uu____3517  in
        let uu____3521 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3515 uu____3521
    | FStar_Parser_AST.TopLevelLet (uu____3522,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3547 =
               let uu____3548 = str "let"  in p_letlhs uu____3548 lb  in
             FStar_Pprint.group uu____3547) lbs
    | uu____3549 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___108_3564 =
          match uu___108_3564 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3572 = f x  in
              let uu____3573 =
                let uu____3574 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3574  in
              FStar_Pprint.op_Hat_Hat uu____3572 uu____3573
           in
        let uu____3575 = str "["  in
        let uu____3576 =
          let uu____3577 = p_list' l  in
          let uu____3578 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3577 uu____3578  in
        FStar_Pprint.op_Hat_Hat uu____3575 uu____3576

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3581 =
          let uu____3582 = str "open"  in
          let uu____3583 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3582 uu____3583  in
        FStar_Pprint.group uu____3581
    | FStar_Parser_AST.Include uid ->
        let uu____3585 =
          let uu____3586 = str "include"  in
          let uu____3587 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3586 uu____3587  in
        FStar_Pprint.group uu____3585
    | FStar_Parser_AST.Friend uid ->
        let uu____3589 =
          let uu____3590 = str "friend"  in
          let uu____3591 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3590 uu____3591  in
        FStar_Pprint.group uu____3589
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3594 =
          let uu____3595 = str "module"  in
          let uu____3596 =
            let uu____3597 =
              let uu____3598 = p_uident uid1  in
              let uu____3599 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3598 uu____3599  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3597  in
          FStar_Pprint.op_Hat_Hat uu____3595 uu____3596  in
        let uu____3600 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3594 uu____3600
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3602 =
          let uu____3603 = str "module"  in
          let uu____3604 =
            let uu____3605 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3605  in
          FStar_Pprint.op_Hat_Hat uu____3603 uu____3604  in
        FStar_Pprint.group uu____3602
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3606,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3639 = str "effect"  in
          let uu____3640 =
            let uu____3641 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3641  in
          FStar_Pprint.op_Hat_Hat uu____3639 uu____3640  in
        let uu____3642 =
          let uu____3643 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3643 FStar_Pprint.equals
           in
        let uu____3644 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3642 uu____3644
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3665 =
          let uu____3666 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3666  in
        let uu____3679 =
          let uu____3680 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3718 =
                    let uu____3719 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3719 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3718)) uu____3680
           in
        FStar_Pprint.op_Hat_Hat uu____3665 uu____3679
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3735 = str "let"  in
          let uu____3736 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3735 uu____3736  in
        let uu____3737 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3737 p_letbinding lbs
          (fun uu____3746  ->
             match uu____3746 with
             | (p,t) ->
                 let uu____3753 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____3753;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
                   is_fsdoc = false
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3756 = str "val"  in
        let uu____3757 =
          let uu____3758 =
            let uu____3759 = p_lident lid  in
            let uu____3760 =
              let uu____3761 =
                let uu____3762 =
                  let uu____3763 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3763  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3762  in
              FStar_Pprint.group uu____3761  in
            FStar_Pprint.op_Hat_Hat uu____3759 uu____3760  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3758  in
        FStar_Pprint.op_Hat_Hat uu____3756 uu____3757
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3767 =
            let uu____3768 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3768 FStar_Util.is_upper  in
          if uu____3767
          then FStar_Pprint.empty
          else
            (let uu____3772 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3772 FStar_Pprint.space)
           in
        let uu____3773 =
          let uu____3774 = p_ident id1  in
          let uu____3775 =
            let uu____3776 =
              let uu____3777 =
                let uu____3778 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3778  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3777  in
            FStar_Pprint.group uu____3776  in
          FStar_Pprint.op_Hat_Hat uu____3774 uu____3775  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3773
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3785 = str "exception"  in
        let uu____3786 =
          let uu____3787 =
            let uu____3788 = p_uident uid  in
            let uu____3789 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3793 =
                     let uu____3794 = str "of"  in
                     let uu____3795 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3794 uu____3795  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3793) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3788 uu____3789  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3787  in
        FStar_Pprint.op_Hat_Hat uu____3785 uu____3786
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3797 = str "new_effect"  in
        let uu____3798 =
          let uu____3799 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3799  in
        FStar_Pprint.op_Hat_Hat uu____3797 uu____3798
    | FStar_Parser_AST.SubEffect se ->
        let uu____3801 = str "sub_effect"  in
        let uu____3802 =
          let uu____3803 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3803  in
        FStar_Pprint.op_Hat_Hat uu____3801 uu____3802
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 -> p_fsdoc doc1
    | FStar_Parser_AST.Main uu____3806 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3807,uu____3808) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3831 = str "%splice"  in
        let uu____3832 =
          let uu____3833 =
            let uu____3834 = str ";"  in p_list p_uident uu____3834 ids  in
          let uu____3835 =
            let uu____3836 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3836  in
          FStar_Pprint.op_Hat_Hat uu____3833 uu____3835  in
        FStar_Pprint.op_Hat_Hat uu____3831 uu____3832

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___109_3837  ->
    match uu___109_3837 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3839 = str "#set-options"  in
        let uu____3840 =
          let uu____3841 =
            let uu____3842 = str s  in FStar_Pprint.dquotes uu____3842  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3841  in
        FStar_Pprint.op_Hat_Hat uu____3839 uu____3840
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3846 = str "#reset-options"  in
        let uu____3847 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3851 =
                 let uu____3852 = str s  in FStar_Pprint.dquotes uu____3852
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3851) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3846 uu____3847
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3856 = str "#push-options"  in
        let uu____3857 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3861 =
                 let uu____3862 = str s  in FStar_Pprint.dquotes uu____3862
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3861) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3856 uu____3857
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
    fun uu____3887  ->
      match uu____3887 with
      | (typedecl,fsdoc_opt) ->
          let uu____3900 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3900 with
           | (decl,body) ->
               let uu____3918 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3918)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___110_3920  ->
      match uu___110_3920 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3950 = FStar_Pprint.empty  in
          let uu____3951 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3951, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3972 =
            let uu____3973 = p_typ false false t  in jump2 uu____3973  in
          let uu____3974 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3974, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4028 =
            match uu____4028 with
            | (lid1,t,doc_opt) ->
                let uu____4044 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4044
             in
          let p_fields uu____4060 =
            let uu____4061 =
              let uu____4062 =
                let uu____4063 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4063 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4062  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4061  in
          let uu____4072 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4072, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4133 =
            match uu____4133 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4159 =
                    let uu____4160 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4160  in
                  FStar_Range.extend_to_end_of_line uu____4159  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4186 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4199 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4199,
            ((fun uu____4205  ->
                let uu____4206 = datacon_doc ()  in jump2 uu____4206)))

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
  fun uu____4207  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4207 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4241 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4241  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4243 =
                        let uu____4246 =
                          let uu____4249 = p_fsdoc fsdoc  in
                          let uu____4250 =
                            let uu____4253 = cont lid_doc  in [uu____4253]
                             in
                          uu____4249 :: uu____4250  in
                        kw :: uu____4246  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4243
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4258 =
                        let uu____4259 =
                          let uu____4260 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4260 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4259
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4258
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4275 =
                          let uu____4276 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4276  in
                        prefix2 uu____4275 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4278  ->
      match uu____4278 with
      | (lid,t,doc_opt) ->
          let uu____4294 =
            let uu____4295 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4296 =
              let uu____4297 = p_lident lid  in
              let uu____4298 =
                let uu____4299 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4299  in
              FStar_Pprint.op_Hat_Hat uu____4297 uu____4298  in
            FStar_Pprint.op_Hat_Hat uu____4295 uu____4296  in
          FStar_Pprint.group uu____4294

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4300  ->
    match uu____4300 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4328 =
            let uu____4329 =
              let uu____4330 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4330  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4329  in
          FStar_Pprint.group uu____4328  in
        let uu____4331 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4332 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4336 =
                 let uu____4337 =
                   let uu____4338 =
                     let uu____4339 =
                       let uu____4340 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4340
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4339  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4338  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4337  in
               FStar_Pprint.group uu____4336) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4331 uu____4332

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4342  ->
      match uu____4342 with
      | (pat,uu____4348) ->
          let uu____4349 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4368 =
                  let uu____4369 =
                    let uu____4370 =
                      let uu____4371 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4371
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4370  in
                  FStar_Pprint.group uu____4369  in
                (pat1, uu____4368)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4383 =
                  let uu____4384 =
                    let uu____4385 =
                      let uu____4386 =
                        let uu____4387 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4387
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4386
                       in
                    FStar_Pprint.group uu____4385  in
                  let uu____4388 =
                    let uu____4389 =
                      let uu____4390 = str "by"  in
                      let uu____4391 =
                        let uu____4392 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4392
                         in
                      FStar_Pprint.op_Hat_Hat uu____4390 uu____4391  in
                    FStar_Pprint.group uu____4389  in
                  FStar_Pprint.op_Hat_Hat uu____4384 uu____4388  in
                (pat1, uu____4383)
            | uu____4393 -> (pat, FStar_Pprint.empty)  in
          (match uu____4349 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4397);
                       FStar_Parser_AST.prange = uu____4398;_},pats)
                    ->
                    let uu____4408 =
                      let uu____4409 =
                        let uu____4410 =
                          let uu____4411 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4411  in
                        FStar_Pprint.group uu____4410  in
                      let uu____4412 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4409 uu____4412  in
                    prefix2_nonempty uu____4408 ascr_doc
                | uu____4413 ->
                    let uu____4414 =
                      let uu____4415 =
                        let uu____4416 =
                          let uu____4417 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4417  in
                        FStar_Pprint.group uu____4416  in
                      FStar_Pprint.op_Hat_Hat uu____4415 ascr_doc  in
                    FStar_Pprint.group uu____4414))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4419  ->
      match uu____4419 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4428 =
            let uu____4429 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4429  in
          let uu____4430 =
            let uu____4431 =
              let uu____4432 =
                let uu____4433 =
                  let uu____4434 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4434  in
                FStar_Pprint.group uu____4433  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4432  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4431  in
          FStar_Pprint.ifflat uu____4428 uu____4430

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___111_4435  ->
    match uu___111_4435 with
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
        let uu____4460 = p_uident uid  in
        let uu____4461 = p_binders true bs  in
        let uu____4462 =
          let uu____4463 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4463  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4460 uu____4461 uu____4462

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
          let uu____4473 =
            let uu____4474 =
              let uu____4475 =
                let uu____4476 = p_uident uid  in
                let uu____4477 = p_binders true bs  in
                let uu____4478 =
                  let uu____4479 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4479  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4476 uu____4477 uu____4478
                 in
              FStar_Pprint.group uu____4475  in
            let uu____4480 =
              let uu____4481 = str "with"  in
              let uu____4482 =
                let uu____4483 =
                  let uu____4484 =
                    let uu____4485 =
                      let uu____4486 =
                        let uu____4487 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4487
                         in
                      separate_map_last uu____4486 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4485  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4484  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4483  in
              FStar_Pprint.op_Hat_Hat uu____4481 uu____4482  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4474 uu____4480  in
          braces_with_nesting uu____4473

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4490,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4519 =
            let uu____4520 = p_lident lid  in
            let uu____4521 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4520 uu____4521  in
          let uu____4522 = p_simpleTerm ps false e  in
          prefix2 uu____4519 uu____4522
      | uu____4523 ->
          let uu____4524 =
            let uu____4525 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4525
             in
          failwith uu____4524

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4587 =
        match uu____4587 with
        | (kwd,t) ->
            let uu____4594 =
              let uu____4595 = str kwd  in
              let uu____4596 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4595 uu____4596  in
            let uu____4597 = p_simpleTerm ps false t  in
            prefix2 uu____4594 uu____4597
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4602 =
      let uu____4603 =
        let uu____4604 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4605 =
          let uu____4606 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4606  in
        FStar_Pprint.op_Hat_Hat uu____4604 uu____4605  in
      let uu____4607 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4603 uu____4607  in
    let uu____4608 =
      let uu____4609 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4609  in
    FStar_Pprint.op_Hat_Hat uu____4602 uu____4608

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___112_4610  ->
    match uu___112_4610 with
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
        let uu____4613 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4613 FStar_Pprint.hardline
    | uu____4614 ->
        let uu____4615 =
          let uu____4616 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4616  in
        FStar_Pprint.op_Hat_Hat uu____4615 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___113_4619  ->
    match uu___113_4619 with
    | FStar_Parser_AST.Rec  ->
        let uu____4620 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4620
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___114_4621  ->
    match uu___114_4621 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        (match t.FStar_Parser_AST.tm with
         | FStar_Parser_AST.Abs (uu____4623,e) ->
             let uu____4629 = str "#["  in
             let uu____4630 =
               let uu____4631 = p_term false false e  in
               let uu____4632 =
                 let uu____4633 = str "]"  in
                 FStar_Pprint.op_Hat_Hat uu____4633 break1  in
               FStar_Pprint.op_Hat_Hat uu____4631 uu____4632  in
             FStar_Pprint.op_Hat_Hat uu____4629 uu____4630
         | uu____4634 -> failwith "Invalid term for typeclass")

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4639 =
          let uu____4640 =
            let uu____4641 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4641  in
          FStar_Pprint.separate_map uu____4640 p_tuplePattern pats  in
        FStar_Pprint.group uu____4639
    | uu____4642 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4649 =
          let uu____4650 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4650 p_constructorPattern pats  in
        FStar_Pprint.group uu____4649
    | uu____4651 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4654;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4659 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4660 = p_constructorPattern hd1  in
        let uu____4661 = p_constructorPattern tl1  in
        infix0 uu____4659 uu____4660 uu____4661
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4663;_},pats)
        ->
        let uu____4669 = p_quident uid  in
        let uu____4670 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4669 uu____4670
    | uu____4671 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4687;
               FStar_Parser_AST.blevel = uu____4688;
               FStar_Parser_AST.aqual = uu____4689;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4697 =
               let uu____4698 = p_ident lid  in
               p_refinement aqual uu____4698 t1 phi  in
             soft_parens_with_nesting uu____4697
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4701;
               FStar_Parser_AST.blevel = uu____4702;
               FStar_Parser_AST.aqual = uu____4703;_},phi))
             ->
             let uu____4709 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4709
         | uu____4710 ->
             let uu____4715 =
               let uu____4716 = p_tuplePattern pat  in
               let uu____4717 =
                 let uu____4718 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4718
                  in
               FStar_Pprint.op_Hat_Hat uu____4716 uu____4717  in
             soft_parens_with_nesting uu____4715)
    | FStar_Parser_AST.PatList pats ->
        let uu____4722 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4722 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4739 =
          match uu____4739 with
          | (lid,pat) ->
              let uu____4746 = p_qlident lid  in
              let uu____4747 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4746 uu____4747
           in
        let uu____4748 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4748
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4758 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4759 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4760 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4758 uu____4759 uu____4760
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4769 =
          let uu____4770 =
            let uu____4771 =
              let uu____4772 = FStar_Ident.text_of_id op  in str uu____4772
               in
            let uu____4773 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4771 uu____4773  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4770  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4769
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4777 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4777 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4785 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4786 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4785 uu____4786
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4788 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4791;
           FStar_Parser_AST.prange = uu____4792;_},uu____4793)
        ->
        let uu____4798 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4798
    | FStar_Parser_AST.PatTuple (uu____4799,false ) ->
        let uu____4804 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4804
    | uu____4805 ->
        let uu____4806 =
          let uu____4807 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4807  in
        failwith uu____4806

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4809;_},uu____4810)
        -> true
    | uu____4815 -> false

and (is_meta_qualifier :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun aq  ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta uu____4819) -> true
    | uu____4820 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4826 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4827 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4826 uu____4827
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4834;
                   FStar_Parser_AST.blevel = uu____4835;
                   FStar_Parser_AST.aqual = uu____4836;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4840 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4840 t1 phi
            | uu____4841 ->
                let t' =
                  let uu____4843 = is_typ_tuple t  in
                  if uu____4843
                  then
                    let uu____4844 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4844
                  else p_tmFormula t  in
                let uu____4846 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4847 =
                  let uu____4848 = p_lident lid  in
                  let uu____4849 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4848 uu____4849  in
                FStar_Pprint.op_Hat_Hat uu____4846 uu____4847
             in
          let uu____4850 =
            is_atomic || (is_meta_qualifier b.FStar_Parser_AST.aqual)  in
          if uu____4850
          then
            let uu____4851 =
              let uu____4852 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4852  in
            FStar_Pprint.group uu____4851
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4854 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4861;
                  FStar_Parser_AST.blevel = uu____4862;
                  FStar_Parser_AST.aqual = uu____4863;_},phi)
               ->
               if is_atomic
               then
                 let uu____4867 =
                   let uu____4868 =
                     let uu____4869 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4869 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4868  in
                 FStar_Pprint.group uu____4867
               else
                 (let uu____4871 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4871)
           | uu____4872 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4881 -> false
            | FStar_Parser_AST.App uu____4892 -> false
            | FStar_Parser_AST.Op uu____4899 -> false
            | uu____4906 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4910 =
            let uu____4911 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4912 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4911 uu____4912  in
          let uu____4913 =
            let uu____4914 = p_appTerm t  in
            let uu____4915 =
              let uu____4916 =
                let uu____4917 =
                  let uu____4918 = soft_braces_with_nesting_tight phi1  in
                  let uu____4919 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4918 uu____4919  in
                FStar_Pprint.group uu____4917  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4916
               in
            FStar_Pprint.op_Hat_Hat uu____4914 uu____4915  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4910 uu____4913

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4930 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4930

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4935 = FStar_Ident.text_of_id lid  in str uu____4935)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4938 = FStar_Ident.text_of_lid lid  in str uu____4938)

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
            let uu____4956 =
              let uu____4957 =
                let uu____4958 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4958 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4957  in
            let uu____4959 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4956 uu____4959
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4963 =
              let uu____4964 =
                let uu____4965 =
                  let uu____4966 = p_lident x  in
                  let uu____4967 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4966 uu____4967  in
                let uu____4968 =
                  let uu____4969 = p_noSeqTerm true false e1  in
                  let uu____4970 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4969 uu____4970  in
                op_Hat_Slash_Plus_Hat uu____4965 uu____4968  in
              FStar_Pprint.group uu____4964  in
            let uu____4971 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4963 uu____4971
        | uu____4972 ->
            let uu____4973 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4973

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
            let uu____4984 =
              let uu____4985 = p_tmIff e1  in
              let uu____4986 =
                let uu____4987 =
                  let uu____4988 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4988
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4987  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4985 uu____4986  in
            FStar_Pprint.group uu____4984
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4994 =
              let uu____4995 = p_tmIff e1  in
              let uu____4996 =
                let uu____4997 =
                  let uu____4998 =
                    let uu____4999 = p_typ false false t  in
                    let uu____5000 =
                      let uu____5001 = str "by"  in
                      let uu____5002 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5001 uu____5002  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4999 uu____5000  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4998
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4997  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4995 uu____4996  in
            FStar_Pprint.group uu____4994
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5003;_},e1::e2::e3::[])
            ->
            let uu____5009 =
              let uu____5010 =
                let uu____5011 =
                  let uu____5012 = p_atomicTermNotQUident e1  in
                  let uu____5013 =
                    let uu____5014 =
                      let uu____5015 =
                        let uu____5016 = p_term false false e2  in
                        soft_parens_with_nesting uu____5016  in
                      let uu____5017 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5015 uu____5017  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5014  in
                  FStar_Pprint.op_Hat_Hat uu____5012 uu____5013  in
                FStar_Pprint.group uu____5011  in
              let uu____5018 =
                let uu____5019 = p_noSeqTerm ps pb e3  in jump2 uu____5019
                 in
              FStar_Pprint.op_Hat_Hat uu____5010 uu____5018  in
            FStar_Pprint.group uu____5009
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5020;_},e1::e2::e3::[])
            ->
            let uu____5026 =
              let uu____5027 =
                let uu____5028 =
                  let uu____5029 = p_atomicTermNotQUident e1  in
                  let uu____5030 =
                    let uu____5031 =
                      let uu____5032 =
                        let uu____5033 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5033  in
                      let uu____5034 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5032 uu____5034  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5031  in
                  FStar_Pprint.op_Hat_Hat uu____5029 uu____5030  in
                FStar_Pprint.group uu____5028  in
              let uu____5035 =
                let uu____5036 = p_noSeqTerm ps pb e3  in jump2 uu____5036
                 in
              FStar_Pprint.op_Hat_Hat uu____5027 uu____5035  in
            FStar_Pprint.group uu____5026
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5044 =
              let uu____5045 = str "requires"  in
              let uu____5046 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5045 uu____5046  in
            FStar_Pprint.group uu____5044
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5054 =
              let uu____5055 = str "ensures"  in
              let uu____5056 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5055 uu____5056  in
            FStar_Pprint.group uu____5054
        | FStar_Parser_AST.Attributes es ->
            let uu____5060 =
              let uu____5061 = str "attributes"  in
              let uu____5062 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5061 uu____5062  in
            FStar_Pprint.group uu____5060
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5066 =
                let uu____5067 =
                  let uu____5068 = str "if"  in
                  let uu____5069 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5068 uu____5069  in
                let uu____5070 =
                  let uu____5071 = str "then"  in
                  let uu____5072 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5071 uu____5072  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5067 uu____5070  in
              FStar_Pprint.group uu____5066
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5075,uu____5076,e31) when
                     is_unit e31 ->
                     let uu____5078 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5078
                 | uu____5079 -> p_noSeqTerm false false e2  in
               let uu____5080 =
                 let uu____5081 =
                   let uu____5082 = str "if"  in
                   let uu____5083 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5082 uu____5083  in
                 let uu____5084 =
                   let uu____5085 =
                     let uu____5086 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5086 e2_doc  in
                   let uu____5087 =
                     let uu____5088 = str "else"  in
                     let uu____5089 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5088 uu____5089  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5085 uu____5087  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5081 uu____5084  in
               FStar_Pprint.group uu____5080)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5112 =
              let uu____5113 =
                let uu____5114 =
                  let uu____5115 = str "try"  in
                  let uu____5116 = p_noSeqTerm false false e1  in
                  prefix2 uu____5115 uu____5116  in
                let uu____5117 =
                  let uu____5118 = str "with"  in
                  let uu____5119 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5118 uu____5119  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5114 uu____5117  in
              FStar_Pprint.group uu____5113  in
            let uu____5128 = paren_if (ps || pb)  in uu____5128 uu____5112
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5155 =
              let uu____5156 =
                let uu____5157 =
                  let uu____5158 = str "match"  in
                  let uu____5159 = p_noSeqTerm false false e1  in
                  let uu____5160 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5158 uu____5159 uu____5160
                   in
                let uu____5161 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5157 uu____5161  in
              FStar_Pprint.group uu____5156  in
            let uu____5170 = paren_if (ps || pb)  in uu____5170 uu____5155
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5177 =
              let uu____5178 =
                let uu____5179 =
                  let uu____5180 = str "let open"  in
                  let uu____5181 = p_quident uid  in
                  let uu____5182 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5180 uu____5181 uu____5182
                   in
                let uu____5183 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5179 uu____5183  in
              FStar_Pprint.group uu____5178  in
            let uu____5184 = paren_if ps  in uu____5184 uu____5177
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5248 is_last =
              match uu____5248 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5281 =
                          let uu____5282 = str "let"  in
                          let uu____5283 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5282 uu____5283
                           in
                        FStar_Pprint.group uu____5281
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5284 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5289 =
                    if is_last
                    then
                      let uu____5290 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5291 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5290 doc_expr uu____5291
                    else
                      (let uu____5293 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5293)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5289
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5339 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5339
                     else
                       (let uu____5347 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5347)) lbs
               in
            let lbs_doc =
              let uu____5355 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5355  in
            let uu____5356 =
              let uu____5357 =
                let uu____5358 =
                  let uu____5359 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5359
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5358  in
              FStar_Pprint.group uu____5357  in
            let uu____5360 = paren_if ps  in uu____5360 uu____5356
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5367;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5370;
                                                             FStar_Parser_AST.level
                                                               = uu____5371;_})
            when matches_var maybe_x x ->
            let uu____5398 =
              let uu____5399 =
                let uu____5400 = str "function"  in
                let uu____5401 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5400 uu____5401  in
              FStar_Pprint.group uu____5399  in
            let uu____5410 = paren_if (ps || pb)  in uu____5410 uu____5398
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5416 =
              let uu____5417 = str "quote"  in
              let uu____5418 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5417 uu____5418  in
            FStar_Pprint.group uu____5416
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5420 =
              let uu____5421 = str "`"  in
              let uu____5422 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5421 uu____5422  in
            FStar_Pprint.group uu____5420
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5424 =
              let uu____5425 = str "`%"  in
              let uu____5426 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5425 uu____5426  in
            FStar_Pprint.group uu____5424
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5428;
              FStar_Parser_AST.level = uu____5429;_}
            ->
            let uu____5430 =
              let uu____5431 = str "`@"  in
              let uu____5432 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5431 uu____5432  in
            FStar_Pprint.group uu____5430
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5434 =
              let uu____5435 = str "`#"  in
              let uu____5436 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5435 uu____5436  in
            FStar_Pprint.group uu____5434
        | uu____5437 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___115_5438  ->
    match uu___115_5438 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5450 =
          let uu____5451 = str "[@"  in
          let uu____5452 =
            let uu____5453 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5454 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5453 uu____5454  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5451 uu____5452  in
        FStar_Pprint.group uu____5450

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
                 let uu____5480 =
                   let uu____5481 =
                     let uu____5482 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5482 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5481 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5480 term_doc
             | pats ->
                 let uu____5488 =
                   let uu____5489 =
                     let uu____5490 =
                       let uu____5491 =
                         let uu____5492 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5492
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5491 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5493 = p_trigger trigger  in
                     prefix2 uu____5490 uu____5493  in
                   FStar_Pprint.group uu____5489  in
                 prefix2 uu____5488 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5513 =
                   let uu____5514 =
                     let uu____5515 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5515 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5514 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5513 term_doc
             | pats ->
                 let uu____5521 =
                   let uu____5522 =
                     let uu____5523 =
                       let uu____5524 =
                         let uu____5525 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5525
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5524 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5526 = p_trigger trigger  in
                     prefix2 uu____5523 uu____5526  in
                   FStar_Pprint.group uu____5522  in
                 prefix2 uu____5521 term_doc)
        | uu____5527 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5529 -> str "forall"
    | FStar_Parser_AST.QExists uu____5542 -> str "exists"
    | uu____5555 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___116_5556  ->
    match uu___116_5556 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5568 =
          let uu____5569 =
            let uu____5570 =
              let uu____5571 = str "pattern"  in
              let uu____5572 =
                let uu____5573 =
                  let uu____5574 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5574
                   in
                FStar_Pprint.op_Hat_Hat uu____5573 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5571 uu____5572  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5570  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5569  in
        FStar_Pprint.group uu____5568

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5580 = str "\\/"  in
    FStar_Pprint.separate_map uu____5580 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5586 =
      let uu____5587 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5587 p_appTerm pats  in
    FStar_Pprint.group uu____5586

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5597 =
              let uu____5598 =
                let uu____5599 = str "fun"  in
                let uu____5600 =
                  let uu____5601 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5601
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5599 uu____5600  in
              let uu____5602 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5598 uu____5602  in
            let uu____5603 = paren_if ps  in uu____5603 uu____5597
        | uu____5608 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5612  ->
      match uu____5612 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5635 =
                    let uu____5636 =
                      let uu____5637 =
                        let uu____5638 = p_tuplePattern p  in
                        let uu____5639 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5638 uu____5639  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5637
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5636  in
                  FStar_Pprint.group uu____5635
              | FStar_Pervasives_Native.Some f ->
                  let uu____5641 =
                    let uu____5642 =
                      let uu____5643 =
                        let uu____5644 =
                          let uu____5645 =
                            let uu____5646 = p_tuplePattern p  in
                            let uu____5647 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5646
                              uu____5647
                             in
                          FStar_Pprint.group uu____5645  in
                        let uu____5648 =
                          let uu____5649 =
                            let uu____5652 = p_tmFormula f  in
                            [uu____5652; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5649  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5644 uu____5648
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5643
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5642  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5641
               in
            let uu____5653 =
              let uu____5654 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5654  in
            FStar_Pprint.group uu____5653  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5663 =
                      let uu____5664 =
                        let uu____5665 =
                          let uu____5666 =
                            let uu____5667 =
                              let uu____5668 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5668  in
                            FStar_Pprint.separate_map uu____5667
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5666
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5665
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5664  in
                    FStar_Pprint.group uu____5663
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5669 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5671;_},e1::e2::[])
        ->
        let uu____5676 = str "<==>"  in
        let uu____5677 = p_tmImplies e1  in
        let uu____5678 = p_tmIff e2  in
        infix0 uu____5676 uu____5677 uu____5678
    | uu____5679 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5681;_},e1::e2::[])
        ->
        let uu____5686 = str "==>"  in
        let uu____5687 = p_tmArrow p_tmFormula e1  in
        let uu____5688 = p_tmImplies e2  in
        infix0 uu____5686 uu____5687 uu____5688
    | uu____5689 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5697 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5697 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5718 ->
               let uu____5719 =
                 let uu____5720 =
                   let uu____5721 =
                     let uu____5722 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5722
                      in
                   FStar_Pprint.separate uu____5721 terms  in
                 let uu____5723 =
                   let uu____5724 =
                     let uu____5725 =
                       let uu____5726 =
                         let uu____5727 =
                           let uu____5728 =
                             let uu____5729 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5729
                              in
                           FStar_Pprint.separate uu____5728 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5727 last_op  in
                       let uu____5730 =
                         let uu____5731 =
                           let uu____5732 =
                             let uu____5733 =
                               let uu____5734 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5734
                                in
                             FStar_Pprint.separate uu____5733 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5732 last_op  in
                         jump2 uu____5731  in
                       FStar_Pprint.ifflat uu____5726 uu____5730  in
                     FStar_Pprint.group uu____5725  in
                   let uu____5735 = FStar_List.hd last1  in
                   prefix2 uu____5724 uu____5735  in
                 FStar_Pprint.ifflat uu____5720 uu____5723  in
               FStar_Pprint.group uu____5719)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5748 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5753 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5748 uu____5753
      | uu____5756 -> let uu____5757 = p_Tm e  in [uu____5757]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5760 =
        let uu____5761 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5761 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5760  in
    let disj =
      let uu____5763 =
        let uu____5764 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5764 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5763  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5783;_},e1::e2::[])
        ->
        let uu____5788 = p_tmDisjunction e1  in
        let uu____5793 = let uu____5798 = p_tmConjunction e2  in [uu____5798]
           in
        FStar_List.append uu____5788 uu____5793
    | uu____5807 -> let uu____5808 = p_tmConjunction e  in [uu____5808]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5818;_},e1::e2::[])
        ->
        let uu____5823 = p_tmConjunction e1  in
        let uu____5826 = let uu____5829 = p_tmTuple e2  in [uu____5829]  in
        FStar_List.append uu____5823 uu____5826
    | uu____5830 -> let uu____5831 = p_tmTuple e  in [uu____5831]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5848 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5848
          (fun uu____5856  ->
             match uu____5856 with | (e1,uu____5862) -> p_tmEq e1) args
    | uu____5863 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5868 =
             let uu____5869 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5869  in
           FStar_Pprint.group uu____5868)

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
               (let uu____5886 = FStar_Ident.text_of_id op  in
                uu____5886 = "="))
              ||
              (let uu____5888 = FStar_Ident.text_of_id op  in
               uu____5888 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5890 = levels op1  in
            (match uu____5890 with
             | (left1,mine,right1) ->
                 let uu____5900 =
                   let uu____5901 = FStar_All.pipe_left str op1  in
                   let uu____5902 = p_tmEqWith' p_X left1 e1  in
                   let uu____5903 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5901 uu____5902 uu____5903  in
                 paren_if_gt curr mine uu____5900)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5904;_},e1::e2::[])
            ->
            let uu____5909 =
              let uu____5910 = p_tmEqWith p_X e1  in
              let uu____5911 =
                let uu____5912 =
                  let uu____5913 =
                    let uu____5914 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5914  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5913  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5912  in
              FStar_Pprint.op_Hat_Hat uu____5910 uu____5911  in
            FStar_Pprint.group uu____5909
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5915;_},e1::[])
            ->
            let uu____5919 = levels "-"  in
            (match uu____5919 with
             | (left1,mine,right1) ->
                 let uu____5929 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5929)
        | uu____5930 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5974)::(e2,uu____5976)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5996 = is_list e  in Prims.op_Negation uu____5996)
              ->
              let op = "::"  in
              let uu____5998 = levels op  in
              (match uu____5998 with
               | (left1,mine,right1) ->
                   let uu____6008 =
                     let uu____6009 = str op  in
                     let uu____6010 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6011 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6009 uu____6010 uu____6011  in
                   paren_if_gt curr mine uu____6008)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6019 = levels op  in
              (match uu____6019 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6035 = p_binder false b  in
                     let uu____6036 =
                       let uu____6037 =
                         let uu____6038 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6038 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6037
                        in
                     FStar_Pprint.op_Hat_Hat uu____6035 uu____6036  in
                   let uu____6039 =
                     let uu____6040 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6041 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6040 uu____6041  in
                   paren_if_gt curr mine uu____6039)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6042;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6067 = levels op  in
              (match uu____6067 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6077 = str op  in
                     let uu____6078 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6079 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6077 uu____6078 uu____6079
                   else
                     (let uu____6081 =
                        let uu____6082 = str op  in
                        let uu____6083 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6084 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6082 uu____6083 uu____6084  in
                      paren_if_gt curr mine uu____6081))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6091 = levels op1  in
              (match uu____6091 with
               | (left1,mine,right1) ->
                   let uu____6101 =
                     let uu____6102 = str op1  in
                     let uu____6103 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6104 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6102 uu____6103 uu____6104  in
                   paren_if_gt curr mine uu____6101)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6123 =
                let uu____6124 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6125 =
                  let uu____6126 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6126 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6124 uu____6125  in
              braces_with_nesting uu____6123
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6131;_},e1::[])
              ->
              let uu____6135 =
                let uu____6136 = str "~"  in
                let uu____6137 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6136 uu____6137  in
              FStar_Pprint.group uu____6135
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6139;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6145 = levels op  in
                   (match uu____6145 with
                    | (left1,mine,right1) ->
                        let uu____6155 =
                          let uu____6156 = str op  in
                          let uu____6157 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6158 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6156 uu____6157 uu____6158  in
                        paren_if_gt curr mine uu____6155)
               | uu____6159 -> p_X e)
          | uu____6160 -> p_X e

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
        let uu____6167 =
          let uu____6168 = p_lident lid  in
          let uu____6169 =
            let uu____6170 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6170  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6168 uu____6169  in
        FStar_Pprint.group uu____6167
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6173 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6175 = p_appTerm e  in
    let uu____6176 =
      let uu____6177 =
        let uu____6178 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6178 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6177  in
    FStar_Pprint.op_Hat_Hat uu____6175 uu____6176

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6183 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6183 t phi
      | FStar_Parser_AST.TAnnotated uu____6184 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6189 ->
          let uu____6190 =
            let uu____6191 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6191
             in
          failwith uu____6190
      | FStar_Parser_AST.TVariable uu____6192 ->
          let uu____6193 =
            let uu____6194 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6194
             in
          failwith uu____6193
      | FStar_Parser_AST.NoName uu____6195 ->
          let uu____6196 =
            let uu____6197 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6197
             in
          failwith uu____6196

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6199  ->
      match uu____6199 with
      | (lid,e) ->
          let uu____6206 =
            let uu____6207 = p_qlident lid  in
            let uu____6208 =
              let uu____6209 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6209
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6207 uu____6208  in
          FStar_Pprint.group uu____6206

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6211 when is_general_application e ->
        let uu____6218 = head_and_args e  in
        (match uu____6218 with
         | (head1,args) ->
             let uu____6243 =
               let uu____6254 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6254
               then
                 let uu____6284 =
                   FStar_Util.take
                     (fun uu____6308  ->
                        match uu____6308 with
                        | (uu____6313,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6284 with
                 | (fs_typ_args,args1) ->
                     let uu____6351 =
                       let uu____6352 = p_indexingTerm head1  in
                       let uu____6353 =
                         let uu____6354 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6354 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6352 uu____6353  in
                     (uu____6351, args1)
               else
                 (let uu____6366 = p_indexingTerm head1  in
                  (uu____6366, args))
                in
             (match uu____6243 with
              | (head_doc,args1) ->
                  let uu____6387 =
                    let uu____6388 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6388 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6387))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6408 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6408)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6426 =
               let uu____6427 = p_quident lid  in
               let uu____6428 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6427 uu____6428  in
             FStar_Pprint.group uu____6426
         | hd1::tl1 ->
             let uu____6445 =
               let uu____6446 =
                 let uu____6447 =
                   let uu____6448 = p_quident lid  in
                   let uu____6449 = p_argTerm hd1  in
                   prefix2 uu____6448 uu____6449  in
                 FStar_Pprint.group uu____6447  in
               let uu____6450 =
                 let uu____6451 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6451  in
               FStar_Pprint.op_Hat_Hat uu____6446 uu____6450  in
             FStar_Pprint.group uu____6445)
    | uu____6456 -> p_indexingTerm e

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
         (let uu____6465 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6465 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6467 = str "#"  in
        let uu____6468 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6467 uu____6468
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6471 = str "#["  in
        let uu____6472 =
          let uu____6473 = p_indexingTerm t  in
          let uu____6474 =
            let uu____6475 = str "]"  in
            let uu____6476 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6475 uu____6476  in
          FStar_Pprint.op_Hat_Hat uu____6473 uu____6474  in
        FStar_Pprint.op_Hat_Hat uu____6471 uu____6472
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6478  ->
    match uu____6478 with | (e,uu____6484) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6489;_},e1::e2::[])
          ->
          let uu____6494 =
            let uu____6495 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6496 =
              let uu____6497 =
                let uu____6498 = p_term false false e2  in
                soft_parens_with_nesting uu____6498  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6497  in
            FStar_Pprint.op_Hat_Hat uu____6495 uu____6496  in
          FStar_Pprint.group uu____6494
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6499;_},e1::e2::[])
          ->
          let uu____6504 =
            let uu____6505 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6506 =
              let uu____6507 =
                let uu____6508 = p_term false false e2  in
                soft_brackets_with_nesting uu____6508  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6507  in
            FStar_Pprint.op_Hat_Hat uu____6505 uu____6506  in
          FStar_Pprint.group uu____6504
      | uu____6509 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6514 = p_quident lid  in
        let uu____6515 =
          let uu____6516 =
            let uu____6517 = p_term false false e1  in
            soft_parens_with_nesting uu____6517  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6516  in
        FStar_Pprint.op_Hat_Hat uu____6514 uu____6515
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6523 =
          let uu____6524 = FStar_Ident.text_of_id op  in str uu____6524  in
        let uu____6525 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6523 uu____6525
    | uu____6526 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assume_lid ->
        str "assume"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____6536 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6543 =
          let uu____6544 = FStar_Ident.text_of_id op  in str uu____6544  in
        let uu____6545 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6543 uu____6545
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6549 =
          let uu____6550 =
            let uu____6551 =
              let uu____6552 = FStar_Ident.text_of_id op  in str uu____6552
               in
            let uu____6553 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6551 uu____6553  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6550  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6549
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6568 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6569 =
          let uu____6570 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6571 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6570 p_tmEq uu____6571  in
        let uu____6578 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6568 uu____6569 uu____6578
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6581 =
          let uu____6582 = p_atomicTermNotQUident e1  in
          let uu____6583 =
            let uu____6584 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6584  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6582 uu____6583
           in
        FStar_Pprint.group uu____6581
    | uu____6585 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6590 = p_quident constr_lid  in
        let uu____6591 =
          let uu____6592 =
            let uu____6593 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6593  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6592  in
        FStar_Pprint.op_Hat_Hat uu____6590 uu____6591
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6595 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6595 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6597 = p_term false false e1  in
        soft_parens_with_nesting uu____6597
    | uu____6598 when is_array e ->
        let es = extract_from_list e  in
        let uu____6602 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6603 =
          let uu____6604 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6604
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6607 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6602 uu____6603 uu____6607
    | uu____6608 when is_list e ->
        let uu____6609 =
          let uu____6610 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6611 = extract_from_list e  in
          separate_map_or_flow_last uu____6610
            (fun ps  -> p_noSeqTerm ps false) uu____6611
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6609 FStar_Pprint.rbracket
    | uu____6616 when is_lex_list e ->
        let uu____6617 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6618 =
          let uu____6619 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6620 = extract_from_list e  in
          separate_map_or_flow_last uu____6619
            (fun ps  -> p_noSeqTerm ps false) uu____6620
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6617 uu____6618 FStar_Pprint.rbracket
    | uu____6625 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6629 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6630 =
          let uu____6631 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6631 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6629 uu____6630 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6635 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6636 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6635 uu____6636
    | FStar_Parser_AST.Op (op,args) when
        let uu____6643 = handleable_op op args  in
        Prims.op_Negation uu____6643 ->
        let uu____6644 =
          let uu____6645 =
            let uu____6646 = FStar_Ident.text_of_id op  in
            let uu____6647 =
              let uu____6648 =
                let uu____6649 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6649
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6648  in
            Prims.strcat uu____6646 uu____6647  in
          Prims.strcat "Operation " uu____6645  in
        failwith uu____6644
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6651 = str "u#"  in
        let uu____6652 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6651 uu____6652
    | FStar_Parser_AST.Wild  ->
        let uu____6653 = p_term false false e  in
        soft_parens_with_nesting uu____6653
    | FStar_Parser_AST.Const uu____6654 ->
        let uu____6655 = p_term false false e  in
        soft_parens_with_nesting uu____6655
    | FStar_Parser_AST.Op uu____6656 ->
        let uu____6663 = p_term false false e  in
        soft_parens_with_nesting uu____6663
    | FStar_Parser_AST.Tvar uu____6664 ->
        let uu____6665 = p_term false false e  in
        soft_parens_with_nesting uu____6665
    | FStar_Parser_AST.Var uu____6666 ->
        let uu____6667 = p_term false false e  in
        soft_parens_with_nesting uu____6667
    | FStar_Parser_AST.Name uu____6668 ->
        let uu____6669 = p_term false false e  in
        soft_parens_with_nesting uu____6669
    | FStar_Parser_AST.Construct uu____6670 ->
        let uu____6681 = p_term false false e  in
        soft_parens_with_nesting uu____6681
    | FStar_Parser_AST.Abs uu____6682 ->
        let uu____6689 = p_term false false e  in
        soft_parens_with_nesting uu____6689
    | FStar_Parser_AST.App uu____6690 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.Let uu____6698 ->
        let uu____6719 = p_term false false e  in
        soft_parens_with_nesting uu____6719
    | FStar_Parser_AST.LetOpen uu____6720 ->
        let uu____6725 = p_term false false e  in
        soft_parens_with_nesting uu____6725
    | FStar_Parser_AST.Seq uu____6726 ->
        let uu____6731 = p_term false false e  in
        soft_parens_with_nesting uu____6731
    | FStar_Parser_AST.Bind uu____6732 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.If uu____6740 ->
        let uu____6747 = p_term false false e  in
        soft_parens_with_nesting uu____6747
    | FStar_Parser_AST.Match uu____6748 ->
        let uu____6763 = p_term false false e  in
        soft_parens_with_nesting uu____6763
    | FStar_Parser_AST.TryWith uu____6764 ->
        let uu____6779 = p_term false false e  in
        soft_parens_with_nesting uu____6779
    | FStar_Parser_AST.Ascribed uu____6780 ->
        let uu____6789 = p_term false false e  in
        soft_parens_with_nesting uu____6789
    | FStar_Parser_AST.Record uu____6790 ->
        let uu____6803 = p_term false false e  in
        soft_parens_with_nesting uu____6803
    | FStar_Parser_AST.Project uu____6804 ->
        let uu____6809 = p_term false false e  in
        soft_parens_with_nesting uu____6809
    | FStar_Parser_AST.Product uu____6810 ->
        let uu____6817 = p_term false false e  in
        soft_parens_with_nesting uu____6817
    | FStar_Parser_AST.Sum uu____6818 ->
        let uu____6825 = p_term false false e  in
        soft_parens_with_nesting uu____6825
    | FStar_Parser_AST.QForall uu____6826 ->
        let uu____6839 = p_term false false e  in
        soft_parens_with_nesting uu____6839
    | FStar_Parser_AST.QExists uu____6840 ->
        let uu____6853 = p_term false false e  in
        soft_parens_with_nesting uu____6853
    | FStar_Parser_AST.Refine uu____6854 ->
        let uu____6859 = p_term false false e  in
        soft_parens_with_nesting uu____6859
    | FStar_Parser_AST.NamedTyp uu____6860 ->
        let uu____6865 = p_term false false e  in
        soft_parens_with_nesting uu____6865
    | FStar_Parser_AST.Requires uu____6866 ->
        let uu____6873 = p_term false false e  in
        soft_parens_with_nesting uu____6873
    | FStar_Parser_AST.Ensures uu____6874 ->
        let uu____6881 = p_term false false e  in
        soft_parens_with_nesting uu____6881
    | FStar_Parser_AST.Attributes uu____6882 ->
        let uu____6885 = p_term false false e  in
        soft_parens_with_nesting uu____6885
    | FStar_Parser_AST.Quote uu____6886 ->
        let uu____6891 = p_term false false e  in
        soft_parens_with_nesting uu____6891
    | FStar_Parser_AST.VQuote uu____6892 ->
        let uu____6893 = p_term false false e  in
        soft_parens_with_nesting uu____6893
    | FStar_Parser_AST.Antiquote uu____6894 ->
        let uu____6895 = p_term false false e  in
        soft_parens_with_nesting uu____6895

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___119_6896  ->
    match uu___119_6896 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6902) ->
        let uu____6903 = str s  in FStar_Pprint.dquotes uu____6903
    | FStar_Const.Const_bytearray (bytes,uu____6905) ->
        let uu____6910 =
          let uu____6911 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6911  in
        let uu____6912 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6910 uu____6912
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___117_6932 =
          match uu___117_6932 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___118_6938 =
          match uu___118_6938 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6949  ->
               match uu____6949 with
               | (s,w) ->
                   let uu____6956 = signedness s  in
                   let uu____6957 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6956 uu____6957)
            sign_width_opt
           in
        let uu____6958 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6958 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6960 = FStar_Range.string_of_range r  in str uu____6960
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6962 = p_quident lid  in
        let uu____6963 =
          let uu____6964 =
            let uu____6965 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6965  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6964  in
        FStar_Pprint.op_Hat_Hat uu____6962 uu____6963

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6967 = str "u#"  in
    let uu____6968 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6967 uu____6968

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6970;_},u1::u2::[])
        ->
        let uu____6975 =
          let uu____6976 = p_universeFrom u1  in
          let uu____6977 =
            let uu____6978 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6978  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6976 uu____6977  in
        FStar_Pprint.group uu____6975
    | FStar_Parser_AST.App uu____6979 ->
        let uu____6986 = head_and_args u  in
        (match uu____6986 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7012 =
                    let uu____7013 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7014 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7022  ->
                           match uu____7022 with
                           | (u1,uu____7028) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7013 uu____7014  in
                  FStar_Pprint.group uu____7012
              | uu____7029 ->
                  let uu____7030 =
                    let uu____7031 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7031
                     in
                  failwith uu____7030))
    | uu____7032 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7055 = FStar_Ident.text_of_id id1  in str uu____7055
    | FStar_Parser_AST.Paren u1 ->
        let uu____7057 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7057
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7058;_},uu____7059::uu____7060::[])
        ->
        let uu____7063 = p_universeFrom u  in
        soft_parens_with_nesting uu____7063
    | FStar_Parser_AST.App uu____7064 ->
        let uu____7071 = p_universeFrom u  in
        soft_parens_with_nesting uu____7071
    | uu____7072 ->
        let uu____7073 =
          let uu____7074 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7074
           in
        failwith uu____7073

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
       | FStar_Parser_AST.Module (uu____7146,decls) ->
           let uu____7152 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7152
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7161,decls,uu____7163) ->
           let uu____7168 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7168
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7221  ->
         match uu____7221 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7237)) -> false
      | ([],uu____7240) -> false
      | uu____7243 -> true  in
    {
      r = (d.FStar_Parser_AST.drange);
      has_qs;
      has_attrs =
        (Prims.op_Negation (FStar_List.isEmpty d.FStar_Parser_AST.attrs));
      has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc);
      is_fsdoc =
        (match d.FStar_Parser_AST.d with
         | FStar_Parser_AST.Fsdoc uu____7251 -> true
         | uu____7252 -> false)
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
        | FStar_Parser_AST.Module (uu____7290,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7296,decls,uu____7298) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7343 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7356;
                 FStar_Parser_AST.doc = uu____7357;
                 FStar_Parser_AST.quals = uu____7358;
                 FStar_Parser_AST.attrs = uu____7359;_}::uu____7360 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7366 =
                   let uu____7369 =
                     let uu____7372 = FStar_List.tl ds  in d :: uu____7372
                      in
                   d0 :: uu____7369  in
                 (uu____7366, (d0.FStar_Parser_AST.drange))
             | uu____7377 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7343 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7431 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7431 dummy_meta
                      FStar_Pprint.empty false true
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7527 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7527, comments1))))))
  