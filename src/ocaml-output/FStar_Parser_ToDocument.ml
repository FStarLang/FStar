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
         (id1,uu____3382)) ->
          let uu____3385 =
            let uu____3386 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3386 FStar_Util.is_upper  in
          if uu____3385
          then
            let uu____3389 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3389 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3391 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3398 =
      FStar_Pprint.optional
        (fun d1  ->
           let uu____3402 = p_fsdoc d1  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3402)
        d.FStar_Parser_AST.doc
       in
    let uu____3403 =
      let uu____3404 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3405 =
        let uu____3406 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3406  in
      FStar_Pprint.op_Hat_Hat uu____3404 uu____3405  in
    FStar_Pprint.op_Hat_Hat uu____3398 uu____3403

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3408 ->
        let uu____3409 =
          let uu____3410 = str "@ "  in
          let uu____3411 =
            let uu____3412 =
              let uu____3413 =
                let uu____3414 =
                  let uu____3415 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3415  in
                FStar_Pprint.op_Hat_Hat uu____3414 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3413  in
            FStar_Pprint.op_Hat_Hat uu____3412 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3410 uu____3411  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3409

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3418  ->
    match uu____3418 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3454 =
                match uu____3454 with
                | (kwd,arg) ->
                    let uu____3461 = str "@"  in
                    let uu____3462 =
                      let uu____3463 = str kwd  in
                      let uu____3464 =
                        let uu____3465 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3465
                         in
                      FStar_Pprint.op_Hat_Hat uu____3463 uu____3464  in
                    FStar_Pprint.op_Hat_Hat uu____3461 uu____3462
                 in
              let uu____3466 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____3466 FStar_Pprint.hardline
           in
        let uu____3471 =
          let uu____3472 =
            let uu____3473 =
              let uu____3474 = str doc1  in
              let uu____3475 =
                let uu____3476 =
                  let uu____3477 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3477  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3476  in
              FStar_Pprint.op_Hat_Hat uu____3474 uu____3475  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3473  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3472  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3471

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3481 =
          let uu____3482 = str "val"  in
          let uu____3483 =
            let uu____3484 =
              let uu____3485 = p_lident lid  in
              let uu____3486 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3485 uu____3486  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3484  in
          FStar_Pprint.op_Hat_Hat uu____3482 uu____3483  in
        let uu____3487 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3481 uu____3487
    | FStar_Parser_AST.TopLevelLet (uu____3488,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3513 =
               let uu____3514 = str "let"  in p_letlhs uu____3514 lb  in
             FStar_Pprint.group uu____3513) lbs
    | uu____3515 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___108_3530 =
          match uu___108_3530 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3538 = f x  in
              let uu____3539 =
                let uu____3540 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3540  in
              FStar_Pprint.op_Hat_Hat uu____3538 uu____3539
           in
        let uu____3541 = str "["  in
        let uu____3542 =
          let uu____3543 = p_list' l  in
          let uu____3544 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3543 uu____3544  in
        FStar_Pprint.op_Hat_Hat uu____3541 uu____3542

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3547 =
          let uu____3548 = str "open"  in
          let uu____3549 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3548 uu____3549  in
        FStar_Pprint.group uu____3547
    | FStar_Parser_AST.Include uid ->
        let uu____3551 =
          let uu____3552 = str "include"  in
          let uu____3553 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3552 uu____3553  in
        FStar_Pprint.group uu____3551
    | FStar_Parser_AST.Friend uid ->
        let uu____3555 =
          let uu____3556 = str "friend"  in
          let uu____3557 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3556 uu____3557  in
        FStar_Pprint.group uu____3555
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3560 =
          let uu____3561 = str "module"  in
          let uu____3562 =
            let uu____3563 =
              let uu____3564 = p_uident uid1  in
              let uu____3565 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3564 uu____3565  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3563  in
          FStar_Pprint.op_Hat_Hat uu____3561 uu____3562  in
        let uu____3566 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3560 uu____3566
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3568 =
          let uu____3569 = str "module"  in
          let uu____3570 =
            let uu____3571 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3571  in
          FStar_Pprint.op_Hat_Hat uu____3569 uu____3570  in
        FStar_Pprint.group uu____3568
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3572,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3605 = str "effect"  in
          let uu____3606 =
            let uu____3607 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3607  in
          FStar_Pprint.op_Hat_Hat uu____3605 uu____3606  in
        let uu____3608 =
          let uu____3609 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3609 FStar_Pprint.equals
           in
        let uu____3610 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3608 uu____3610
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3631 =
          let uu____3632 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3632  in
        let uu____3645 =
          let uu____3646 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3684 =
                    let uu____3685 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3685 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3684)) uu____3646
           in
        FStar_Pprint.op_Hat_Hat uu____3631 uu____3645
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3701 = str "let"  in
          let uu____3702 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3701 uu____3702  in
        let uu____3703 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3703 p_letbinding lbs
          (fun uu____3712  ->
             match uu____3712 with
             | (p,t) ->
                 let uu____3719 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____3719;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc)
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3722 = str "val"  in
        let uu____3723 =
          let uu____3724 =
            let uu____3725 = p_lident lid  in
            let uu____3726 =
              let uu____3727 =
                let uu____3728 =
                  let uu____3729 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3729  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3728  in
              FStar_Pprint.group uu____3727  in
            FStar_Pprint.op_Hat_Hat uu____3725 uu____3726  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3724  in
        FStar_Pprint.op_Hat_Hat uu____3722 uu____3723
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3733 =
            let uu____3734 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3734 FStar_Util.is_upper  in
          if uu____3733
          then FStar_Pprint.empty
          else
            (let uu____3738 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3738 FStar_Pprint.space)
           in
        let uu____3739 =
          let uu____3740 = p_ident id1  in
          let uu____3741 =
            let uu____3742 =
              let uu____3743 =
                let uu____3744 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3744  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3743  in
            FStar_Pprint.group uu____3742  in
          FStar_Pprint.op_Hat_Hat uu____3740 uu____3741  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3739
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3751 = str "exception"  in
        let uu____3752 =
          let uu____3753 =
            let uu____3754 = p_uident uid  in
            let uu____3755 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3759 =
                     let uu____3760 = str "of"  in
                     let uu____3761 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3760 uu____3761  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3759) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3754 uu____3755  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3753  in
        FStar_Pprint.op_Hat_Hat uu____3751 uu____3752
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3763 = str "new_effect"  in
        let uu____3764 =
          let uu____3765 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3765  in
        FStar_Pprint.op_Hat_Hat uu____3763 uu____3764
    | FStar_Parser_AST.SubEffect se ->
        let uu____3767 = str "sub_effect"  in
        let uu____3768 =
          let uu____3769 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3769  in
        FStar_Pprint.op_Hat_Hat uu____3767 uu____3768
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3772 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3772 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3773 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3774,uu____3775) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3798 = str "%splice"  in
        let uu____3799 =
          let uu____3800 =
            let uu____3801 = str ";"  in p_list p_uident uu____3801 ids  in
          let uu____3802 =
            let uu____3803 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3803  in
          FStar_Pprint.op_Hat_Hat uu____3800 uu____3802  in
        FStar_Pprint.op_Hat_Hat uu____3798 uu____3799

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___109_3804  ->
    match uu___109_3804 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3806 = str "#set-options"  in
        let uu____3807 =
          let uu____3808 =
            let uu____3809 = str s  in FStar_Pprint.dquotes uu____3809  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3808  in
        FStar_Pprint.op_Hat_Hat uu____3806 uu____3807
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3813 = str "#reset-options"  in
        let uu____3814 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3818 =
                 let uu____3819 = str s  in FStar_Pprint.dquotes uu____3819
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3818) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3813 uu____3814
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3823 = str "#push-options"  in
        let uu____3824 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3828 =
                 let uu____3829 = str s  in FStar_Pprint.dquotes uu____3829
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3828) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3823 uu____3824
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
    fun uu____3854  ->
      match uu____3854 with
      | (typedecl,fsdoc_opt) ->
          let uu____3867 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3867 with
           | (decl,body) ->
               let uu____3885 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3885)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___110_3887  ->
      match uu___110_3887 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3917 = FStar_Pprint.empty  in
          let uu____3918 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3918, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3939 =
            let uu____3940 = p_typ false false t  in jump2 uu____3940  in
          let uu____3941 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3941, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3995 =
            match uu____3995 with
            | (lid1,t,doc_opt) ->
                let uu____4011 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4011
             in
          let p_fields uu____4027 =
            let uu____4028 =
              let uu____4029 =
                let uu____4030 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4030 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4029  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4028  in
          let uu____4039 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4039, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4100 =
            match uu____4100 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4126 =
                    let uu____4127 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4127  in
                  FStar_Range.extend_to_end_of_line uu____4126  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4153 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4166 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4166,
            ((fun uu____4172  ->
                let uu____4173 = datacon_doc ()  in jump2 uu____4173)))

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
  fun uu____4174  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4174 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4208 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4208  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4210 =
                        let uu____4213 =
                          let uu____4216 = p_fsdoc fsdoc  in
                          let uu____4217 =
                            let uu____4220 = cont lid_doc  in [uu____4220]
                             in
                          uu____4216 :: uu____4217  in
                        kw :: uu____4213  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4210
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4225 =
                        let uu____4226 =
                          let uu____4227 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4227 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4226
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4225
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4242 =
                          let uu____4243 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4243  in
                        prefix2 uu____4242 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4245  ->
      match uu____4245 with
      | (lid,t,doc_opt) ->
          let uu____4261 =
            let uu____4262 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4263 =
              let uu____4264 = p_lident lid  in
              let uu____4265 =
                let uu____4266 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4266  in
              FStar_Pprint.op_Hat_Hat uu____4264 uu____4265  in
            FStar_Pprint.op_Hat_Hat uu____4262 uu____4263  in
          FStar_Pprint.group uu____4261

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4267  ->
    match uu____4267 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4295 =
            let uu____4296 =
              let uu____4297 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4297  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4296  in
          FStar_Pprint.group uu____4295  in
        let uu____4298 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4299 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4303 =
                 let uu____4304 =
                   let uu____4305 =
                     let uu____4306 =
                       let uu____4307 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4307
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4306  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4305  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4304  in
               FStar_Pprint.group uu____4303) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4298 uu____4299

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4309  ->
      match uu____4309 with
      | (pat,uu____4315) ->
          let uu____4316 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4335 =
                  let uu____4336 =
                    let uu____4337 =
                      let uu____4338 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4338
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4337  in
                  FStar_Pprint.group uu____4336  in
                (pat1, uu____4335)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4350 =
                  let uu____4351 =
                    let uu____4352 =
                      let uu____4353 =
                        let uu____4354 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4354
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4353
                       in
                    FStar_Pprint.group uu____4352  in
                  let uu____4355 =
                    let uu____4356 =
                      let uu____4357 = str "by"  in
                      let uu____4358 =
                        let uu____4359 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4359
                         in
                      FStar_Pprint.op_Hat_Hat uu____4357 uu____4358  in
                    FStar_Pprint.group uu____4356  in
                  FStar_Pprint.op_Hat_Hat uu____4351 uu____4355  in
                (pat1, uu____4350)
            | uu____4360 -> (pat, FStar_Pprint.empty)  in
          (match uu____4316 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4364);
                       FStar_Parser_AST.prange = uu____4365;_},pats)
                    ->
                    let uu____4375 =
                      let uu____4376 =
                        let uu____4377 =
                          let uu____4378 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4378  in
                        FStar_Pprint.group uu____4377  in
                      let uu____4379 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4376 uu____4379  in
                    prefix2_nonempty uu____4375 ascr_doc
                | uu____4380 ->
                    let uu____4381 =
                      let uu____4382 =
                        let uu____4383 =
                          let uu____4384 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4384  in
                        FStar_Pprint.group uu____4383  in
                      FStar_Pprint.op_Hat_Hat uu____4382 ascr_doc  in
                    FStar_Pprint.group uu____4381))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4386  ->
      match uu____4386 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4395 =
            let uu____4396 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4396  in
          let uu____4397 =
            let uu____4398 =
              let uu____4399 =
                let uu____4400 =
                  let uu____4401 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4401  in
                FStar_Pprint.group uu____4400  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4399  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4398  in
          FStar_Pprint.ifflat uu____4395 uu____4397

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___111_4402  ->
    match uu___111_4402 with
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
        let uu____4427 = p_uident uid  in
        let uu____4428 = p_binders true bs  in
        let uu____4429 =
          let uu____4430 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4430  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4427 uu____4428 uu____4429

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
          let uu____4440 =
            let uu____4441 =
              let uu____4442 =
                let uu____4443 = p_uident uid  in
                let uu____4444 = p_binders true bs  in
                let uu____4445 =
                  let uu____4446 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4446  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4443 uu____4444 uu____4445
                 in
              FStar_Pprint.group uu____4442  in
            let uu____4447 =
              let uu____4448 = str "with"  in
              let uu____4449 =
                let uu____4450 =
                  let uu____4451 =
                    let uu____4452 =
                      let uu____4453 =
                        let uu____4454 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4454
                         in
                      separate_map_last uu____4453 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4452  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4451  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4450  in
              FStar_Pprint.op_Hat_Hat uu____4448 uu____4449  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4441 uu____4447  in
          braces_with_nesting uu____4440

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4457,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4486 =
            let uu____4487 = p_lident lid  in
            let uu____4488 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4487 uu____4488  in
          let uu____4489 = p_simpleTerm ps false e  in
          prefix2 uu____4486 uu____4489
      | uu____4490 ->
          let uu____4491 =
            let uu____4492 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4492
             in
          failwith uu____4491

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4554 =
        match uu____4554 with
        | (kwd,t) ->
            let uu____4561 =
              let uu____4562 = str kwd  in
              let uu____4563 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4562 uu____4563  in
            let uu____4564 = p_simpleTerm ps false t  in
            prefix2 uu____4561 uu____4564
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4569 =
      let uu____4570 =
        let uu____4571 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4572 =
          let uu____4573 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4573  in
        FStar_Pprint.op_Hat_Hat uu____4571 uu____4572  in
      let uu____4574 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4570 uu____4574  in
    let uu____4575 =
      let uu____4576 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4576  in
    FStar_Pprint.op_Hat_Hat uu____4569 uu____4575

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___112_4577  ->
    match uu___112_4577 with
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
        let uu____4580 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4580 FStar_Pprint.hardline
    | uu____4581 ->
        let uu____4582 =
          let uu____4583 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4583  in
        FStar_Pprint.op_Hat_Hat uu____4582 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___113_4586  ->
    match uu___113_4586 with
    | FStar_Parser_AST.Rec  ->
        let uu____4587 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4587
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___114_4588  ->
    match uu___114_4588 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4590 = str "#["  in
        let uu____4591 =
          let uu____4592 = p_term false false t  in
          let uu____4593 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4592 uu____4593  in
        FStar_Pprint.op_Hat_Hat uu____4590 uu____4591

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4598 =
          let uu____4599 =
            let uu____4600 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4600  in
          FStar_Pprint.separate_map uu____4599 p_tuplePattern pats  in
        FStar_Pprint.group uu____4598
    | uu____4601 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4608 =
          let uu____4609 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4609 p_constructorPattern pats  in
        FStar_Pprint.group uu____4608
    | uu____4610 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4613;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4618 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4619 = p_constructorPattern hd1  in
        let uu____4620 = p_constructorPattern tl1  in
        infix0 uu____4618 uu____4619 uu____4620
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4622;_},pats)
        ->
        let uu____4628 = p_quident uid  in
        let uu____4629 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4628 uu____4629
    | uu____4630 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4646;
               FStar_Parser_AST.blevel = uu____4647;
               FStar_Parser_AST.aqual = uu____4648;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4656 =
               let uu____4657 = p_ident lid  in
               p_refinement aqual uu____4657 t1 phi  in
             soft_parens_with_nesting uu____4656
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4660;
               FStar_Parser_AST.blevel = uu____4661;
               FStar_Parser_AST.aqual = uu____4662;_},phi))
             ->
             let uu____4668 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4668
         | uu____4669 ->
             let uu____4674 =
               let uu____4675 = p_tuplePattern pat  in
               let uu____4676 =
                 let uu____4677 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4677
                  in
               FStar_Pprint.op_Hat_Hat uu____4675 uu____4676  in
             soft_parens_with_nesting uu____4674)
    | FStar_Parser_AST.PatList pats ->
        let uu____4681 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4681 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4698 =
          match uu____4698 with
          | (lid,pat) ->
              let uu____4705 = p_qlident lid  in
              let uu____4706 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4705 uu____4706
           in
        let uu____4707 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4707
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4717 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4718 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4719 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4717 uu____4718 uu____4719
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4728 =
          let uu____4729 =
            let uu____4730 =
              let uu____4731 = FStar_Ident.text_of_id op  in str uu____4731
               in
            let uu____4732 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4730 uu____4732  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4729  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4728
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4736 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4736 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4744 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4745 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4744 uu____4745
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4747 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4750;
           FStar_Parser_AST.prange = uu____4751;_},uu____4752)
        ->
        let uu____4757 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4757
    | FStar_Parser_AST.PatTuple (uu____4758,false ) ->
        let uu____4763 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4763
    | uu____4764 ->
        let uu____4765 =
          let uu____4766 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4766  in
        failwith uu____4765

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4768;_},uu____4769)
        -> true
    | uu____4774 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4778 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4779 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4778 uu____4779
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4786;
                   FStar_Parser_AST.blevel = uu____4787;
                   FStar_Parser_AST.aqual = uu____4788;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4792 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4792 t1 phi
            | uu____4793 ->
                let t' =
                  let uu____4795 = is_typ_tuple t  in
                  if uu____4795
                  then
                    let uu____4796 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4796
                  else p_tmFormula t  in
                let uu____4798 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4799 =
                  let uu____4800 = p_lident lid  in
                  let uu____4801 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4800 uu____4801  in
                FStar_Pprint.op_Hat_Hat uu____4798 uu____4799
             in
          if is_atomic
          then
            let uu____4802 =
              let uu____4803 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4803  in
            FStar_Pprint.group uu____4802
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4805 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4812;
                  FStar_Parser_AST.blevel = uu____4813;
                  FStar_Parser_AST.aqual = uu____4814;_},phi)
               ->
               if is_atomic
               then
                 let uu____4818 =
                   let uu____4819 =
                     let uu____4820 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4820 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4819  in
                 FStar_Pprint.group uu____4818
               else
                 (let uu____4822 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4822)
           | uu____4823 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4832 -> false
            | FStar_Parser_AST.App uu____4843 -> false
            | FStar_Parser_AST.Op uu____4850 -> false
            | uu____4857 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4861 =
            let uu____4862 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4863 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4862 uu____4863  in
          let uu____4864 =
            let uu____4865 = p_appTerm t  in
            let uu____4866 =
              let uu____4867 =
                let uu____4868 =
                  let uu____4869 = soft_braces_with_nesting_tight phi1  in
                  let uu____4870 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4869 uu____4870  in
                FStar_Pprint.group uu____4868  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4867
               in
            FStar_Pprint.op_Hat_Hat uu____4865 uu____4866  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4861 uu____4864

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4881 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4881

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4886 = FStar_Ident.text_of_id lid  in str uu____4886)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4889 = FStar_Ident.text_of_lid lid  in str uu____4889)

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
            let uu____4907 =
              let uu____4908 =
                let uu____4909 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4909 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4908  in
            let uu____4910 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4907 uu____4910
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4914 =
              let uu____4915 =
                let uu____4916 =
                  let uu____4917 = p_lident x  in
                  let uu____4918 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4917 uu____4918  in
                let uu____4919 =
                  let uu____4920 = p_noSeqTerm true false e1  in
                  let uu____4921 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4920 uu____4921  in
                op_Hat_Slash_Plus_Hat uu____4916 uu____4919  in
              FStar_Pprint.group uu____4915  in
            let uu____4922 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4914 uu____4922
        | uu____4923 ->
            let uu____4924 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4924

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
            let uu____4935 =
              let uu____4936 = p_tmIff e1  in
              let uu____4937 =
                let uu____4938 =
                  let uu____4939 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4939
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4938  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4936 uu____4937  in
            FStar_Pprint.group uu____4935
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4945 =
              let uu____4946 = p_tmIff e1  in
              let uu____4947 =
                let uu____4948 =
                  let uu____4949 =
                    let uu____4950 = p_typ false false t  in
                    let uu____4951 =
                      let uu____4952 = str "by"  in
                      let uu____4953 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4952 uu____4953  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4950 uu____4951  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4949
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4948  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4946 uu____4947  in
            FStar_Pprint.group uu____4945
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
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
                        soft_parens_with_nesting uu____4967  in
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
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4971;_},e1::e2::e3::[])
            ->
            let uu____4977 =
              let uu____4978 =
                let uu____4979 =
                  let uu____4980 = p_atomicTermNotQUident e1  in
                  let uu____4981 =
                    let uu____4982 =
                      let uu____4983 =
                        let uu____4984 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4984  in
                      let uu____4985 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4983 uu____4985  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4982  in
                  FStar_Pprint.op_Hat_Hat uu____4980 uu____4981  in
                FStar_Pprint.group uu____4979  in
              let uu____4986 =
                let uu____4987 = p_noSeqTerm ps pb e3  in jump2 uu____4987
                 in
              FStar_Pprint.op_Hat_Hat uu____4978 uu____4986  in
            FStar_Pprint.group uu____4977
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4995 =
              let uu____4996 = str "requires"  in
              let uu____4997 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4996 uu____4997  in
            FStar_Pprint.group uu____4995
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5005 =
              let uu____5006 = str "ensures"  in
              let uu____5007 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5006 uu____5007  in
            FStar_Pprint.group uu____5005
        | FStar_Parser_AST.Attributes es ->
            let uu____5011 =
              let uu____5012 = str "attributes"  in
              let uu____5013 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5012 uu____5013  in
            FStar_Pprint.group uu____5011
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5017 =
                let uu____5018 =
                  let uu____5019 = str "if"  in
                  let uu____5020 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5019 uu____5020  in
                let uu____5021 =
                  let uu____5022 = str "then"  in
                  let uu____5023 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5022 uu____5023  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5021  in
              FStar_Pprint.group uu____5017
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5026,uu____5027,e31) when
                     is_unit e31 ->
                     let uu____5029 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5029
                 | uu____5030 -> p_noSeqTerm false false e2  in
               let uu____5031 =
                 let uu____5032 =
                   let uu____5033 = str "if"  in
                   let uu____5034 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5033 uu____5034  in
                 let uu____5035 =
                   let uu____5036 =
                     let uu____5037 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5037 e2_doc  in
                   let uu____5038 =
                     let uu____5039 = str "else"  in
                     let uu____5040 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5039 uu____5040  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5036 uu____5038  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5032 uu____5035  in
               FStar_Pprint.group uu____5031)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5063 =
              let uu____5064 =
                let uu____5065 =
                  let uu____5066 = str "try"  in
                  let uu____5067 = p_noSeqTerm false false e1  in
                  prefix2 uu____5066 uu____5067  in
                let uu____5068 =
                  let uu____5069 = str "with"  in
                  let uu____5070 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5069 uu____5070  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5065 uu____5068  in
              FStar_Pprint.group uu____5064  in
            let uu____5079 = paren_if (ps || pb)  in uu____5079 uu____5063
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5106 =
              let uu____5107 =
                let uu____5108 =
                  let uu____5109 = str "match"  in
                  let uu____5110 = p_noSeqTerm false false e1  in
                  let uu____5111 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5109 uu____5110 uu____5111
                   in
                let uu____5112 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5108 uu____5112  in
              FStar_Pprint.group uu____5107  in
            let uu____5121 = paren_if (ps || pb)  in uu____5121 uu____5106
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5128 =
              let uu____5129 =
                let uu____5130 =
                  let uu____5131 = str "let open"  in
                  let uu____5132 = p_quident uid  in
                  let uu____5133 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5131 uu____5132 uu____5133
                   in
                let uu____5134 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5130 uu____5134  in
              FStar_Pprint.group uu____5129  in
            let uu____5135 = paren_if ps  in uu____5135 uu____5128
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5199 is_last =
              match uu____5199 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5232 =
                          let uu____5233 = str "let"  in
                          let uu____5234 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5233 uu____5234
                           in
                        FStar_Pprint.group uu____5232
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5235 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5240 =
                    if is_last
                    then
                      let uu____5241 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5242 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5241 doc_expr uu____5242
                    else
                      (let uu____5244 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5244)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5240
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5290 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5290
                     else
                       (let uu____5298 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5298)) lbs
               in
            let lbs_doc =
              let uu____5306 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5306  in
            let uu____5307 =
              let uu____5308 =
                let uu____5309 =
                  let uu____5310 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5310
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5309  in
              FStar_Pprint.group uu____5308  in
            let uu____5311 = paren_if ps  in uu____5311 uu____5307
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5318;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5321;
                                                             FStar_Parser_AST.level
                                                               = uu____5322;_})
            when matches_var maybe_x x ->
            let uu____5349 =
              let uu____5350 =
                let uu____5351 = str "function"  in
                let uu____5352 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5351 uu____5352  in
              FStar_Pprint.group uu____5350  in
            let uu____5361 = paren_if (ps || pb)  in uu____5361 uu____5349
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5367 =
              let uu____5368 = str "quote"  in
              let uu____5369 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5368 uu____5369  in
            FStar_Pprint.group uu____5367
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5371 =
              let uu____5372 = str "`"  in
              let uu____5373 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5372 uu____5373  in
            FStar_Pprint.group uu____5371
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5375 =
              let uu____5376 = str "`%"  in
              let uu____5377 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5376 uu____5377  in
            FStar_Pprint.group uu____5375
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5379;
              FStar_Parser_AST.level = uu____5380;_}
            ->
            let uu____5381 =
              let uu____5382 = str "`@"  in
              let uu____5383 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5382 uu____5383  in
            FStar_Pprint.group uu____5381
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5385 =
              let uu____5386 = str "`#"  in
              let uu____5387 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5386 uu____5387  in
            FStar_Pprint.group uu____5385
        | uu____5388 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___115_5389  ->
    match uu___115_5389 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5401 =
          let uu____5402 = str "[@"  in
          let uu____5403 =
            let uu____5404 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5405 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5404 uu____5405  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5402 uu____5403  in
        FStar_Pprint.group uu____5401

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
                 let uu____5431 =
                   let uu____5432 =
                     let uu____5433 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5433 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5432 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5431 term_doc
             | pats ->
                 let uu____5439 =
                   let uu____5440 =
                     let uu____5441 =
                       let uu____5442 =
                         let uu____5443 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5443
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5442 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5444 = p_trigger trigger  in
                     prefix2 uu____5441 uu____5444  in
                   FStar_Pprint.group uu____5440  in
                 prefix2 uu____5439 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5464 =
                   let uu____5465 =
                     let uu____5466 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5466 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5465 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5464 term_doc
             | pats ->
                 let uu____5472 =
                   let uu____5473 =
                     let uu____5474 =
                       let uu____5475 =
                         let uu____5476 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5476
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5475 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5477 = p_trigger trigger  in
                     prefix2 uu____5474 uu____5477  in
                   FStar_Pprint.group uu____5473  in
                 prefix2 uu____5472 term_doc)
        | uu____5478 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5480 -> str "forall"
    | FStar_Parser_AST.QExists uu____5493 -> str "exists"
    | uu____5506 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___116_5507  ->
    match uu___116_5507 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5519 =
          let uu____5520 =
            let uu____5521 =
              let uu____5522 = str "pattern"  in
              let uu____5523 =
                let uu____5524 =
                  let uu____5525 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5525
                   in
                FStar_Pprint.op_Hat_Hat uu____5524 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5522 uu____5523  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5521  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5520  in
        FStar_Pprint.group uu____5519

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5531 = str "\\/"  in
    FStar_Pprint.separate_map uu____5531 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5537 =
      let uu____5538 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5538 p_appTerm pats  in
    FStar_Pprint.group uu____5537

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5548 =
              let uu____5549 =
                let uu____5550 = str "fun"  in
                let uu____5551 =
                  let uu____5552 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5552
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5550 uu____5551  in
              let uu____5553 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5549 uu____5553  in
            let uu____5554 = paren_if ps  in uu____5554 uu____5548
        | uu____5559 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5563  ->
      match uu____5563 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5586 =
                    let uu____5587 =
                      let uu____5588 =
                        let uu____5589 = p_tuplePattern p  in
                        let uu____5590 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5589 uu____5590  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5588
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5587  in
                  FStar_Pprint.group uu____5586
              | FStar_Pervasives_Native.Some f ->
                  let uu____5592 =
                    let uu____5593 =
                      let uu____5594 =
                        let uu____5595 =
                          let uu____5596 =
                            let uu____5597 = p_tuplePattern p  in
                            let uu____5598 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5597
                              uu____5598
                             in
                          FStar_Pprint.group uu____5596  in
                        let uu____5599 =
                          let uu____5600 =
                            let uu____5603 = p_tmFormula f  in
                            [uu____5603; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5600  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5595 uu____5599
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5594
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5593  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5592
               in
            let uu____5604 =
              let uu____5605 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5605  in
            FStar_Pprint.group uu____5604  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5614 =
                      let uu____5615 =
                        let uu____5616 =
                          let uu____5617 =
                            let uu____5618 =
                              let uu____5619 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5619  in
                            FStar_Pprint.separate_map uu____5618
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5617
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5616
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5615  in
                    FStar_Pprint.group uu____5614
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5620 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5622;_},e1::e2::[])
        ->
        let uu____5627 = str "<==>"  in
        let uu____5628 = p_tmImplies e1  in
        let uu____5629 = p_tmIff e2  in
        infix0 uu____5627 uu____5628 uu____5629
    | uu____5630 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5632;_},e1::e2::[])
        ->
        let uu____5637 = str "==>"  in
        let uu____5638 = p_tmArrow p_tmFormula e1  in
        let uu____5639 = p_tmImplies e2  in
        infix0 uu____5637 uu____5638 uu____5639
    | uu____5640 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5648 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5648 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5669 ->
               let uu____5670 =
                 let uu____5671 =
                   let uu____5672 =
                     let uu____5673 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5673
                      in
                   FStar_Pprint.separate uu____5672 terms  in
                 let uu____5674 =
                   let uu____5675 =
                     let uu____5676 =
                       let uu____5677 =
                         let uu____5678 =
                           let uu____5679 =
                             let uu____5680 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5680
                              in
                           FStar_Pprint.separate uu____5679 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5678 last_op  in
                       let uu____5681 =
                         let uu____5682 =
                           let uu____5683 =
                             let uu____5684 =
                               let uu____5685 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5685
                                in
                             FStar_Pprint.separate uu____5684 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5683 last_op  in
                         jump2 uu____5682  in
                       FStar_Pprint.ifflat uu____5677 uu____5681  in
                     FStar_Pprint.group uu____5676  in
                   let uu____5686 = FStar_List.hd last1  in
                   prefix2 uu____5675 uu____5686  in
                 FStar_Pprint.ifflat uu____5671 uu____5674  in
               FStar_Pprint.group uu____5670)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5699 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5704 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5699 uu____5704
      | uu____5707 -> let uu____5708 = p_Tm e  in [uu____5708]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5711 =
        let uu____5712 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5712 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5711  in
    let disj =
      let uu____5714 =
        let uu____5715 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5715 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5714  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5734;_},e1::e2::[])
        ->
        let uu____5739 = p_tmDisjunction e1  in
        let uu____5744 = let uu____5749 = p_tmConjunction e2  in [uu____5749]
           in
        FStar_List.append uu____5739 uu____5744
    | uu____5758 -> let uu____5759 = p_tmConjunction e  in [uu____5759]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5769;_},e1::e2::[])
        ->
        let uu____5774 = p_tmConjunction e1  in
        let uu____5777 = let uu____5780 = p_tmTuple e2  in [uu____5780]  in
        FStar_List.append uu____5774 uu____5777
    | uu____5781 -> let uu____5782 = p_tmTuple e  in [uu____5782]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5799 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5799
          (fun uu____5807  ->
             match uu____5807 with | (e1,uu____5813) -> p_tmEq e1) args
    | uu____5814 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5819 =
             let uu____5820 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5820  in
           FStar_Pprint.group uu____5819)

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
               (let uu____5837 = FStar_Ident.text_of_id op  in
                uu____5837 = "="))
              ||
              (let uu____5839 = FStar_Ident.text_of_id op  in
               uu____5839 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5841 = levels op1  in
            (match uu____5841 with
             | (left1,mine,right1) ->
                 let uu____5851 =
                   let uu____5852 = FStar_All.pipe_left str op1  in
                   let uu____5853 = p_tmEqWith' p_X left1 e1  in
                   let uu____5854 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5852 uu____5853 uu____5854  in
                 paren_if_gt curr mine uu____5851)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5855;_},e1::e2::[])
            ->
            let uu____5860 =
              let uu____5861 = p_tmEqWith p_X e1  in
              let uu____5862 =
                let uu____5863 =
                  let uu____5864 =
                    let uu____5865 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5865  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5864  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5863  in
              FStar_Pprint.op_Hat_Hat uu____5861 uu____5862  in
            FStar_Pprint.group uu____5860
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5866;_},e1::[])
            ->
            let uu____5870 = levels "-"  in
            (match uu____5870 with
             | (left1,mine,right1) ->
                 let uu____5880 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5880)
        | uu____5881 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5925)::(e2,uu____5927)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5947 = is_list e  in Prims.op_Negation uu____5947)
              ->
              let op = "::"  in
              let uu____5949 = levels op  in
              (match uu____5949 with
               | (left1,mine,right1) ->
                   let uu____5959 =
                     let uu____5960 = str op  in
                     let uu____5961 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5962 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5960 uu____5961 uu____5962  in
                   paren_if_gt curr mine uu____5959)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5970 = levels op  in
              (match uu____5970 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5986 = p_binder false b  in
                     let uu____5987 =
                       let uu____5988 =
                         let uu____5989 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5989 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5988
                        in
                     FStar_Pprint.op_Hat_Hat uu____5986 uu____5987  in
                   let uu____5990 =
                     let uu____5991 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5992 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5991 uu____5992  in
                   paren_if_gt curr mine uu____5990)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5993;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6018 = levels op  in
              (match uu____6018 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6028 = str op  in
                     let uu____6029 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6030 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6028 uu____6029 uu____6030
                   else
                     (let uu____6032 =
                        let uu____6033 = str op  in
                        let uu____6034 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6035 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6033 uu____6034 uu____6035  in
                      paren_if_gt curr mine uu____6032))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6042 = levels op1  in
              (match uu____6042 with
               | (left1,mine,right1) ->
                   let uu____6052 =
                     let uu____6053 = str op1  in
                     let uu____6054 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6055 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6053 uu____6054 uu____6055  in
                   paren_if_gt curr mine uu____6052)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6074 =
                let uu____6075 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6076 =
                  let uu____6077 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6077 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6075 uu____6076  in
              braces_with_nesting uu____6074
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6082;_},e1::[])
              ->
              let uu____6086 =
                let uu____6087 = str "~"  in
                let uu____6088 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6087 uu____6088  in
              FStar_Pprint.group uu____6086
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6090;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6096 = levels op  in
                   (match uu____6096 with
                    | (left1,mine,right1) ->
                        let uu____6106 =
                          let uu____6107 = str op  in
                          let uu____6108 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6109 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6107 uu____6108 uu____6109  in
                        paren_if_gt curr mine uu____6106)
               | uu____6110 -> p_X e)
          | uu____6111 -> p_X e

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
        let uu____6118 =
          let uu____6119 = p_lident lid  in
          let uu____6120 =
            let uu____6121 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6121  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6119 uu____6120  in
        FStar_Pprint.group uu____6118
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6124 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6126 = p_appTerm e  in
    let uu____6127 =
      let uu____6128 =
        let uu____6129 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6129 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6128  in
    FStar_Pprint.op_Hat_Hat uu____6126 uu____6127

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6134 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6134 t phi
      | FStar_Parser_AST.TAnnotated uu____6135 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6140 ->
          let uu____6141 =
            let uu____6142 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6142
             in
          failwith uu____6141
      | FStar_Parser_AST.TVariable uu____6143 ->
          let uu____6144 =
            let uu____6145 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6145
             in
          failwith uu____6144
      | FStar_Parser_AST.NoName uu____6146 ->
          let uu____6147 =
            let uu____6148 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6148
             in
          failwith uu____6147

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6150  ->
      match uu____6150 with
      | (lid,e) ->
          let uu____6157 =
            let uu____6158 = p_qlident lid  in
            let uu____6159 =
              let uu____6160 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6160
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6158 uu____6159  in
          FStar_Pprint.group uu____6157

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6162 when is_general_application e ->
        let uu____6169 = head_and_args e  in
        (match uu____6169 with
         | (head1,args) ->
             let uu____6194 =
               let uu____6205 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6205
               then
                 let uu____6235 =
                   FStar_Util.take
                     (fun uu____6259  ->
                        match uu____6259 with
                        | (uu____6264,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6235 with
                 | (fs_typ_args,args1) ->
                     let uu____6302 =
                       let uu____6303 = p_indexingTerm head1  in
                       let uu____6304 =
                         let uu____6305 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6305 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6303 uu____6304  in
                     (uu____6302, args1)
               else
                 (let uu____6317 = p_indexingTerm head1  in
                  (uu____6317, args))
                in
             (match uu____6194 with
              | (head_doc,args1) ->
                  let uu____6338 =
                    let uu____6339 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6339 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6338))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6359 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6359)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6377 =
               let uu____6378 = p_quident lid  in
               let uu____6379 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6378 uu____6379  in
             FStar_Pprint.group uu____6377
         | hd1::tl1 ->
             let uu____6396 =
               let uu____6397 =
                 let uu____6398 =
                   let uu____6399 = p_quident lid  in
                   let uu____6400 = p_argTerm hd1  in
                   prefix2 uu____6399 uu____6400  in
                 FStar_Pprint.group uu____6398  in
               let uu____6401 =
                 let uu____6402 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6402  in
               FStar_Pprint.op_Hat_Hat uu____6397 uu____6401  in
             FStar_Pprint.group uu____6396)
    | uu____6407 -> p_indexingTerm e

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
         (let uu____6416 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6416 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6418 = str "#"  in
        let uu____6419 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6418 uu____6419
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6422 = str "#["  in
        let uu____6423 =
          let uu____6424 = p_indexingTerm t  in
          let uu____6425 =
            let uu____6426 = str "]"  in
            let uu____6427 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6426 uu____6427  in
          FStar_Pprint.op_Hat_Hat uu____6424 uu____6425  in
        FStar_Pprint.op_Hat_Hat uu____6422 uu____6423
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6429  ->
    match uu____6429 with | (e,uu____6435) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6440;_},e1::e2::[])
          ->
          let uu____6445 =
            let uu____6446 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6447 =
              let uu____6448 =
                let uu____6449 = p_term false false e2  in
                soft_parens_with_nesting uu____6449  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6448  in
            FStar_Pprint.op_Hat_Hat uu____6446 uu____6447  in
          FStar_Pprint.group uu____6445
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6450;_},e1::e2::[])
          ->
          let uu____6455 =
            let uu____6456 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6457 =
              let uu____6458 =
                let uu____6459 = p_term false false e2  in
                soft_brackets_with_nesting uu____6459  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6458  in
            FStar_Pprint.op_Hat_Hat uu____6456 uu____6457  in
          FStar_Pprint.group uu____6455
      | uu____6460 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6465 = p_quident lid  in
        let uu____6466 =
          let uu____6467 =
            let uu____6468 = p_term false false e1  in
            soft_parens_with_nesting uu____6468  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6467  in
        FStar_Pprint.op_Hat_Hat uu____6465 uu____6466
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6474 =
          let uu____6475 = FStar_Ident.text_of_id op  in str uu____6475  in
        let uu____6476 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6474 uu____6476
    | uu____6477 -> p_atomicTermNotQUident e

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
         | uu____6486 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6493 =
          let uu____6494 = FStar_Ident.text_of_id op  in str uu____6494  in
        let uu____6495 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6493 uu____6495
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6499 =
          let uu____6500 =
            let uu____6501 =
              let uu____6502 = FStar_Ident.text_of_id op  in str uu____6502
               in
            let uu____6503 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6501 uu____6503  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6500  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6499
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6518 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6519 =
          let uu____6520 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6521 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6520 p_tmEq uu____6521  in
        let uu____6528 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6518 uu____6519 uu____6528
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6531 =
          let uu____6532 = p_atomicTermNotQUident e1  in
          let uu____6533 =
            let uu____6534 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6534  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6532 uu____6533
           in
        FStar_Pprint.group uu____6531
    | uu____6535 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6540 = p_quident constr_lid  in
        let uu____6541 =
          let uu____6542 =
            let uu____6543 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6543  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6542  in
        FStar_Pprint.op_Hat_Hat uu____6540 uu____6541
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6545 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6545 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6547 = p_term false false e1  in
        soft_parens_with_nesting uu____6547
    | uu____6548 when is_array e ->
        let es = extract_from_list e  in
        let uu____6552 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6553 =
          let uu____6554 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6554
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6557 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6552 uu____6553 uu____6557
    | uu____6558 when is_list e ->
        let uu____6559 =
          let uu____6560 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6561 = extract_from_list e  in
          separate_map_or_flow_last uu____6560
            (fun ps  -> p_noSeqTerm ps false) uu____6561
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6559 FStar_Pprint.rbracket
    | uu____6566 when is_lex_list e ->
        let uu____6567 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6568 =
          let uu____6569 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6570 = extract_from_list e  in
          separate_map_or_flow_last uu____6569
            (fun ps  -> p_noSeqTerm ps false) uu____6570
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6567 uu____6568 FStar_Pprint.rbracket
    | uu____6575 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6579 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6580 =
          let uu____6581 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6581 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6579 uu____6580 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6585 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6586 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6585 uu____6586
    | FStar_Parser_AST.Op (op,args) when
        let uu____6593 = handleable_op op args  in
        Prims.op_Negation uu____6593 ->
        let uu____6594 =
          let uu____6595 =
            let uu____6596 = FStar_Ident.text_of_id op  in
            let uu____6597 =
              let uu____6598 =
                let uu____6599 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6599
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6598  in
            Prims.strcat uu____6596 uu____6597  in
          Prims.strcat "Operation " uu____6595  in
        failwith uu____6594
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6601 = str "u#"  in
        let uu____6602 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6601 uu____6602
    | FStar_Parser_AST.Wild  ->
        let uu____6603 = p_term false false e  in
        soft_parens_with_nesting uu____6603
    | FStar_Parser_AST.Const uu____6604 ->
        let uu____6605 = p_term false false e  in
        soft_parens_with_nesting uu____6605
    | FStar_Parser_AST.Op uu____6606 ->
        let uu____6613 = p_term false false e  in
        soft_parens_with_nesting uu____6613
    | FStar_Parser_AST.Tvar uu____6614 ->
        let uu____6615 = p_term false false e  in
        soft_parens_with_nesting uu____6615
    | FStar_Parser_AST.Var uu____6616 ->
        let uu____6617 = p_term false false e  in
        soft_parens_with_nesting uu____6617
    | FStar_Parser_AST.Name uu____6618 ->
        let uu____6619 = p_term false false e  in
        soft_parens_with_nesting uu____6619
    | FStar_Parser_AST.Construct uu____6620 ->
        let uu____6631 = p_term false false e  in
        soft_parens_with_nesting uu____6631
    | FStar_Parser_AST.Abs uu____6632 ->
        let uu____6639 = p_term false false e  in
        soft_parens_with_nesting uu____6639
    | FStar_Parser_AST.App uu____6640 ->
        let uu____6647 = p_term false false e  in
        soft_parens_with_nesting uu____6647
    | FStar_Parser_AST.Let uu____6648 ->
        let uu____6669 = p_term false false e  in
        soft_parens_with_nesting uu____6669
    | FStar_Parser_AST.LetOpen uu____6670 ->
        let uu____6675 = p_term false false e  in
        soft_parens_with_nesting uu____6675
    | FStar_Parser_AST.Seq uu____6676 ->
        let uu____6681 = p_term false false e  in
        soft_parens_with_nesting uu____6681
    | FStar_Parser_AST.Bind uu____6682 ->
        let uu____6689 = p_term false false e  in
        soft_parens_with_nesting uu____6689
    | FStar_Parser_AST.If uu____6690 ->
        let uu____6697 = p_term false false e  in
        soft_parens_with_nesting uu____6697
    | FStar_Parser_AST.Match uu____6698 ->
        let uu____6713 = p_term false false e  in
        soft_parens_with_nesting uu____6713
    | FStar_Parser_AST.TryWith uu____6714 ->
        let uu____6729 = p_term false false e  in
        soft_parens_with_nesting uu____6729
    | FStar_Parser_AST.Ascribed uu____6730 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.Record uu____6740 ->
        let uu____6753 = p_term false false e  in
        soft_parens_with_nesting uu____6753
    | FStar_Parser_AST.Project uu____6754 ->
        let uu____6759 = p_term false false e  in
        soft_parens_with_nesting uu____6759
    | FStar_Parser_AST.Product uu____6760 ->
        let uu____6767 = p_term false false e  in
        soft_parens_with_nesting uu____6767
    | FStar_Parser_AST.Sum uu____6768 ->
        let uu____6775 = p_term false false e  in
        soft_parens_with_nesting uu____6775
    | FStar_Parser_AST.QForall uu____6776 ->
        let uu____6789 = p_term false false e  in
        soft_parens_with_nesting uu____6789
    | FStar_Parser_AST.QExists uu____6790 ->
        let uu____6803 = p_term false false e  in
        soft_parens_with_nesting uu____6803
    | FStar_Parser_AST.Refine uu____6804 ->
        let uu____6809 = p_term false false e  in
        soft_parens_with_nesting uu____6809
    | FStar_Parser_AST.NamedTyp uu____6810 ->
        let uu____6815 = p_term false false e  in
        soft_parens_with_nesting uu____6815
    | FStar_Parser_AST.Requires uu____6816 ->
        let uu____6823 = p_term false false e  in
        soft_parens_with_nesting uu____6823
    | FStar_Parser_AST.Ensures uu____6824 ->
        let uu____6831 = p_term false false e  in
        soft_parens_with_nesting uu____6831
    | FStar_Parser_AST.Attributes uu____6832 ->
        let uu____6835 = p_term false false e  in
        soft_parens_with_nesting uu____6835
    | FStar_Parser_AST.Quote uu____6836 ->
        let uu____6841 = p_term false false e  in
        soft_parens_with_nesting uu____6841
    | FStar_Parser_AST.VQuote uu____6842 ->
        let uu____6843 = p_term false false e  in
        soft_parens_with_nesting uu____6843
    | FStar_Parser_AST.Antiquote uu____6844 ->
        let uu____6845 = p_term false false e  in
        soft_parens_with_nesting uu____6845

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___119_6846  ->
    match uu___119_6846 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6852) ->
        let uu____6853 = str s  in FStar_Pprint.dquotes uu____6853
    | FStar_Const.Const_bytearray (bytes,uu____6855) ->
        let uu____6860 =
          let uu____6861 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6861  in
        let uu____6862 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6860 uu____6862
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___117_6882 =
          match uu___117_6882 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___118_6888 =
          match uu___118_6888 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6899  ->
               match uu____6899 with
               | (s,w) ->
                   let uu____6906 = signedness s  in
                   let uu____6907 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6906 uu____6907)
            sign_width_opt
           in
        let uu____6908 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6908 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6910 = FStar_Range.string_of_range r  in str uu____6910
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6912 = p_quident lid  in
        let uu____6913 =
          let uu____6914 =
            let uu____6915 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6915  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6914  in
        FStar_Pprint.op_Hat_Hat uu____6912 uu____6913

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6917 = str "u#"  in
    let uu____6918 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6917 uu____6918

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6920;_},u1::u2::[])
        ->
        let uu____6925 =
          let uu____6926 = p_universeFrom u1  in
          let uu____6927 =
            let uu____6928 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6928  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6926 uu____6927  in
        FStar_Pprint.group uu____6925
    | FStar_Parser_AST.App uu____6929 ->
        let uu____6936 = head_and_args u  in
        (match uu____6936 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6962 =
                    let uu____6963 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6964 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6972  ->
                           match uu____6972 with
                           | (u1,uu____6978) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6963 uu____6964  in
                  FStar_Pprint.group uu____6962
              | uu____6979 ->
                  let uu____6980 =
                    let uu____6981 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6981
                     in
                  failwith uu____6980))
    | uu____6982 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7005 = FStar_Ident.text_of_id id1  in str uu____7005
    | FStar_Parser_AST.Paren u1 ->
        let uu____7007 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7007
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7008;_},uu____7009::uu____7010::[])
        ->
        let uu____7013 = p_universeFrom u  in
        soft_parens_with_nesting uu____7013
    | FStar_Parser_AST.App uu____7014 ->
        let uu____7021 = p_universeFrom u  in
        soft_parens_with_nesting uu____7021
    | uu____7022 ->
        let uu____7023 =
          let uu____7024 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7024
           in
        failwith uu____7023

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
       | FStar_Parser_AST.Module (uu____7096,decls) ->
           let uu____7102 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7102
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7111,decls,uu____7113) ->
           let uu____7118 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7118
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7171  ->
         match uu____7171 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7187)) -> false
      | ([],uu____7190) -> false
      | uu____7193 -> true  in
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
        | FStar_Parser_AST.Module (uu____7237,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7243,decls,uu____7245) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7290 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7303;
                 FStar_Parser_AST.doc = uu____7304;
                 FStar_Parser_AST.quals = uu____7305;
                 FStar_Parser_AST.attrs = uu____7306;_}::uu____7307 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7313 =
                   let uu____7316 =
                     let uu____7319 = FStar_List.tl ds  in d :: uu____7319
                      in
                   d0 :: uu____7316  in
                 (uu____7313, (d0.FStar_Parser_AST.drange))
             | uu____7324 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7290 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7378 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7378 dummy_meta
                      FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7474 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7474, comments1))))))
  