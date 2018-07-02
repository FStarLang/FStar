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
  'Auu____169 'Auu____170 .
    'Auu____169 ->
      ('Auu____170 -> 'Auu____169) ->
        'Auu____170 FStar_Pervasives_Native.option -> 'Auu____169
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
  'Auu____264 .
    FStar_Pprint.document ->
      ('Auu____264 -> FStar_Pprint.document) ->
        'Auu____264 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____289 =
          let uu____290 =
            let uu____291 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____291  in
          FStar_Pprint.separate_map uu____290 f l  in
        FStar_Pprint.group uu____289
  
let precede_break_separate_map :
  'Auu____302 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____302 -> FStar_Pprint.document) ->
          'Auu____302 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____332 =
            let uu____333 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____334 =
              let uu____335 = FStar_List.hd l  in
              FStar_All.pipe_right uu____335 f  in
            FStar_Pprint.precede uu____333 uu____334  in
          let uu____336 =
            let uu____337 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____343 =
                   let uu____344 =
                     let uu____345 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____345  in
                   FStar_Pprint.op_Hat_Hat sep uu____344  in
                 FStar_Pprint.op_Hat_Hat break1 uu____343) uu____337
             in
          FStar_Pprint.op_Hat_Hat uu____332 uu____336
  
let concat_break_map :
  'Auu____352 .
    ('Auu____352 -> FStar_Pprint.document) ->
      'Auu____352 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____372 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____376 = f x  in FStar_Pprint.op_Hat_Hat uu____376 break1)
          l
         in
      FStar_Pprint.group uu____372
  
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
    let uu____417 = str "begin"  in
    let uu____418 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____417 contents uu____418
  
let separate_map_last :
  'Auu____427 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____427 -> FStar_Pprint.document) ->
        'Auu____427 Prims.list -> FStar_Pprint.document
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
  'Auu____479 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____479 -> FStar_Pprint.document) ->
        'Auu____479 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____509 =
          let uu____510 =
            let uu____511 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____511  in
          separate_map_last uu____510 f l  in
        FStar_Pprint.group uu____509
  
let separate_map_or_flow :
  'Auu____520 .
    FStar_Pprint.document ->
      ('Auu____520 -> FStar_Pprint.document) ->
        'Auu____520 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____554 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____554 -> FStar_Pprint.document) ->
        'Auu____554 Prims.list -> FStar_Pprint.document
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
  'Auu____606 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____606 -> FStar_Pprint.document) ->
        'Auu____606 Prims.list -> FStar_Pprint.document
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
              let uu____676 = FStar_Pprint.op_Hat_Slash_Hat doc1 doc3  in
              FStar_Pprint.group uu____676
            else FStar_Pprint.surround n1 b doc1 doc2 doc3
  
let soft_surround_separate_map :
  'Auu____696 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____696 -> FStar_Pprint.document) ->
                  'Auu____696 Prims.list -> FStar_Pprint.document
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
                    (let uu____749 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____749
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____768 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____768 -> FStar_Pprint.document) ->
                  'Auu____768 Prims.list -> FStar_Pprint.document
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
                    (let uu____821 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____821
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____836  ->
    match uu____836 with
    | (comment,keywords) ->
        let uu____861 =
          let uu____862 =
            let uu____865 = str comment  in
            let uu____866 =
              let uu____869 =
                let uu____872 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____881  ->
                       match uu____881 with
                       | (k,v1) ->
                           let uu____888 =
                             let uu____891 = str k  in
                             let uu____892 =
                               let uu____895 =
                                 let uu____898 = str v1  in [uu____898]  in
                               FStar_Pprint.rarrow :: uu____895  in
                             uu____891 :: uu____892  in
                           FStar_Pprint.concat uu____888) keywords
                   in
                [uu____872]  in
              FStar_Pprint.space :: uu____869  in
            uu____865 :: uu____866  in
          FStar_Pprint.concat uu____862  in
        FStar_Pprint.group uu____861
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____904 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____916 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____916
      | uu____917 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____959::(e2,uu____961)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____984 -> false  in
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
    | FStar_Parser_AST.Construct (uu____1002,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____1013,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                     )::[])
        -> let uu____1034 = extract_from_list e2  in e1 :: uu____1034
    | uu____1037 ->
        let uu____1038 =
          let uu____1039 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____1039  in
        failwith uu____1038
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____1048;
           FStar_Parser_AST.level = uu____1049;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____1051 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____1059;
           FStar_Parser_AST.level = uu____1060;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           maybe_addr_of_lid;
                                                         FStar_Parser_AST.range
                                                           = uu____1062;
                                                         FStar_Parser_AST.level
                                                           = uu____1063;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1065;
                                                    FStar_Parser_AST.level =
                                                      uu____1066;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____1068;
                FStar_Parser_AST.level = uu____1069;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1071;
           FStar_Parser_AST.level = uu____1072;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____1074 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____1084 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1085;
           FStar_Parser_AST.range = uu____1086;
           FStar_Parser_AST.level = uu____1087;_},{
                                                    FStar_Parser_AST.tm =
                                                      FStar_Parser_AST.App
                                                      ({
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Var
                                                           uu____1088;
                                                         FStar_Parser_AST.range
                                                           = uu____1089;
                                                         FStar_Parser_AST.level
                                                           = uu____1090;_},e1,FStar_Parser_AST.Nothing
                                                       );
                                                    FStar_Parser_AST.range =
                                                      uu____1092;
                                                    FStar_Parser_AST.level =
                                                      uu____1093;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1094;
                FStar_Parser_AST.range = uu____1095;
                FStar_Parser_AST.level = uu____1096;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1098;
           FStar_Parser_AST.level = uu____1099;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1101 = extract_from_ref_set e1  in
        let uu____1104 = extract_from_ref_set e2  in
        FStar_List.append uu____1101 uu____1104
    | uu____1107 ->
        let uu____1108 =
          let uu____1109 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1109  in
        failwith uu____1108
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1117 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1117
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1123 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1123
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1131 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1131 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1139 = FStar_Ident.text_of_id op  in uu____1139 <> "~"))
  
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
      | uu____1205 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1221 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1227 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1233 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___101_1254  ->
    match uu___101_1254 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___102_1279  ->
      match uu___102_1279 with
      | FStar_Util.Inl c ->
          let uu____1288 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1288 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1299 .
    Prims.string ->
      ('Auu____1299,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1320  ->
      match uu____1320 with
      | (assoc_levels,tokens) ->
          let uu____1348 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1348 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___103_1466 =
    match uu___103_1466 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1496  ->
         match uu____1496 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1555 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1555 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1595) ->
          assoc_levels
      | uu____1624 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max_level :
  'Auu____1649 .
    ('Auu____1649,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1694 =
        FStar_List.tryFind
          (fun uu____1724  ->
             match uu____1724 with
             | (uu____1737,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1694 with
      | FStar_Pervasives_Native.Some ((uu____1759,l1,uu____1761),uu____1762)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1797 =
            let uu____1798 =
              let uu____1799 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1799  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1798
             in
          failwith uu____1797
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1821 = assign_levels level_associativity_spec op  in
    match uu____1821 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1851 =
      let uu____1854 =
        let uu____1859 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1859  in
      FStar_List.tryFind uu____1854 operatorInfix0ad12  in
    uu____1851 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1917 =
      let uu____1931 =
        let uu____1947 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1947  in
      FStar_List.tryFind uu____1931 opinfix34  in
    uu____1917 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2003 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2003
    then (Prims.parse_int "1")
    else
      (let uu____2005 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2005
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2014 . FStar_Ident.ident -> 'Auu____2014 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2030 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2030 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2032 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2032
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2033 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2033 [".()<-"; ".[]<-"]
      | uu____2034 -> false
  
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
  'Auu____2128 .
    ('Auu____2128 -> FStar_Pprint.document) ->
      'Auu____2128 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2169 = FStar_ST.op_Bang comment_stack  in
          match uu____2169 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2232 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2232
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2273 =
                    let uu____2274 =
                      let uu____2275 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2275
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2274  in
                  comments_before_pos uu____2273 print_pos lookahead_pos))
              else
                (let uu____2277 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2277))
           in
        let uu____2278 =
          let uu____2283 =
            let uu____2284 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2284  in
          let uu____2285 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2283 uu____2285  in
        match uu____2278 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2291 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2291
              else comments  in
            let uu____2297 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2297
  
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
            let uu____2323 = FStar_ST.op_Bang comment_stack  in
            match uu____2323 with
            | (comment,crange)::cs when
                FStar_Range.range_before_pos crange pos_end ->
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let lnum =
                    let uu____2415 =
                      let uu____2416 =
                        let uu____2417 = FStar_Range.start_of_range crange
                           in
                        FStar_Range.line_of_pos uu____2417  in
                      uu____2416 - lbegin  in
                    max k uu____2415  in
                  let lnum1 = min (Prims.parse_int "2") lnum  in
                  let doc2 =
                    let uu____2420 =
                      let uu____2421 =
                        FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                      let uu____2422 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2421 uu____2422  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____2420  in
                  let uu____2423 =
                    let uu____2424 = FStar_Range.end_of_range crange  in
                    FStar_Range.line_of_pos uu____2424  in
                  place_comments_until_pos (Prims.parse_int "1") uu____2423
                    pos_end meta_decl doc2))
            | uu____2425 ->
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
                     let uu____2438 = FStar_Range.line_of_pos pos_end  in
                     uu____2438 - lbegin  in
                   let lnum1 =
                     if lnum >= (Prims.parse_int "2")
                     then lnum - end_correction
                     else lnum  in
                   let lnum2 = min (Prims.parse_int "2") lnum1  in
                   let lnum3 =
                     if lnum2 >= (Prims.parse_int "2")
                     then lnum2 - fsdoc_correction
                     else lnum2  in
                   let uu____2444 =
                     FStar_Pprint.repeat lnum3 FStar_Pprint.hardline  in
                   FStar_Pprint.op_Hat_Hat doc1 uu____2444)
  
let separate_map_with_comments :
  'Auu____2457 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2457 -> FStar_Pprint.document) ->
          'Auu____2457 Prims.list ->
            ('Auu____2457 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2514 x =
              match uu____2514 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2529 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2529 meta_decl doc1
                     in
                  let uu____2530 =
                    let uu____2531 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2531  in
                  let uu____2532 =
                    let uu____2533 =
                      let uu____2534 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2534  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2533  in
                  (uu____2530, uu____2532)
               in
            let uu____2535 =
              let uu____2542 = FStar_List.hd xs  in
              let uu____2543 = FStar_List.tl xs  in (uu____2542, uu____2543)
               in
            match uu____2535 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2560 =
                    let uu____2561 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2561  in
                  let uu____2562 =
                    let uu____2563 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2563  in
                  (uu____2560, uu____2562)  in
                let uu____2564 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2564
  
let separate_map_with_comments_kw :
  'Auu____2587 'Auu____2588 .
    'Auu____2587 ->
      'Auu____2587 ->
        ('Auu____2587 -> 'Auu____2588 -> FStar_Pprint.document) ->
          'Auu____2588 Prims.list ->
            ('Auu____2588 -> decl_meta) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_meta  ->
            let fold_fun uu____2650 x =
              match uu____2650 with
              | (last_line,doc1) ->
                  let meta_decl = extract_meta x  in
                  let r = meta_decl.r  in
                  let doc2 =
                    let uu____2665 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2665 meta_decl doc1
                     in
                  let uu____2666 =
                    let uu____2667 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2667  in
                  let uu____2668 =
                    let uu____2669 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2669  in
                  (uu____2666, uu____2668)
               in
            let uu____2670 =
              let uu____2677 = FStar_List.hd xs  in
              let uu____2678 = FStar_List.tl xs  in (uu____2677, uu____2678)
               in
            match uu____2670 with
            | (x,xs1) ->
                let init1 =
                  let meta_decl = extract_meta x  in
                  let uu____2695 =
                    let uu____2696 = FStar_Range.end_of_range meta_decl.r  in
                    FStar_Range.line_of_pos uu____2696  in
                  let uu____2697 = f prefix1 x  in (uu____2695, uu____2697)
                   in
                let uu____2698 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2698
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3408)) ->
          let uu____3411 =
            let uu____3412 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3412 FStar_Util.is_upper  in
          if uu____3411
          then
            let uu____3415 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3415 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3417 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3424 =
      FStar_Pprint.optional
        (fun d1  ->
           let uu____3428 = p_fsdoc d1  in
           FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3428)
        d.FStar_Parser_AST.doc
       in
    let uu____3429 =
      let uu____3430 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3431 =
        let uu____3432 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3432  in
      FStar_Pprint.op_Hat_Hat uu____3430 uu____3431  in
    FStar_Pprint.op_Hat_Hat uu____3424 uu____3429

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3434 ->
        let uu____3435 =
          let uu____3436 = str "@ "  in
          let uu____3437 =
            let uu____3438 =
              let uu____3439 =
                let uu____3440 =
                  let uu____3441 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3441  in
                FStar_Pprint.op_Hat_Hat uu____3440 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3439  in
            FStar_Pprint.op_Hat_Hat uu____3438 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3436 uu____3437  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3435

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3444  ->
    match uu____3444 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3480 =
                match uu____3480 with
                | (kwd,arg) ->
                    let uu____3487 = str "@"  in
                    let uu____3488 =
                      let uu____3489 = str kwd  in
                      let uu____3490 =
                        let uu____3491 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3491
                         in
                      FStar_Pprint.op_Hat_Hat uu____3489 uu____3490  in
                    FStar_Pprint.op_Hat_Hat uu____3487 uu____3488
                 in
              let uu____3492 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  process_kwd_arg kwd_args1
                 in
              FStar_Pprint.op_Hat_Hat uu____3492 FStar_Pprint.hardline
           in
        let uu____3497 =
          let uu____3498 =
            let uu____3499 =
              let uu____3500 = str doc1  in
              let uu____3501 =
                let uu____3502 =
                  let uu____3503 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3503  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3502  in
              FStar_Pprint.op_Hat_Hat uu____3500 uu____3501  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3499  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3498  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3497

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3507 =
          let uu____3508 = str "val"  in
          let uu____3509 =
            let uu____3510 =
              let uu____3511 = p_lident lid  in
              let uu____3512 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3511 uu____3512  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3510  in
          FStar_Pprint.op_Hat_Hat uu____3508 uu____3509  in
        let uu____3513 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3507 uu____3513
    | FStar_Parser_AST.TopLevelLet (uu____3514,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3539 =
               let uu____3540 = str "let"  in p_letlhs uu____3540 lb  in
             FStar_Pprint.group uu____3539) lbs
    | uu____3541 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___104_3556 =
          match uu___104_3556 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3564 = f x  in
              let uu____3565 =
                let uu____3566 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3566  in
              FStar_Pprint.op_Hat_Hat uu____3564 uu____3565
           in
        let uu____3567 = str "["  in
        let uu____3568 =
          let uu____3569 = p_list' l  in
          let uu____3570 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3569 uu____3570  in
        FStar_Pprint.op_Hat_Hat uu____3567 uu____3568

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3573 =
          let uu____3574 = str "open"  in
          let uu____3575 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3574 uu____3575  in
        FStar_Pprint.group uu____3573
    | FStar_Parser_AST.Include uid ->
        let uu____3577 =
          let uu____3578 = str "include"  in
          let uu____3579 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3578 uu____3579  in
        FStar_Pprint.group uu____3577
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3582 =
          let uu____3583 = str "module"  in
          let uu____3584 =
            let uu____3585 =
              let uu____3586 = p_uident uid1  in
              let uu____3587 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3586 uu____3587  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3585  in
          FStar_Pprint.op_Hat_Hat uu____3583 uu____3584  in
        let uu____3588 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3582 uu____3588
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3590 =
          let uu____3591 = str "module"  in
          let uu____3592 =
            let uu____3593 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3593  in
          FStar_Pprint.op_Hat_Hat uu____3591 uu____3592  in
        FStar_Pprint.group uu____3590
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3626 = str "effect"  in
          let uu____3627 =
            let uu____3628 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3628  in
          FStar_Pprint.op_Hat_Hat uu____3626 uu____3627  in
        let uu____3629 =
          let uu____3630 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3630 FStar_Pprint.equals
           in
        let uu____3631 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3629 uu____3631
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3649 =
          let uu____3650 = str "type"  in
          let uu____3651 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3650 uu____3651  in
        let uu____3664 =
          let uu____3665 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3703 =
                    let uu____3704 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3704 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3703)) uu____3665
           in
        FStar_Pprint.op_Hat_Hat uu____3649 uu____3664
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3720 = str "let"  in
          let uu____3721 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3720 uu____3721  in
        let uu____3722 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3722 p_letbinding lbs
          (fun uu____3731  ->
             match uu____3731 with
             | (p,t) ->
                 let uu____3738 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 {
                   r = uu____3738;
                   has_qs = false;
                   has_attrs = false;
                   has_fsdoc = (FStar_Util.is_some d.FStar_Parser_AST.doc)
                 })
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3741 = str "val"  in
        let uu____3742 =
          let uu____3743 =
            let uu____3744 = p_lident lid  in
            let uu____3745 =
              let uu____3746 =
                let uu____3747 =
                  let uu____3748 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3748  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3747  in
              FStar_Pprint.group uu____3746  in
            FStar_Pprint.op_Hat_Hat uu____3744 uu____3745  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3743  in
        FStar_Pprint.op_Hat_Hat uu____3741 uu____3742
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3752 =
            let uu____3753 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3753 FStar_Util.is_upper  in
          if uu____3752
          then FStar_Pprint.empty
          else
            (let uu____3757 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3757 FStar_Pprint.space)
           in
        let uu____3758 =
          let uu____3759 = p_ident id1  in
          let uu____3760 =
            let uu____3761 =
              let uu____3762 =
                let uu____3763 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3763  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3762  in
            FStar_Pprint.group uu____3761  in
          FStar_Pprint.op_Hat_Hat uu____3759 uu____3760  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3758
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3770 = str "exception"  in
        let uu____3771 =
          let uu____3772 =
            let uu____3773 = p_uident uid  in
            let uu____3774 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3778 =
                     let uu____3779 = str "of"  in
                     let uu____3780 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3779 uu____3780  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3778) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3773 uu____3774  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3772  in
        FStar_Pprint.op_Hat_Hat uu____3770 uu____3771
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3782 = str "new_effect"  in
        let uu____3783 =
          let uu____3784 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3784  in
        FStar_Pprint.op_Hat_Hat uu____3782 uu____3783
    | FStar_Parser_AST.SubEffect se ->
        let uu____3786 = str "sub_effect"  in
        let uu____3787 =
          let uu____3788 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3788  in
        FStar_Pprint.op_Hat_Hat uu____3786 uu____3787
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3791 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3791 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3792 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3793) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3816 = str "%splice"  in
        let uu____3817 =
          let uu____3818 =
            let uu____3819 = str ";"  in p_list p_uident uu____3819 ids  in
          let uu____3820 =
            let uu____3821 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3821  in
          FStar_Pprint.op_Hat_Hat uu____3818 uu____3820  in
        FStar_Pprint.op_Hat_Hat uu____3816 uu____3817

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___105_3822  ->
    match uu___105_3822 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3824 = str "#set-options"  in
        let uu____3825 =
          let uu____3826 =
            let uu____3827 = str s  in FStar_Pprint.dquotes uu____3827  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3826  in
        FStar_Pprint.op_Hat_Hat uu____3824 uu____3825
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3831 = str "#reset-options"  in
        let uu____3832 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3836 =
                 let uu____3837 = str s  in FStar_Pprint.dquotes uu____3837
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3836) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3831 uu____3832
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
    fun uu____3866  ->
      match uu____3866 with
      | (typedecl,fsdoc_opt) ->
          let uu____3879 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3879 with
           | (decl,body) ->
               let uu____3897 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3897)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___106_3899  ->
      match uu___106_3899 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3929 = FStar_Pprint.empty  in
          let uu____3930 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3930, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3951 =
            let uu____3952 = p_typ false false t  in jump2 uu____3952  in
          let uu____3953 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3953, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4007 =
            match uu____4007 with
            | (lid1,t,doc_opt) ->
                let uu____4023 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4023
             in
          let p_fields uu____4039 =
            let uu____4040 =
              let uu____4041 =
                let uu____4042 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4042 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4041  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4040  in
          let uu____4051 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4051, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4112 =
            match uu____4112 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4138 =
                    let uu____4139 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4139  in
                  FStar_Range.extend_to_end_of_line uu____4138  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4165 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4178 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4178,
            ((fun uu____4184  ->
                let uu____4185 = datacon_doc ()  in jump2 uu____4185)))

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
  fun uu____4186  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4186 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4220 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4220  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4222 =
                        let uu____4225 =
                          let uu____4228 = p_fsdoc fsdoc  in
                          let uu____4229 =
                            let uu____4232 = cont lid_doc  in [uu____4232]
                             in
                          uu____4228 :: uu____4229  in
                        kw :: uu____4225  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4222
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4237 =
                        let uu____4238 =
                          let uu____4239 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4239 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4238
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4237
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4254 =
                          let uu____4255 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4255  in
                        prefix2 uu____4254 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4257  ->
      match uu____4257 with
      | (lid,t,doc_opt) ->
          let uu____4273 =
            let uu____4274 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4275 =
              let uu____4276 = p_lident lid  in
              let uu____4277 =
                let uu____4278 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4278  in
              FStar_Pprint.op_Hat_Hat uu____4276 uu____4277  in
            FStar_Pprint.op_Hat_Hat uu____4274 uu____4275  in
          FStar_Pprint.group uu____4273

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4279  ->
    match uu____4279 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4307 =
            let uu____4308 =
              let uu____4309 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4309  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4308  in
          FStar_Pprint.group uu____4307  in
        let uu____4310 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4311 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4315 =
                 let uu____4316 =
                   let uu____4317 =
                     let uu____4318 =
                       let uu____4319 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4319
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4318  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4317  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4316  in
               FStar_Pprint.group uu____4315) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4310 uu____4311

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4321  ->
      match uu____4321 with
      | (pat,uu____4327) ->
          let uu____4328 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4347 =
                  let uu____4348 =
                    let uu____4349 =
                      let uu____4350 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4350
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4349  in
                  FStar_Pprint.group uu____4348  in
                (pat1, uu____4347)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4362 =
                  let uu____4363 =
                    let uu____4364 =
                      let uu____4365 =
                        let uu____4366 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4366
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4365
                       in
                    FStar_Pprint.group uu____4364  in
                  let uu____4367 =
                    let uu____4368 =
                      let uu____4369 = str "by"  in
                      let uu____4370 =
                        let uu____4371 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4371
                         in
                      FStar_Pprint.op_Hat_Hat uu____4369 uu____4370  in
                    FStar_Pprint.group uu____4368  in
                  FStar_Pprint.op_Hat_Hat uu____4363 uu____4367  in
                (pat1, uu____4362)
            | uu____4372 -> (pat, FStar_Pprint.empty)  in
          (match uu____4328 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4376);
                       FStar_Parser_AST.prange = uu____4377;_},pats)
                    ->
                    let uu____4387 =
                      let uu____4388 =
                        let uu____4389 =
                          let uu____4390 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4390  in
                        FStar_Pprint.group uu____4389  in
                      let uu____4391 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4388 uu____4391  in
                    prefix2_nonempty uu____4387 ascr_doc
                | uu____4392 ->
                    let uu____4393 =
                      let uu____4394 =
                        let uu____4395 =
                          let uu____4396 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4396  in
                        FStar_Pprint.group uu____4395  in
                      FStar_Pprint.op_Hat_Hat uu____4394 ascr_doc  in
                    FStar_Pprint.group uu____4393))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4398  ->
      match uu____4398 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4407 =
            let uu____4408 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4408  in
          let uu____4409 =
            let uu____4410 =
              let uu____4411 =
                let uu____4412 =
                  let uu____4413 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4413  in
                FStar_Pprint.group uu____4412  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4411  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4410  in
          FStar_Pprint.ifflat uu____4407 uu____4409

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___107_4414  ->
    match uu___107_4414 with
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
        let uu____4439 = p_uident uid  in
        let uu____4440 = p_binders true bs  in
        let uu____4441 =
          let uu____4442 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4442  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4439 uu____4440 uu____4441

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
          let uu____4452 =
            let uu____4453 =
              let uu____4454 =
                let uu____4455 = p_uident uid  in
                let uu____4456 = p_binders true bs  in
                let uu____4457 =
                  let uu____4458 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4458  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4455 uu____4456 uu____4457
                 in
              FStar_Pprint.group uu____4454  in
            let uu____4459 =
              let uu____4460 = str "with"  in
              let uu____4461 =
                let uu____4462 =
                  let uu____4463 =
                    let uu____4464 =
                      let uu____4465 =
                        let uu____4466 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4466
                         in
                      separate_map_last uu____4465 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4464  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4463  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4462  in
              FStar_Pprint.op_Hat_Hat uu____4460 uu____4461  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4453 uu____4459  in
          braces_with_nesting uu____4452

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
          let uu____4497 =
            let uu____4498 = p_lident lid  in
            let uu____4499 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4498 uu____4499  in
          let uu____4500 = p_simpleTerm ps false e  in
          prefix2 uu____4497 uu____4500
      | uu____4501 ->
          let uu____4502 =
            let uu____4503 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4503
             in
          failwith uu____4502

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4565 =
        match uu____4565 with
        | (kwd,t) ->
            let uu____4572 =
              let uu____4573 = str kwd  in
              let uu____4574 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4573 uu____4574  in
            let uu____4575 = p_simpleTerm ps false t  in
            prefix2 uu____4572 uu____4575
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4580 =
      let uu____4581 =
        let uu____4582 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4583 =
          let uu____4584 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4584  in
        FStar_Pprint.op_Hat_Hat uu____4582 uu____4583  in
      let uu____4585 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4581 uu____4585  in
    let uu____4586 =
      let uu____4587 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4587  in
    FStar_Pprint.op_Hat_Hat uu____4580 uu____4586

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___108_4588  ->
    match uu___108_4588 with
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
        let uu____4591 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4591 FStar_Pprint.hardline
    | uu____4592 ->
        let uu____4593 =
          let uu____4594 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4594  in
        FStar_Pprint.op_Hat_Hat uu____4593 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___109_4597  ->
    match uu___109_4597 with
    | FStar_Parser_AST.Rec  ->
        let uu____4598 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4598
    | FStar_Parser_AST.Mutable  ->
        let uu____4599 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4599
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___110_4600  ->
    match uu___110_4600 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4605 =
          let uu____4606 =
            let uu____4607 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4607  in
          FStar_Pprint.separate_map uu____4606 p_tuplePattern pats  in
        FStar_Pprint.group uu____4605
    | uu____4608 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4615 =
          let uu____4616 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4616 p_constructorPattern pats  in
        FStar_Pprint.group uu____4615
    | uu____4617 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4620;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4625 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4626 = p_constructorPattern hd1  in
        let uu____4627 = p_constructorPattern tl1  in
        infix0 uu____4625 uu____4626 uu____4627
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4629;_},pats)
        ->
        let uu____4635 = p_quident uid  in
        let uu____4636 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4635 uu____4636
    | uu____4637 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4653;
               FStar_Parser_AST.blevel = uu____4654;
               FStar_Parser_AST.aqual = uu____4655;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4661 =
               let uu____4662 = p_ident lid  in
               p_refinement aqual uu____4662 t1 phi  in
             soft_parens_with_nesting uu____4661
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4664;
               FStar_Parser_AST.blevel = uu____4665;
               FStar_Parser_AST.aqual = uu____4666;_},phi))
             ->
             let uu____4668 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
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
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4740 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4741 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4740 uu____4741
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4743 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4746;
           FStar_Parser_AST.prange = uu____4747;_},uu____4748)
        ->
        let uu____4753 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4753
    | FStar_Parser_AST.PatTuple (uu____4754,false ) ->
        let uu____4759 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4759
    | uu____4760 ->
        let uu____4761 =
          let uu____4762 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4762  in
        failwith uu____4761

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4764;_},uu____4765)
        -> true
    | uu____4770 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4774 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4775 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4774 uu____4775
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4782;
                   FStar_Parser_AST.blevel = uu____4783;
                   FStar_Parser_AST.aqual = uu____4784;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4786 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4786 t1 phi
            | uu____4787 ->
                let t' =
                  let uu____4789 = is_typ_tuple t  in
                  if uu____4789
                  then
                    let uu____4790 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4790
                  else p_tmFormula t  in
                let uu____4792 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4793 =
                  let uu____4794 = p_lident lid  in
                  let uu____4795 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4794 uu____4795  in
                FStar_Pprint.op_Hat_Hat uu____4792 uu____4793
             in
          if is_atomic
          then
            let uu____4796 =
              let uu____4797 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4797  in
            FStar_Pprint.group uu____4796
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4799 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4806;
                  FStar_Parser_AST.blevel = uu____4807;
                  FStar_Parser_AST.aqual = uu____4808;_},phi)
               ->
               if is_atomic
               then
                 let uu____4810 =
                   let uu____4811 =
                     let uu____4812 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4812 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4811  in
                 FStar_Pprint.group uu____4810
               else
                 (let uu____4814 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4814)
           | uu____4815 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4824 -> false
            | FStar_Parser_AST.App uu____4835 -> false
            | FStar_Parser_AST.Op uu____4842 -> false
            | uu____4849 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4853 =
            let uu____4854 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4855 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4854 uu____4855  in
          let uu____4856 =
            let uu____4857 = p_appTerm t  in
            let uu____4858 =
              let uu____4859 =
                let uu____4860 =
                  let uu____4861 = soft_braces_with_nesting_tight phi1  in
                  let uu____4862 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4861 uu____4862  in
                FStar_Pprint.group uu____4860  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4859
               in
            FStar_Pprint.op_Hat_Hat uu____4857 uu____4858  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4853 uu____4856

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4873 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4873

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4878 = FStar_Ident.text_of_id lid  in str uu____4878)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4881 = FStar_Ident.text_of_lid lid  in str uu____4881)

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
            let uu____4899 =
              let uu____4900 =
                let uu____4901 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4901 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4900  in
            let uu____4902 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4899 uu____4902
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4906 =
              let uu____4907 =
                let uu____4908 =
                  let uu____4909 = p_lident x  in
                  let uu____4910 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4909 uu____4910  in
                let uu____4911 =
                  let uu____4912 = p_noSeqTerm true false e1  in
                  let uu____4913 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4912 uu____4913  in
                op_Hat_Slash_Plus_Hat uu____4908 uu____4911  in
              FStar_Pprint.group uu____4907  in
            let uu____4914 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4906 uu____4914
        | uu____4915 ->
            let uu____4916 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4916

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
            let uu____4927 =
              let uu____4928 = p_tmIff e1  in
              let uu____4929 =
                let uu____4930 =
                  let uu____4931 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4931
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4930  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4928 uu____4929  in
            FStar_Pprint.group uu____4927
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4937 =
              let uu____4938 = p_tmIff e1  in
              let uu____4939 =
                let uu____4940 =
                  let uu____4941 =
                    let uu____4942 = p_typ false false t  in
                    let uu____4943 =
                      let uu____4944 = str "by"  in
                      let uu____4945 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4944 uu____4945  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4942 uu____4943  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4941
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4940  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4938 uu____4939  in
            FStar_Pprint.group uu____4937
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4946;_},e1::e2::e3::[])
            ->
            let uu____4952 =
              let uu____4953 =
                let uu____4954 =
                  let uu____4955 = p_atomicTermNotQUident e1  in
                  let uu____4956 =
                    let uu____4957 =
                      let uu____4958 =
                        let uu____4959 = p_term false false e2  in
                        soft_parens_with_nesting uu____4959  in
                      let uu____4960 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4958 uu____4960  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4957  in
                  FStar_Pprint.op_Hat_Hat uu____4955 uu____4956  in
                FStar_Pprint.group uu____4954  in
              let uu____4961 =
                let uu____4962 = p_noSeqTerm ps pb e3  in jump2 uu____4962
                 in
              FStar_Pprint.op_Hat_Hat uu____4953 uu____4961  in
            FStar_Pprint.group uu____4952
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4963;_},e1::e2::e3::[])
            ->
            let uu____4969 =
              let uu____4970 =
                let uu____4971 =
                  let uu____4972 = p_atomicTermNotQUident e1  in
                  let uu____4973 =
                    let uu____4974 =
                      let uu____4975 =
                        let uu____4976 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4976  in
                      let uu____4977 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4975 uu____4977  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4974  in
                  FStar_Pprint.op_Hat_Hat uu____4972 uu____4973  in
                FStar_Pprint.group uu____4971  in
              let uu____4978 =
                let uu____4979 = p_noSeqTerm ps pb e3  in jump2 uu____4979
                 in
              FStar_Pprint.op_Hat_Hat uu____4970 uu____4978  in
            FStar_Pprint.group uu____4969
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4987 =
              let uu____4988 = str "requires"  in
              let uu____4989 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4988 uu____4989  in
            FStar_Pprint.group uu____4987
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4997 =
              let uu____4998 = str "ensures"  in
              let uu____4999 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4998 uu____4999  in
            FStar_Pprint.group uu____4997
        | FStar_Parser_AST.Attributes es ->
            let uu____5003 =
              let uu____5004 = str "attributes"  in
              let uu____5005 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5004 uu____5005  in
            FStar_Pprint.group uu____5003
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5009 =
                let uu____5010 =
                  let uu____5011 = str "if"  in
                  let uu____5012 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5011 uu____5012  in
                let uu____5013 =
                  let uu____5014 = str "then"  in
                  let uu____5015 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5014 uu____5015  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5010 uu____5013  in
              FStar_Pprint.group uu____5009
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5018,uu____5019,e31) when
                     is_unit e31 ->
                     let uu____5021 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5021
                 | uu____5022 -> p_noSeqTerm false false e2  in
               let uu____5023 =
                 let uu____5024 =
                   let uu____5025 = str "if"  in
                   let uu____5026 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5025 uu____5026  in
                 let uu____5027 =
                   let uu____5028 =
                     let uu____5029 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5029 e2_doc  in
                   let uu____5030 =
                     let uu____5031 = str "else"  in
                     let uu____5032 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5031 uu____5032  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5028 uu____5030  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5024 uu____5027  in
               FStar_Pprint.group uu____5023)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5055 =
              let uu____5056 =
                let uu____5057 =
                  let uu____5058 = str "try"  in
                  let uu____5059 = p_noSeqTerm false false e1  in
                  prefix2 uu____5058 uu____5059  in
                let uu____5060 =
                  let uu____5061 = str "with"  in
                  let uu____5062 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5061 uu____5062  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5057 uu____5060  in
              FStar_Pprint.group uu____5056  in
            let uu____5071 = paren_if (ps || pb)  in uu____5071 uu____5055
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5098 =
              let uu____5099 =
                let uu____5100 =
                  let uu____5101 = str "match"  in
                  let uu____5102 = p_noSeqTerm false false e1  in
                  let uu____5103 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5101 uu____5102 uu____5103
                   in
                let uu____5104 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5100 uu____5104  in
              FStar_Pprint.group uu____5099  in
            let uu____5113 = paren_if (ps || pb)  in uu____5113 uu____5098
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5120 =
              let uu____5121 =
                let uu____5122 =
                  let uu____5123 = str "let open"  in
                  let uu____5124 = p_quident uid  in
                  let uu____5125 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5123 uu____5124 uu____5125
                   in
                let uu____5126 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5122 uu____5126  in
              FStar_Pprint.group uu____5121  in
            let uu____5127 = paren_if ps  in uu____5127 uu____5120
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5191 is_last =
              match uu____5191 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5224 =
                          let uu____5225 = str "let"  in
                          let uu____5226 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5225 uu____5226
                           in
                        FStar_Pprint.group uu____5224
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5227 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5232 =
                    if is_last
                    then
                      let uu____5233 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5234 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5233 doc_expr uu____5234
                    else
                      (let uu____5236 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5236)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5232
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5282 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5282
                     else
                       (let uu____5290 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5290)) lbs
               in
            let lbs_doc =
              let uu____5298 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5298  in
            let uu____5299 =
              let uu____5300 =
                let uu____5301 =
                  let uu____5302 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5302
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5301  in
              FStar_Pprint.group uu____5300  in
            let uu____5303 = paren_if ps  in uu____5303 uu____5299
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5310;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5313;
                                                             FStar_Parser_AST.level
                                                               = uu____5314;_})
            when matches_var maybe_x x ->
            let uu____5341 =
              let uu____5342 =
                let uu____5343 = str "function"  in
                let uu____5344 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5343 uu____5344  in
              FStar_Pprint.group uu____5342  in
            let uu____5353 = paren_if (ps || pb)  in uu____5353 uu____5341
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5359 =
              let uu____5360 = str "quote"  in
              let uu____5361 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5360 uu____5361  in
            FStar_Pprint.group uu____5359
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5363 =
              let uu____5364 = str "`"  in
              let uu____5365 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5364 uu____5365  in
            FStar_Pprint.group uu____5363
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5367 =
              let uu____5368 = str "%`"  in
              let uu____5369 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5368 uu____5369  in
            FStar_Pprint.group uu____5367
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5371 =
              let uu____5372 = str "`#"  in
              let uu____5373 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5372 uu____5373  in
            FStar_Pprint.group uu____5371
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5375 =
              let uu____5376 = str "`@"  in
              let uu____5377 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5376 uu____5377  in
            FStar_Pprint.group uu____5375
        | uu____5378 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___111_5379  ->
    match uu___111_5379 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5391 =
          let uu____5392 = str "[@"  in
          let uu____5393 =
            let uu____5394 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5395 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5394 uu____5395  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5392 uu____5393  in
        FStar_Pprint.group uu____5391

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
                 let uu____5421 =
                   let uu____5422 =
                     let uu____5423 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5423 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5422 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5421 term_doc
             | pats ->
                 let uu____5429 =
                   let uu____5430 =
                     let uu____5431 =
                       let uu____5432 =
                         let uu____5433 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5433
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5432 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5434 = p_trigger trigger  in
                     prefix2 uu____5431 uu____5434  in
                   FStar_Pprint.group uu____5430  in
                 prefix2 uu____5429 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5454 =
                   let uu____5455 =
                     let uu____5456 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5456 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5455 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5454 term_doc
             | pats ->
                 let uu____5462 =
                   let uu____5463 =
                     let uu____5464 =
                       let uu____5465 =
                         let uu____5466 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5466
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5465 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5467 = p_trigger trigger  in
                     prefix2 uu____5464 uu____5467  in
                   FStar_Pprint.group uu____5463  in
                 prefix2 uu____5462 term_doc)
        | uu____5468 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5470 -> str "forall"
    | FStar_Parser_AST.QExists uu____5483 -> str "exists"
    | uu____5496 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___112_5497  ->
    match uu___112_5497 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5509 =
          let uu____5510 =
            let uu____5511 =
              let uu____5512 = str "pattern"  in
              let uu____5513 =
                let uu____5514 =
                  let uu____5515 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5515
                   in
                FStar_Pprint.op_Hat_Hat uu____5514 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5512 uu____5513  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5511  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5510  in
        FStar_Pprint.group uu____5509

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5521 = str "\\/"  in
    FStar_Pprint.separate_map uu____5521 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5527 =
      let uu____5528 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5528 p_appTerm pats  in
    FStar_Pprint.group uu____5527

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5538 =
              let uu____5539 =
                let uu____5540 = str "fun"  in
                let uu____5541 =
                  let uu____5542 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5542
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5540 uu____5541  in
              let uu____5543 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5539 uu____5543  in
            let uu____5544 = paren_if ps  in uu____5544 uu____5538
        | uu____5549 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5553  ->
      match uu____5553 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5576 =
                    let uu____5577 =
                      let uu____5578 =
                        let uu____5579 = p_tuplePattern p  in
                        let uu____5580 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5579 uu____5580  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5578
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5577  in
                  FStar_Pprint.group uu____5576
              | FStar_Pervasives_Native.Some f ->
                  let uu____5582 =
                    let uu____5583 =
                      let uu____5584 =
                        let uu____5585 =
                          let uu____5586 =
                            let uu____5587 = p_tuplePattern p  in
                            let uu____5588 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5587
                              uu____5588
                             in
                          FStar_Pprint.group uu____5586  in
                        let uu____5589 =
                          let uu____5590 =
                            let uu____5593 = p_tmFormula f  in
                            [uu____5593; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5590  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5585 uu____5589
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5584
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5583  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5582
               in
            let uu____5594 =
              let uu____5595 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5595  in
            FStar_Pprint.group uu____5594  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5604 =
                      let uu____5605 =
                        let uu____5606 =
                          let uu____5607 =
                            let uu____5608 =
                              let uu____5609 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5609  in
                            FStar_Pprint.separate_map uu____5608
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5607
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5606
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5605  in
                    FStar_Pprint.group uu____5604
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5610 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5612;_},e1::e2::[])
        ->
        let uu____5617 = str "<==>"  in
        let uu____5618 = p_tmImplies e1  in
        let uu____5619 = p_tmIff e2  in
        infix0 uu____5617 uu____5618 uu____5619
    | uu____5620 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5622;_},e1::e2::[])
        ->
        let uu____5627 = str "==>"  in
        let uu____5628 = p_tmArrow p_tmFormula e1  in
        let uu____5629 = p_tmImplies e2  in
        infix0 uu____5627 uu____5628 uu____5629
    | uu____5630 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5638 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5638 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5659 ->
               let uu____5660 =
                 let uu____5661 =
                   let uu____5662 =
                     let uu____5663 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5663
                      in
                   FStar_Pprint.separate uu____5662 terms  in
                 let uu____5664 =
                   let uu____5665 =
                     let uu____5666 =
                       let uu____5667 =
                         let uu____5668 =
                           let uu____5669 =
                             let uu____5670 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5670
                              in
                           FStar_Pprint.separate uu____5669 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5668 last_op  in
                       let uu____5671 =
                         let uu____5672 =
                           let uu____5673 =
                             let uu____5674 =
                               let uu____5675 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5675
                                in
                             FStar_Pprint.separate uu____5674 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5673 last_op  in
                         jump2 uu____5672  in
                       FStar_Pprint.ifflat uu____5667 uu____5671  in
                     FStar_Pprint.group uu____5666  in
                   let uu____5676 = FStar_List.hd last1  in
                   prefix2 uu____5665 uu____5676  in
                 FStar_Pprint.ifflat uu____5661 uu____5664  in
               FStar_Pprint.group uu____5660)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5689 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5694 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5689 uu____5694
      | uu____5697 -> let uu____5698 = p_Tm e  in [uu____5698]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5701 =
        let uu____5702 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5702 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5701  in
    let disj =
      let uu____5704 =
        let uu____5705 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5705 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5704  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5724;_},e1::e2::[])
        ->
        let uu____5729 = p_tmDisjunction e1  in
        let uu____5734 = let uu____5739 = p_tmConjunction e2  in [uu____5739]
           in
        FStar_List.append uu____5729 uu____5734
    | uu____5748 -> let uu____5749 = p_tmConjunction e  in [uu____5749]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5759;_},e1::e2::[])
        ->
        let uu____5764 = p_tmConjunction e1  in
        let uu____5767 = let uu____5770 = p_tmTuple e2  in [uu____5770]  in
        FStar_List.append uu____5764 uu____5767
    | uu____5771 -> let uu____5772 = p_tmTuple e  in [uu____5772]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5789 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5789
          (fun uu____5797  ->
             match uu____5797 with | (e1,uu____5803) -> p_tmEq e1) args
    | uu____5804 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5809 =
             let uu____5810 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5810  in
           FStar_Pprint.group uu____5809)

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
               (let uu____5827 = FStar_Ident.text_of_id op  in
                uu____5827 = "="))
              ||
              (let uu____5829 = FStar_Ident.text_of_id op  in
               uu____5829 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5831 = levels op1  in
            (match uu____5831 with
             | (left1,mine,right1) ->
                 let uu____5841 =
                   let uu____5842 = FStar_All.pipe_left str op1  in
                   let uu____5843 = p_tmEqWith' p_X left1 e1  in
                   let uu____5844 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5842 uu____5843 uu____5844  in
                 paren_if_gt curr mine uu____5841)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5845;_},e1::e2::[])
            ->
            let uu____5850 =
              let uu____5851 = p_tmEqWith p_X e1  in
              let uu____5852 =
                let uu____5853 =
                  let uu____5854 =
                    let uu____5855 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5855  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5854  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5853  in
              FStar_Pprint.op_Hat_Hat uu____5851 uu____5852  in
            FStar_Pprint.group uu____5850
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5856;_},e1::[])
            ->
            let uu____5860 = levels "-"  in
            (match uu____5860 with
             | (left1,mine,right1) ->
                 let uu____5870 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5870)
        | uu____5871 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5915)::(e2,uu____5917)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5937 = is_list e  in Prims.op_Negation uu____5937)
              ->
              let op = "::"  in
              let uu____5939 = levels op  in
              (match uu____5939 with
               | (left1,mine,right1) ->
                   let uu____5949 =
                     let uu____5950 = str op  in
                     let uu____5951 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5952 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5950 uu____5951 uu____5952  in
                   paren_if_gt curr mine uu____5949)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5960 = levels op  in
              (match uu____5960 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5976 = p_binder false b  in
                     let uu____5977 =
                       let uu____5978 =
                         let uu____5979 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5979 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5978
                        in
                     FStar_Pprint.op_Hat_Hat uu____5976 uu____5977  in
                   let uu____5980 =
                     let uu____5981 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5982 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5981 uu____5982  in
                   paren_if_gt curr mine uu____5980)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5983;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6012 = levels op  in
              (match uu____6012 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6022 = str op  in
                     let uu____6023 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6024 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6022 uu____6023 uu____6024
                   else
                     (let uu____6026 =
                        let uu____6027 = str op  in
                        let uu____6028 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6029 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6027 uu____6028 uu____6029  in
                      paren_if_gt curr mine uu____6026))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6036 = levels op1  in
              (match uu____6036 with
               | (left1,mine,right1) ->
                   let uu____6046 =
                     let uu____6047 = str op1  in
                     let uu____6048 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6049 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6047 uu____6048 uu____6049  in
                   paren_if_gt curr mine uu____6046)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6068 =
                let uu____6069 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6070 =
                  let uu____6071 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6071 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6069 uu____6070  in
              braces_with_nesting uu____6068
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6076;_},e1::[])
              ->
              let uu____6080 =
                let uu____6081 = str "~"  in
                let uu____6082 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6081 uu____6082  in
              FStar_Pprint.group uu____6080
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6084;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6090 = levels op  in
                   (match uu____6090 with
                    | (left1,mine,right1) ->
                        let uu____6100 =
                          let uu____6101 = str op  in
                          let uu____6102 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6103 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6101 uu____6102 uu____6103  in
                        paren_if_gt curr mine uu____6100)
               | uu____6104 -> p_X e)
          | uu____6105 -> p_X e

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
        let uu____6112 =
          let uu____6113 = p_lident lid  in
          let uu____6114 =
            let uu____6115 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6115  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6113 uu____6114  in
        FStar_Pprint.group uu____6112
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6118 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6120 = p_appTerm e  in
    let uu____6121 =
      let uu____6122 =
        let uu____6123 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6123 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6122  in
    FStar_Pprint.op_Hat_Hat uu____6120 uu____6121

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6128 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6128 t phi
      | FStar_Parser_AST.TAnnotated uu____6129 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6134 ->
          let uu____6135 =
            let uu____6136 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6136
             in
          failwith uu____6135
      | FStar_Parser_AST.TVariable uu____6137 ->
          let uu____6138 =
            let uu____6139 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6139
             in
          failwith uu____6138
      | FStar_Parser_AST.NoName uu____6140 ->
          let uu____6141 =
            let uu____6142 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6142
             in
          failwith uu____6141

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6144  ->
      match uu____6144 with
      | (lid,e) ->
          let uu____6151 =
            let uu____6152 = p_qlident lid  in
            let uu____6153 =
              let uu____6154 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6154
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6152 uu____6153  in
          FStar_Pprint.group uu____6151

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6156 when is_general_application e ->
        let uu____6163 = head_and_args e  in
        (match uu____6163 with
         | (head1,args) ->
             let uu____6188 =
               let uu____6199 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6199
               then
                 let uu____6233 =
                   FStar_Util.take
                     (fun uu____6257  ->
                        match uu____6257 with
                        | (uu____6262,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6233 with
                 | (fs_typ_args,args1) ->
                     let uu____6300 =
                       let uu____6301 = p_indexingTerm head1  in
                       let uu____6302 =
                         let uu____6303 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6303 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6301 uu____6302  in
                     (uu____6300, args1)
               else
                 (let uu____6315 = p_indexingTerm head1  in
                  (uu____6315, args))
                in
             (match uu____6188 with
              | (head_doc,args1) ->
                  let uu____6336 =
                    let uu____6337 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6337 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6336))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6357 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6357)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6375 =
               let uu____6376 = p_quident lid  in
               let uu____6377 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6376 uu____6377  in
             FStar_Pprint.group uu____6375
         | hd1::tl1 ->
             let uu____6394 =
               let uu____6395 =
                 let uu____6396 =
                   let uu____6397 = p_quident lid  in
                   let uu____6398 = p_argTerm hd1  in
                   prefix2 uu____6397 uu____6398  in
                 FStar_Pprint.group uu____6396  in
               let uu____6399 =
                 let uu____6400 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6400  in
               FStar_Pprint.op_Hat_Hat uu____6395 uu____6399  in
             FStar_Pprint.group uu____6394)
    | uu____6405 -> p_indexingTerm e

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
         (let uu____6414 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6414 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6416 = str "#"  in
        let uu____6417 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6416 uu____6417
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6419  ->
    match uu____6419 with | (e,uu____6425) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6430;_},e1::e2::[])
          ->
          let uu____6435 =
            let uu____6436 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6437 =
              let uu____6438 =
                let uu____6439 = p_term false false e2  in
                soft_parens_with_nesting uu____6439  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6438  in
            FStar_Pprint.op_Hat_Hat uu____6436 uu____6437  in
          FStar_Pprint.group uu____6435
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6440;_},e1::e2::[])
          ->
          let uu____6445 =
            let uu____6446 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6447 =
              let uu____6448 =
                let uu____6449 = p_term false false e2  in
                soft_brackets_with_nesting uu____6449  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6448  in
            FStar_Pprint.op_Hat_Hat uu____6446 uu____6447  in
          FStar_Pprint.group uu____6445
      | uu____6450 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6455 = p_quident lid  in
        let uu____6456 =
          let uu____6457 =
            let uu____6458 = p_term false false e1  in
            soft_parens_with_nesting uu____6458  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6457  in
        FStar_Pprint.op_Hat_Hat uu____6455 uu____6456
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6464 =
          let uu____6465 = FStar_Ident.text_of_id op  in str uu____6465  in
        let uu____6466 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6464 uu____6466
    | uu____6467 -> p_atomicTermNotQUident e

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
         | uu____6476 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6483 =
          let uu____6484 = FStar_Ident.text_of_id op  in str uu____6484  in
        let uu____6485 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6483 uu____6485
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6489 =
          let uu____6490 =
            let uu____6491 =
              let uu____6492 = FStar_Ident.text_of_id op  in str uu____6492
               in
            let uu____6493 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6491 uu____6493  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6490  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6489
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6508 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6509 =
          let uu____6510 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6511 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6510 p_tmEq uu____6511  in
        let uu____6518 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6508 uu____6509 uu____6518
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6521 =
          let uu____6522 = p_atomicTermNotQUident e1  in
          let uu____6523 =
            let uu____6524 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6524  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6522 uu____6523
           in
        FStar_Pprint.group uu____6521
    | uu____6525 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6530 = p_quident constr_lid  in
        let uu____6531 =
          let uu____6532 =
            let uu____6533 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6533  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6532  in
        FStar_Pprint.op_Hat_Hat uu____6530 uu____6531
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6535 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6535 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6537 = p_term false false e1  in
        soft_parens_with_nesting uu____6537
    | uu____6538 when is_array e ->
        let es = extract_from_list e  in
        let uu____6542 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6543 =
          let uu____6544 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6544
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6547 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6542 uu____6543 uu____6547
    | uu____6548 when is_list e ->
        let uu____6549 =
          let uu____6550 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6551 = extract_from_list e  in
          separate_map_or_flow_last uu____6550
            (fun ps  -> p_noSeqTerm ps false) uu____6551
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6549 FStar_Pprint.rbracket
    | uu____6556 when is_lex_list e ->
        let uu____6557 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6558 =
          let uu____6559 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6560 = extract_from_list e  in
          separate_map_or_flow_last uu____6559
            (fun ps  -> p_noSeqTerm ps false) uu____6560
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6557 uu____6558 FStar_Pprint.rbracket
    | uu____6565 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6569 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6570 =
          let uu____6571 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6571 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6569 uu____6570 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6575 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6576 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6575 uu____6576
    | FStar_Parser_AST.Op (op,args) when
        let uu____6583 = handleable_op op args  in
        Prims.op_Negation uu____6583 ->
        let uu____6584 =
          let uu____6585 =
            let uu____6586 = FStar_Ident.text_of_id op  in
            let uu____6587 =
              let uu____6588 =
                let uu____6589 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6589
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6588  in
            Prims.strcat uu____6586 uu____6587  in
          Prims.strcat "Operation " uu____6585  in
        failwith uu____6584
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6591 = str "u#"  in
        let uu____6592 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6591 uu____6592
    | FStar_Parser_AST.Wild  ->
        let uu____6593 = p_term false false e  in
        soft_parens_with_nesting uu____6593
    | FStar_Parser_AST.Const uu____6594 ->
        let uu____6595 = p_term false false e  in
        soft_parens_with_nesting uu____6595
    | FStar_Parser_AST.Op uu____6596 ->
        let uu____6603 = p_term false false e  in
        soft_parens_with_nesting uu____6603
    | FStar_Parser_AST.Tvar uu____6604 ->
        let uu____6605 = p_term false false e  in
        soft_parens_with_nesting uu____6605
    | FStar_Parser_AST.Var uu____6606 ->
        let uu____6607 = p_term false false e  in
        soft_parens_with_nesting uu____6607
    | FStar_Parser_AST.Name uu____6608 ->
        let uu____6609 = p_term false false e  in
        soft_parens_with_nesting uu____6609
    | FStar_Parser_AST.Construct uu____6610 ->
        let uu____6621 = p_term false false e  in
        soft_parens_with_nesting uu____6621
    | FStar_Parser_AST.Abs uu____6622 ->
        let uu____6629 = p_term false false e  in
        soft_parens_with_nesting uu____6629
    | FStar_Parser_AST.App uu____6630 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Let uu____6638 ->
        let uu____6659 = p_term false false e  in
        soft_parens_with_nesting uu____6659
    | FStar_Parser_AST.LetOpen uu____6660 ->
        let uu____6665 = p_term false false e  in
        soft_parens_with_nesting uu____6665
    | FStar_Parser_AST.Seq uu____6666 ->
        let uu____6671 = p_term false false e  in
        soft_parens_with_nesting uu____6671
    | FStar_Parser_AST.Bind uu____6672 ->
        let uu____6679 = p_term false false e  in
        soft_parens_with_nesting uu____6679
    | FStar_Parser_AST.If uu____6680 ->
        let uu____6687 = p_term false false e  in
        soft_parens_with_nesting uu____6687
    | FStar_Parser_AST.Match uu____6688 ->
        let uu____6703 = p_term false false e  in
        soft_parens_with_nesting uu____6703
    | FStar_Parser_AST.TryWith uu____6704 ->
        let uu____6719 = p_term false false e  in
        soft_parens_with_nesting uu____6719
    | FStar_Parser_AST.Ascribed uu____6720 ->
        let uu____6729 = p_term false false e  in
        soft_parens_with_nesting uu____6729
    | FStar_Parser_AST.Record uu____6730 ->
        let uu____6743 = p_term false false e  in
        soft_parens_with_nesting uu____6743
    | FStar_Parser_AST.Project uu____6744 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.Product uu____6750 ->
        let uu____6757 = p_term false false e  in
        soft_parens_with_nesting uu____6757
    | FStar_Parser_AST.Sum uu____6758 ->
        let uu____6765 = p_term false false e  in
        soft_parens_with_nesting uu____6765
    | FStar_Parser_AST.QForall uu____6766 ->
        let uu____6779 = p_term false false e  in
        soft_parens_with_nesting uu____6779
    | FStar_Parser_AST.QExists uu____6780 ->
        let uu____6793 = p_term false false e  in
        soft_parens_with_nesting uu____6793
    | FStar_Parser_AST.Refine uu____6794 ->
        let uu____6799 = p_term false false e  in
        soft_parens_with_nesting uu____6799
    | FStar_Parser_AST.NamedTyp uu____6800 ->
        let uu____6805 = p_term false false e  in
        soft_parens_with_nesting uu____6805
    | FStar_Parser_AST.Requires uu____6806 ->
        let uu____6813 = p_term false false e  in
        soft_parens_with_nesting uu____6813
    | FStar_Parser_AST.Ensures uu____6814 ->
        let uu____6821 = p_term false false e  in
        soft_parens_with_nesting uu____6821
    | FStar_Parser_AST.Attributes uu____6822 ->
        let uu____6825 = p_term false false e  in
        soft_parens_with_nesting uu____6825
    | FStar_Parser_AST.Quote uu____6826 ->
        let uu____6831 = p_term false false e  in
        soft_parens_with_nesting uu____6831
    | FStar_Parser_AST.VQuote uu____6832 ->
        let uu____6833 = p_term false false e  in
        soft_parens_with_nesting uu____6833
    | FStar_Parser_AST.Antiquote uu____6834 ->
        let uu____6839 = p_term false false e  in
        soft_parens_with_nesting uu____6839

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___115_6840  ->
    match uu___115_6840 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6846) ->
        let uu____6847 = str s  in FStar_Pprint.dquotes uu____6847
    | FStar_Const.Const_bytearray (bytes,uu____6849) ->
        let uu____6854 =
          let uu____6855 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6855  in
        let uu____6856 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6854 uu____6856
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___113_6876 =
          match uu___113_6876 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___114_6882 =
          match uu___114_6882 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6893  ->
               match uu____6893 with
               | (s,w) ->
                   let uu____6900 = signedness s  in
                   let uu____6901 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6900 uu____6901)
            sign_width_opt
           in
        let uu____6902 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6902 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6904 = FStar_Range.string_of_range r  in str uu____6904
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6906 = p_quident lid  in
        let uu____6907 =
          let uu____6908 =
            let uu____6909 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6909  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6908  in
        FStar_Pprint.op_Hat_Hat uu____6906 uu____6907

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6911 = str "u#"  in
    let uu____6912 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6911 uu____6912

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6914;_},u1::u2::[])
        ->
        let uu____6919 =
          let uu____6920 = p_universeFrom u1  in
          let uu____6921 =
            let uu____6922 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6922  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6920 uu____6921  in
        FStar_Pprint.group uu____6919
    | FStar_Parser_AST.App uu____6923 ->
        let uu____6930 = head_and_args u  in
        (match uu____6930 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6956 =
                    let uu____6957 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6958 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6966  ->
                           match uu____6966 with
                           | (u1,uu____6972) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6957 uu____6958  in
                  FStar_Pprint.group uu____6956
              | uu____6973 ->
                  let uu____6974 =
                    let uu____6975 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6975
                     in
                  failwith uu____6974))
    | uu____6976 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6999 = FStar_Ident.text_of_id id1  in str uu____6999
    | FStar_Parser_AST.Paren u1 ->
        let uu____7001 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7001
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7002;_},uu____7003::uu____7004::[])
        ->
        let uu____7007 = p_universeFrom u  in
        soft_parens_with_nesting uu____7007
    | FStar_Parser_AST.App uu____7008 ->
        let uu____7015 = p_universeFrom u  in
        soft_parens_with_nesting uu____7015
    | uu____7016 ->
        let uu____7017 =
          let uu____7018 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7018
           in
        failwith uu____7017

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
       | FStar_Parser_AST.Module (uu____7098,decls) ->
           let uu____7104 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7104
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7113,decls,uu____7115) ->
           let uu____7120 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7120
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7177  ->
         match uu____7177 with | (comment,range) -> str comment) comments
  
let (extract_decl_range : FStar_Parser_AST.decl -> decl_meta) =
  fun d  ->
    let has_qs =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7193)) -> false
      | ([],uu____7196) -> false
      | uu____7199 -> true  in
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
        | FStar_Parser_AST.Module (uu____7243,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7249,decls,uu____7251) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7300 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7313;
                 FStar_Parser_AST.doc = uu____7314;
                 FStar_Parser_AST.quals = uu____7315;
                 FStar_Parser_AST.attrs = uu____7316;_}::uu____7317 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7323 =
                   let uu____7326 =
                     let uu____7329 = FStar_List.tl ds  in d :: uu____7329
                      in
                   d0 :: uu____7326  in
                 (uu____7323, (d0.FStar_Parser_AST.drange))
             | uu____7334 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7300 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7392 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7392 dummy_meta
                      FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty p_decl decls1 extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7500 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7500, comments1))))))
  