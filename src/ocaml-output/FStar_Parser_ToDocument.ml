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
let with_comment :
  'Auu____2072 .
    ('Auu____2072 -> FStar_Pprint.document) ->
      'Auu____2072 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2113 = FStar_ST.op_Bang comment_stack  in
          match uu____2113 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2176 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2176
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2217 =
                    let uu____2218 =
                      let uu____2219 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2219
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2218  in
                  comments_before_pos uu____2217 print_pos lookahead_pos))
              else
                (let uu____2221 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2221))
           in
        let uu____2222 =
          let uu____2227 =
            let uu____2228 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2228  in
          let uu____2229 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2227 uu____2229  in
        match uu____2222 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2235 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2235
              else comments  in
            let uu____2241 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2241
  
let rec place_comments_until_pos :
  'Auu____2255 .
    Prims.int ->
      Prims.int ->
        FStar_Range.pos ->
          'Auu____2255 -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun end_correction  ->
          fun doc1  ->
            let uu____2281 = FStar_ST.op_Bang comment_stack  in
            match uu____2281 with
            | (comment,crange)::cs when
                FStar_Range.range_before_pos crange pos_end ->
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let lnum =
                    let uu____2373 =
                      let uu____2374 =
                        let uu____2375 = FStar_Range.start_of_range crange
                           in
                        FStar_Range.line_of_pos uu____2375  in
                      uu____2374 - lbegin  in
                    max k uu____2373  in
                  let lnum1 = min (Prims.parse_int "2") lnum  in
                  let doc2 =
                    let uu____2378 =
                      let uu____2379 =
                        FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                      let uu____2380 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2379 uu____2380  in
                    FStar_Pprint.op_Hat_Hat doc1 uu____2378  in
                  let uu____2381 =
                    let uu____2382 = FStar_Range.end_of_range crange  in
                    FStar_Range.line_of_pos uu____2382  in
                  place_comments_until_pos (Prims.parse_int "1") uu____2381
                    pos_end end_correction doc2))
            | uu____2383 ->
                if doc1 = FStar_Pprint.empty
                then FStar_Pprint.empty
                else
                  (let lnum' =
                     let uu____2392 = FStar_Range.line_of_pos pos_end  in
                     uu____2392 - lbegin  in
                   let lnum = min (Prims.parse_int "2") lnum'  in
                   let uu____2394 =
                     let uu____2395 =
                       FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                     let uu____2396 =
                       let uu____2397 =
                         let uu____2398 = FStar_Util.string_of_int lbegin  in
                         FStar_All.pipe_left str uu____2398  in
                       let uu____2399 =
                         let uu____2400 = str "*"  in
                         let uu____2401 =
                           let uu____2402 =
                             let uu____2403 = FStar_Range.line_of_pos pos_end
                                in
                             FStar_Util.string_of_int uu____2403  in
                           FStar_All.pipe_left str uu____2402  in
                         FStar_Pprint.op_Hat_Hat uu____2400 uu____2401  in
                       FStar_Pprint.op_Hat_Hat uu____2397 uu____2399  in
                     FStar_Pprint.op_Hat_Hat uu____2395 uu____2396  in
                   FStar_Pprint.op_Hat_Hat doc1 uu____2394)
  
let separate_map_with_comments :
  'Auu____2418 'Auu____2419 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2418 -> FStar_Pprint.document) ->
          'Auu____2418 Prims.list ->
            ('Auu____2418 ->
               (FStar_Range.range,'Auu____2419)
                 FStar_Pervasives_Native.tuple2)
              -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2484 x =
              match uu____2484 with
              | (last_line,doc1) ->
                  let uu____2496 = extract_range x  in
                  (match uu____2496 with
                   | (r,c) ->
                       let doc2 =
                         let uu____2508 = FStar_Range.start_of_range r  in
                         place_comments_until_pos (Prims.parse_int "1")
                           last_line uu____2508 c doc1
                          in
                       let uu____2509 =
                         let uu____2510 = FStar_Range.end_of_range r  in
                         FStar_Range.line_of_pos uu____2510  in
                       let uu____2511 =
                         let uu____2512 =
                           let uu____2513 = f x  in
                           FStar_Pprint.op_Hat_Hat sep uu____2513  in
                         FStar_Pprint.op_Hat_Hat doc2 uu____2512  in
                       (uu____2509, uu____2511))
               in
            let uu____2514 =
              let uu____2521 = FStar_List.hd xs  in
              let uu____2522 = FStar_List.tl xs  in (uu____2521, uu____2522)
               in
            match uu____2514 with
            | (x,xs1) ->
                let init1 =
                  let uu____2538 = extract_range x  in
                  match uu____2538 with
                  | (r,c) ->
                      let uu____2549 =
                        let uu____2550 = FStar_Range.end_of_range r  in
                        FStar_Range.line_of_pos uu____2550  in
                      let uu____2551 =
                        let uu____2552 = f x  in
                        FStar_Pprint.op_Hat_Hat prefix1 uu____2552  in
                      (uu____2549, uu____2551)
                   in
                let uu____2553 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2553
  
let separate_map_with_comments_kw :
  'Auu____2578 'Auu____2579 'Auu____2580 .
    'Auu____2578 ->
      'Auu____2578 ->
        ('Auu____2578 -> 'Auu____2579 -> FStar_Pprint.document) ->
          'Auu____2579 Prims.list ->
            ('Auu____2579 ->
               (FStar_Range.range,'Auu____2580)
                 FStar_Pervasives_Native.tuple2)
              -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2650 x =
              match uu____2650 with
              | (last_line,doc1) ->
                  let uu____2662 = extract_range x  in
                  (match uu____2662 with
                   | (r,c) ->
                       let doc2 =
                         let uu____2674 = FStar_Range.start_of_range r  in
                         place_comments_until_pos (Prims.parse_int "1")
                           last_line uu____2674 c doc1
                          in
                       let uu____2675 =
                         let uu____2676 = FStar_Range.end_of_range r  in
                         FStar_Range.line_of_pos uu____2676  in
                       let uu____2677 =
                         let uu____2678 = f sep x  in
                         FStar_Pprint.op_Hat_Hat doc2 uu____2678  in
                       (uu____2675, uu____2677))
               in
            let uu____2679 =
              let uu____2686 = FStar_List.hd xs  in
              let uu____2687 = FStar_List.tl xs  in (uu____2686, uu____2687)
               in
            match uu____2679 with
            | (x,xs1) ->
                let init1 =
                  let uu____2703 = extract_range x  in
                  match uu____2703 with
                  | (r,c) ->
                      let uu____2714 =
                        let uu____2715 = FStar_Range.end_of_range r  in
                        FStar_Range.line_of_pos uu____2715  in
                      let uu____2716 = f prefix1 x  in
                      (uu____2714, uu____2716)
                   in
                let uu____2717 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2717
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3427)) ->
          let uu____3430 =
            let uu____3431 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3431 FStar_Util.is_upper  in
          if uu____3430
          then
            let uu____3434 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3434 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3436 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3443 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3444 =
      let uu____3445 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3446 =
        let uu____3447 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3447  in
      FStar_Pprint.op_Hat_Hat uu____3445 uu____3446  in
    FStar_Pprint.op_Hat_Hat uu____3443 uu____3444

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3449 ->
        let uu____3450 =
          let uu____3451 = str "@ "  in
          let uu____3452 =
            let uu____3453 =
              let uu____3454 =
                let uu____3455 =
                  let uu____3456 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3456  in
                FStar_Pprint.op_Hat_Hat uu____3455 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3454  in
            FStar_Pprint.op_Hat_Hat uu____3453 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3451 uu____3452  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3450

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3459  ->
    match uu____3459 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3495 =
                match uu____3495 with
                | (kwd,arg) ->
                    let uu____3502 = str "@"  in
                    let uu____3503 =
                      let uu____3504 = str kwd  in
                      let uu____3505 =
                        let uu____3506 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3506
                         in
                      FStar_Pprint.op_Hat_Hat uu____3504 uu____3505  in
                    FStar_Pprint.op_Hat_Hat uu____3502 uu____3503
                 in
              let uu____3507 =
                let uu____3508 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3508 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3507
           in
        let uu____3513 =
          let uu____3514 =
            let uu____3515 =
              let uu____3516 = str doc1  in
              let uu____3517 =
                let uu____3518 =
                  let uu____3519 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                      FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3519  in
                FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3518  in
              FStar_Pprint.op_Hat_Hat uu____3516 uu____3517  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3515  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3514  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3513

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3523 =
          let uu____3524 = str "val"  in
          let uu____3525 =
            let uu____3526 =
              let uu____3527 = p_lident lid  in
              let uu____3528 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3527 uu____3528  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3526  in
          FStar_Pprint.op_Hat_Hat uu____3524 uu____3525  in
        let uu____3529 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3523 uu____3529
    | FStar_Parser_AST.TopLevelLet (uu____3530,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3555 =
               let uu____3556 = str "let"  in p_letlhs uu____3556 lb  in
             FStar_Pprint.group uu____3555) lbs
    | uu____3557 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___104_3572 =
          match uu___104_3572 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3580 = f x  in
              let uu____3581 =
                let uu____3582 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3582  in
              FStar_Pprint.op_Hat_Hat uu____3580 uu____3581
           in
        let uu____3583 = str "["  in
        let uu____3584 =
          let uu____3585 = p_list' l  in
          let uu____3586 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3585 uu____3586  in
        FStar_Pprint.op_Hat_Hat uu____3583 uu____3584

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3589 =
          let uu____3590 = str "open"  in
          let uu____3591 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3590 uu____3591  in
        FStar_Pprint.group uu____3589
    | FStar_Parser_AST.Include uid ->
        let uu____3593 =
          let uu____3594 = str "include"  in
          let uu____3595 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3594 uu____3595  in
        FStar_Pprint.group uu____3593
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3598 =
          let uu____3599 = str "module"  in
          let uu____3600 =
            let uu____3601 =
              let uu____3602 = p_uident uid1  in
              let uu____3603 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3602 uu____3603  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3601  in
          FStar_Pprint.op_Hat_Hat uu____3599 uu____3600  in
        let uu____3604 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3598 uu____3604
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3606 =
          let uu____3607 = str "module"  in
          let uu____3608 =
            let uu____3609 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3609  in
          FStar_Pprint.op_Hat_Hat uu____3607 uu____3608  in
        FStar_Pprint.group uu____3606
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3642 = str "effect"  in
          let uu____3643 =
            let uu____3644 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3644  in
          FStar_Pprint.op_Hat_Hat uu____3642 uu____3643  in
        let uu____3645 =
          let uu____3646 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3646 FStar_Pprint.equals
           in
        let uu____3647 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3645 uu____3647
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3665 =
          let uu____3666 = str "type"  in
          let uu____3667 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3666 uu____3667  in
        let uu____3680 =
          let uu____3681 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3719 =
                    let uu____3720 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3720 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3719)) uu____3681
           in
        FStar_Pprint.op_Hat_Hat uu____3665 uu____3680
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3736 = str "let"  in
          let uu____3737 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3736 uu____3737  in
        let uu____3738 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3738 p_letbinding lbs
          (fun uu____3747  ->
             match uu____3747 with
             | (p,t) ->
                 let uu____3758 =
                   FStar_Range.union_ranges p.FStar_Parser_AST.prange
                     t.FStar_Parser_AST.range
                    in
                 (uu____3758, (Prims.parse_int "0")))
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3761 = str "val"  in
        let uu____3762 =
          let uu____3763 =
            let uu____3764 = p_lident lid  in
            let uu____3765 =
              let uu____3766 =
                let uu____3767 =
                  let uu____3768 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3768  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3767  in
              FStar_Pprint.group uu____3766  in
            FStar_Pprint.op_Hat_Hat uu____3764 uu____3765  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3763  in
        FStar_Pprint.op_Hat_Hat uu____3761 uu____3762
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3772 =
            let uu____3773 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3773 FStar_Util.is_upper  in
          if uu____3772
          then FStar_Pprint.empty
          else
            (let uu____3777 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3777 FStar_Pprint.space)
           in
        let uu____3778 =
          let uu____3779 = p_ident id1  in
          let uu____3780 =
            let uu____3781 =
              let uu____3782 =
                let uu____3783 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3783  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3782  in
            FStar_Pprint.group uu____3781  in
          FStar_Pprint.op_Hat_Hat uu____3779 uu____3780  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3778
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3790 = str "exception"  in
        let uu____3791 =
          let uu____3792 =
            let uu____3793 = p_uident uid  in
            let uu____3794 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3798 =
                     let uu____3799 = str "of"  in
                     let uu____3800 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3799 uu____3800  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3798) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3793 uu____3794  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3792  in
        FStar_Pprint.op_Hat_Hat uu____3790 uu____3791
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3802 = str "new_effect"  in
        let uu____3803 =
          let uu____3804 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3804  in
        FStar_Pprint.op_Hat_Hat uu____3802 uu____3803
    | FStar_Parser_AST.SubEffect se ->
        let uu____3806 = str "sub_effect"  in
        let uu____3807 =
          let uu____3808 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3808  in
        FStar_Pprint.op_Hat_Hat uu____3806 uu____3807
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3811 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3811 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3812 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3813) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3836 = str "%splice"  in
        let uu____3837 =
          let uu____3838 =
            let uu____3839 = str ";"  in p_list p_uident uu____3839 ids  in
          let uu____3840 =
            let uu____3841 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3841  in
          FStar_Pprint.op_Hat_Hat uu____3838 uu____3840  in
        FStar_Pprint.op_Hat_Hat uu____3836 uu____3837

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___105_3842  ->
    match uu___105_3842 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3844 = str "#set-options"  in
        let uu____3845 =
          let uu____3846 =
            let uu____3847 = str s  in FStar_Pprint.dquotes uu____3847  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3846  in
        FStar_Pprint.op_Hat_Hat uu____3844 uu____3845
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3851 = str "#reset-options"  in
        let uu____3852 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3856 =
                 let uu____3857 = str s  in FStar_Pprint.dquotes uu____3857
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3856) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3851 uu____3852
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
    fun uu____3886  ->
      match uu____3886 with
      | (typedecl,fsdoc_opt) ->
          let uu____3899 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3899 with
           | (decl,body) ->
               let uu____3917 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3917)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___106_3919  ->
      match uu___106_3919 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3949 = FStar_Pprint.empty  in
          let uu____3950 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3950, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3971 =
            let uu____3972 = p_typ false false t  in jump2 uu____3972  in
          let uu____3973 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3973, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4027 =
            match uu____4027 with
            | (lid1,t,doc_opt) ->
                let uu____4043 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4043
             in
          let p_fields uu____4059 =
            let uu____4060 =
              let uu____4061 =
                let uu____4062 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4062 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4061  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4060  in
          let uu____4071 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4071, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4132 =
            match uu____4132 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4158 =
                    let uu____4159 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4159  in
                  FStar_Range.extend_to_end_of_line uu____4158  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4185 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4198 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4198,
            ((fun uu____4204  ->
                let uu____4205 = datacon_doc ()  in jump2 uu____4205)))

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
  fun uu____4206  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4206 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4240 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4240  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4242 =
                        let uu____4245 =
                          let uu____4248 = p_fsdoc fsdoc  in
                          let uu____4249 =
                            let uu____4252 = cont lid_doc  in [uu____4252]
                             in
                          uu____4248 :: uu____4249  in
                        kw :: uu____4245  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4242
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4257 =
                        let uu____4258 =
                          let uu____4259 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4259 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4258
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4257
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4274 =
                          let uu____4275 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4275  in
                        prefix2 uu____4274 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4277  ->
      match uu____4277 with
      | (lid,t,doc_opt) ->
          let uu____4293 =
            let uu____4294 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4295 =
              let uu____4296 = p_lident lid  in
              let uu____4297 =
                let uu____4298 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4298  in
              FStar_Pprint.op_Hat_Hat uu____4296 uu____4297  in
            FStar_Pprint.op_Hat_Hat uu____4294 uu____4295  in
          FStar_Pprint.group uu____4293

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4299  ->
    match uu____4299 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4327 =
            let uu____4328 =
              let uu____4329 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4329  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4328  in
          FStar_Pprint.group uu____4327  in
        let uu____4330 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4331 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4335 =
                 let uu____4336 =
                   let uu____4337 =
                     let uu____4338 =
                       let uu____4339 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4339
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4338  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4337  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4336  in
               FStar_Pprint.group uu____4335) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4330 uu____4331

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4341  ->
      match uu____4341 with
      | (pat,uu____4347) ->
          let uu____4348 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4367 =
                  let uu____4368 =
                    let uu____4369 =
                      let uu____4370 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4370
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4369  in
                  FStar_Pprint.group uu____4368  in
                (pat1, uu____4367)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4382 =
                  let uu____4383 =
                    let uu____4384 =
                      let uu____4385 =
                        let uu____4386 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4386
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4385
                       in
                    FStar_Pprint.group uu____4384  in
                  let uu____4387 =
                    let uu____4388 =
                      let uu____4389 = str "by"  in
                      let uu____4390 =
                        let uu____4391 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4391
                         in
                      FStar_Pprint.op_Hat_Hat uu____4389 uu____4390  in
                    FStar_Pprint.group uu____4388  in
                  FStar_Pprint.op_Hat_Hat uu____4383 uu____4387  in
                (pat1, uu____4382)
            | uu____4392 -> (pat, FStar_Pprint.empty)  in
          (match uu____4348 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4396);
                       FStar_Parser_AST.prange = uu____4397;_},pats)
                    ->
                    let uu____4407 =
                      let uu____4408 =
                        let uu____4409 =
                          let uu____4410 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4410  in
                        FStar_Pprint.group uu____4409  in
                      let uu____4411 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4408 uu____4411  in
                    prefix2_nonempty uu____4407 ascr_doc
                | uu____4412 ->
                    let uu____4413 =
                      let uu____4414 =
                        let uu____4415 =
                          let uu____4416 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4416  in
                        FStar_Pprint.group uu____4415  in
                      FStar_Pprint.op_Hat_Hat uu____4414 ascr_doc  in
                    FStar_Pprint.group uu____4413))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4418  ->
      match uu____4418 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4427 =
            let uu____4428 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4428  in
          let uu____4429 =
            let uu____4430 =
              let uu____4431 =
                let uu____4432 =
                  let uu____4433 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4433  in
                FStar_Pprint.group uu____4432  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4431  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4430  in
          FStar_Pprint.ifflat uu____4427 uu____4429

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___107_4434  ->
    match uu___107_4434 with
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
        let uu____4459 = p_uident uid  in
        let uu____4460 = p_binders true bs  in
        let uu____4461 =
          let uu____4462 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4462  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4459 uu____4460 uu____4461

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
          let uu____4472 =
            let uu____4473 =
              let uu____4474 =
                let uu____4475 = p_uident uid  in
                let uu____4476 = p_binders true bs  in
                let uu____4477 =
                  let uu____4478 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4478  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4475 uu____4476 uu____4477
                 in
              FStar_Pprint.group uu____4474  in
            let uu____4479 =
              let uu____4480 = str "with"  in
              let uu____4481 =
                let uu____4482 =
                  let uu____4483 =
                    let uu____4484 =
                      let uu____4485 =
                        let uu____4486 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4486
                         in
                      separate_map_last uu____4485 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4484  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4483  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4482  in
              FStar_Pprint.op_Hat_Hat uu____4480 uu____4481  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4473 uu____4479  in
          braces_with_nesting uu____4472

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
          let uu____4517 =
            let uu____4518 = p_lident lid  in
            let uu____4519 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4518 uu____4519  in
          let uu____4520 = p_simpleTerm ps false e  in
          prefix2 uu____4517 uu____4520
      | uu____4521 ->
          let uu____4522 =
            let uu____4523 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4523
             in
          failwith uu____4522

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4585 =
        match uu____4585 with
        | (kwd,t) ->
            let uu____4592 =
              let uu____4593 = str kwd  in
              let uu____4594 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4593 uu____4594  in
            let uu____4595 = p_simpleTerm ps false t  in
            prefix2 uu____4592 uu____4595
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4600 =
      let uu____4601 =
        let uu____4602 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4603 =
          let uu____4604 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4604  in
        FStar_Pprint.op_Hat_Hat uu____4602 uu____4603  in
      let uu____4605 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4601 uu____4605  in
    let uu____4606 =
      let uu____4607 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4607  in
    FStar_Pprint.op_Hat_Hat uu____4600 uu____4606

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___108_4608  ->
    match uu___108_4608 with
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
        let uu____4611 = p_qualifier q  in
        FStar_Pprint.op_Hat_Hat uu____4611 FStar_Pprint.hardline
    | uu____4612 ->
        let uu____4613 =
          let uu____4614 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4614  in
        FStar_Pprint.op_Hat_Hat uu____4613 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___109_4617  ->
    match uu___109_4617 with
    | FStar_Parser_AST.Rec  ->
        let uu____4618 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4618
    | FStar_Parser_AST.Mutable  ->
        let uu____4619 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4619
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___110_4620  ->
    match uu___110_4620 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4625 =
          let uu____4626 =
            let uu____4627 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4627  in
          FStar_Pprint.separate_map uu____4626 p_tuplePattern pats  in
        FStar_Pprint.group uu____4625
    | uu____4628 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4635 =
          let uu____4636 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4636 p_constructorPattern pats  in
        FStar_Pprint.group uu____4635
    | uu____4637 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4640;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4645 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4646 = p_constructorPattern hd1  in
        let uu____4647 = p_constructorPattern tl1  in
        infix0 uu____4645 uu____4646 uu____4647
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4649;_},pats)
        ->
        let uu____4655 = p_quident uid  in
        let uu____4656 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4655 uu____4656
    | uu____4657 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4673;
               FStar_Parser_AST.blevel = uu____4674;
               FStar_Parser_AST.aqual = uu____4675;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4681 =
               let uu____4682 = p_ident lid  in
               p_refinement aqual uu____4682 t1 phi  in
             soft_parens_with_nesting uu____4681
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4684;
               FStar_Parser_AST.blevel = uu____4685;
               FStar_Parser_AST.aqual = uu____4686;_},phi))
             ->
             let uu____4688 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4688
         | uu____4689 ->
             let uu____4694 =
               let uu____4695 = p_tuplePattern pat  in
               let uu____4696 =
                 let uu____4697 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4697
                  in
               FStar_Pprint.op_Hat_Hat uu____4695 uu____4696  in
             soft_parens_with_nesting uu____4694)
    | FStar_Parser_AST.PatList pats ->
        let uu____4701 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4701 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4718 =
          match uu____4718 with
          | (lid,pat) ->
              let uu____4725 = p_qlident lid  in
              let uu____4726 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4725 uu____4726
           in
        let uu____4727 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4727
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4737 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4738 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4739 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4737 uu____4738 uu____4739
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4748 =
          let uu____4749 =
            let uu____4750 =
              let uu____4751 = FStar_Ident.text_of_id op  in str uu____4751
               in
            let uu____4752 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4750 uu____4752  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4749  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4748
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4760 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4761 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4760 uu____4761
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4763 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4766;
           FStar_Parser_AST.prange = uu____4767;_},uu____4768)
        ->
        let uu____4773 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4773
    | FStar_Parser_AST.PatTuple (uu____4774,false ) ->
        let uu____4779 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4779
    | uu____4780 ->
        let uu____4781 =
          let uu____4782 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4782  in
        failwith uu____4781

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4784;_},uu____4785)
        -> true
    | uu____4790 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4794 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4795 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4794 uu____4795
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4802;
                   FStar_Parser_AST.blevel = uu____4803;
                   FStar_Parser_AST.aqual = uu____4804;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4806 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4806 t1 phi
            | uu____4807 ->
                let t' =
                  let uu____4809 = is_typ_tuple t  in
                  if uu____4809
                  then
                    let uu____4810 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4810
                  else p_tmFormula t  in
                let uu____4812 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4813 =
                  let uu____4814 = p_lident lid  in
                  let uu____4815 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4814 uu____4815  in
                FStar_Pprint.op_Hat_Hat uu____4812 uu____4813
             in
          if is_atomic
          then
            let uu____4816 =
              let uu____4817 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4817  in
            FStar_Pprint.group uu____4816
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4819 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4826;
                  FStar_Parser_AST.blevel = uu____4827;
                  FStar_Parser_AST.aqual = uu____4828;_},phi)
               ->
               if is_atomic
               then
                 let uu____4830 =
                   let uu____4831 =
                     let uu____4832 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4832 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4831  in
                 FStar_Pprint.group uu____4830
               else
                 (let uu____4834 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4834)
           | uu____4835 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4844 -> false
            | FStar_Parser_AST.App uu____4855 -> false
            | FStar_Parser_AST.Op uu____4862 -> false
            | uu____4869 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4873 =
            let uu____4874 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4875 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4874 uu____4875  in
          let uu____4876 =
            let uu____4877 = p_appTerm t  in
            let uu____4878 =
              let uu____4879 =
                let uu____4880 =
                  let uu____4881 = soft_braces_with_nesting_tight phi1  in
                  let uu____4882 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4881 uu____4882  in
                FStar_Pprint.group uu____4880  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4879
               in
            FStar_Pprint.op_Hat_Hat uu____4877 uu____4878  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4873 uu____4876

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4893 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4893

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4898 = FStar_Ident.text_of_id lid  in str uu____4898)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4901 = FStar_Ident.text_of_lid lid  in str uu____4901)

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
            let uu____4919 =
              let uu____4920 =
                let uu____4921 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4921 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4920  in
            let uu____4922 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4919 uu____4922
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4926 =
              let uu____4927 =
                let uu____4928 =
                  let uu____4929 = p_lident x  in
                  let uu____4930 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4929 uu____4930  in
                let uu____4931 =
                  let uu____4932 = p_noSeqTerm true false e1  in
                  let uu____4933 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4932 uu____4933  in
                op_Hat_Slash_Plus_Hat uu____4928 uu____4931  in
              FStar_Pprint.group uu____4927  in
            let uu____4934 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4926 uu____4934
        | uu____4935 ->
            let uu____4936 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4936

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
            let uu____4947 =
              let uu____4948 = p_tmIff e1  in
              let uu____4949 =
                let uu____4950 =
                  let uu____4951 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4951
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4950  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4948 uu____4949  in
            FStar_Pprint.group uu____4947
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4957 =
              let uu____4958 = p_tmIff e1  in
              let uu____4959 =
                let uu____4960 =
                  let uu____4961 =
                    let uu____4962 = p_typ false false t  in
                    let uu____4963 =
                      let uu____4964 = str "by"  in
                      let uu____4965 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4964 uu____4965  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4962 uu____4963  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4961
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4960  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4958 uu____4959  in
            FStar_Pprint.group uu____4957
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4966;_},e1::e2::e3::[])
            ->
            let uu____4972 =
              let uu____4973 =
                let uu____4974 =
                  let uu____4975 = p_atomicTermNotQUident e1  in
                  let uu____4976 =
                    let uu____4977 =
                      let uu____4978 =
                        let uu____4979 = p_term false false e2  in
                        soft_parens_with_nesting uu____4979  in
                      let uu____4980 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4978 uu____4980  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4977  in
                  FStar_Pprint.op_Hat_Hat uu____4975 uu____4976  in
                FStar_Pprint.group uu____4974  in
              let uu____4981 =
                let uu____4982 = p_noSeqTerm ps pb e3  in jump2 uu____4982
                 in
              FStar_Pprint.op_Hat_Hat uu____4973 uu____4981  in
            FStar_Pprint.group uu____4972
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4983;_},e1::e2::e3::[])
            ->
            let uu____4989 =
              let uu____4990 =
                let uu____4991 =
                  let uu____4992 = p_atomicTermNotQUident e1  in
                  let uu____4993 =
                    let uu____4994 =
                      let uu____4995 =
                        let uu____4996 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4996  in
                      let uu____4997 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4995 uu____4997  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4994  in
                  FStar_Pprint.op_Hat_Hat uu____4992 uu____4993  in
                FStar_Pprint.group uu____4991  in
              let uu____4998 =
                let uu____4999 = p_noSeqTerm ps pb e3  in jump2 uu____4999
                 in
              FStar_Pprint.op_Hat_Hat uu____4990 uu____4998  in
            FStar_Pprint.group uu____4989
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5007 =
              let uu____5008 = str "requires"  in
              let uu____5009 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5008 uu____5009  in
            FStar_Pprint.group uu____5007
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5017 =
              let uu____5018 = str "ensures"  in
              let uu____5019 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5018 uu____5019  in
            FStar_Pprint.group uu____5017
        | FStar_Parser_AST.Attributes es ->
            let uu____5023 =
              let uu____5024 = str "attributes"  in
              let uu____5025 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5024 uu____5025  in
            FStar_Pprint.group uu____5023
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5029 =
                let uu____5030 =
                  let uu____5031 = str "if"  in
                  let uu____5032 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5031 uu____5032  in
                let uu____5033 =
                  let uu____5034 = str "then"  in
                  let uu____5035 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5034 uu____5035  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5030 uu____5033  in
              FStar_Pprint.group uu____5029
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5038,uu____5039,e31) when
                     is_unit e31 ->
                     let uu____5041 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5041
                 | uu____5042 -> p_noSeqTerm false false e2  in
               let uu____5043 =
                 let uu____5044 =
                   let uu____5045 = str "if"  in
                   let uu____5046 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5045 uu____5046  in
                 let uu____5047 =
                   let uu____5048 =
                     let uu____5049 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5049 e2_doc  in
                   let uu____5050 =
                     let uu____5051 = str "else"  in
                     let uu____5052 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5051 uu____5052  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5048 uu____5050  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5044 uu____5047  in
               FStar_Pprint.group uu____5043)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5075 =
              let uu____5076 =
                let uu____5077 =
                  let uu____5078 = str "try"  in
                  let uu____5079 = p_noSeqTerm false false e1  in
                  prefix2 uu____5078 uu____5079  in
                let uu____5080 =
                  let uu____5081 = str "with"  in
                  let uu____5082 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5081 uu____5082  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5077 uu____5080  in
              FStar_Pprint.group uu____5076  in
            let uu____5091 = paren_if (ps || pb)  in uu____5091 uu____5075
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5118 =
              let uu____5119 =
                let uu____5120 =
                  let uu____5121 = str "match"  in
                  let uu____5122 = p_noSeqTerm false false e1  in
                  let uu____5123 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5121 uu____5122 uu____5123
                   in
                let uu____5124 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5120 uu____5124  in
              FStar_Pprint.group uu____5119  in
            let uu____5133 = paren_if (ps || pb)  in uu____5133 uu____5118
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5140 =
              let uu____5141 =
                let uu____5142 =
                  let uu____5143 = str "let open"  in
                  let uu____5144 = p_quident uid  in
                  let uu____5145 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5143 uu____5144 uu____5145
                   in
                let uu____5146 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5142 uu____5146  in
              FStar_Pprint.group uu____5141  in
            let uu____5147 = paren_if ps  in uu____5147 uu____5140
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5211 is_last =
              match uu____5211 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5244 =
                          let uu____5245 = str "let"  in
                          let uu____5246 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5245 uu____5246
                           in
                        FStar_Pprint.group uu____5244
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5247 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5252 =
                    if is_last
                    then
                      let uu____5253 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5254 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5253 doc_expr uu____5254
                    else
                      (let uu____5256 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5256)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5252
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5302 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5302
                     else
                       (let uu____5310 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5310)) lbs
               in
            let lbs_doc =
              let uu____5318 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5318  in
            let uu____5319 =
              let uu____5320 =
                let uu____5321 =
                  let uu____5322 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5322
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5321  in
              FStar_Pprint.group uu____5320  in
            let uu____5323 = paren_if ps  in uu____5323 uu____5319
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5330;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5333;
                                                             FStar_Parser_AST.level
                                                               = uu____5334;_})
            when matches_var maybe_x x ->
            let uu____5361 =
              let uu____5362 =
                let uu____5363 = str "function"  in
                let uu____5364 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5363 uu____5364  in
              FStar_Pprint.group uu____5362  in
            let uu____5373 = paren_if (ps || pb)  in uu____5373 uu____5361
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5379 =
              let uu____5380 = str "quote"  in
              let uu____5381 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5380 uu____5381  in
            FStar_Pprint.group uu____5379
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5383 =
              let uu____5384 = str "`"  in
              let uu____5385 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5384 uu____5385  in
            FStar_Pprint.group uu____5383
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5387 =
              let uu____5388 = str "%`"  in
              let uu____5389 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5388 uu____5389  in
            FStar_Pprint.group uu____5387
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5391 =
              let uu____5392 = str "`#"  in
              let uu____5393 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5392 uu____5393  in
            FStar_Pprint.group uu____5391
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5395 =
              let uu____5396 = str "`@"  in
              let uu____5397 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5396 uu____5397  in
            FStar_Pprint.group uu____5395
        | uu____5398 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___111_5399  ->
    match uu___111_5399 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5411 =
          let uu____5412 = str "[@"  in
          let uu____5413 =
            let uu____5414 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5415 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5414 uu____5415  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5412 uu____5413  in
        FStar_Pprint.group uu____5411

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
                 let uu____5441 =
                   let uu____5442 =
                     let uu____5443 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5443 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5442 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5441 term_doc
             | pats ->
                 let uu____5449 =
                   let uu____5450 =
                     let uu____5451 =
                       let uu____5452 =
                         let uu____5453 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5453
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5452 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5454 = p_trigger trigger  in
                     prefix2 uu____5451 uu____5454  in
                   FStar_Pprint.group uu____5450  in
                 prefix2 uu____5449 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5474 =
                   let uu____5475 =
                     let uu____5476 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5476 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5475 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5474 term_doc
             | pats ->
                 let uu____5482 =
                   let uu____5483 =
                     let uu____5484 =
                       let uu____5485 =
                         let uu____5486 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5486
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5485 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5487 = p_trigger trigger  in
                     prefix2 uu____5484 uu____5487  in
                   FStar_Pprint.group uu____5483  in
                 prefix2 uu____5482 term_doc)
        | uu____5488 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5490 -> str "forall"
    | FStar_Parser_AST.QExists uu____5503 -> str "exists"
    | uu____5516 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___112_5517  ->
    match uu___112_5517 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5529 =
          let uu____5530 =
            let uu____5531 =
              let uu____5532 = str "pattern"  in
              let uu____5533 =
                let uu____5534 =
                  let uu____5535 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5535
                   in
                FStar_Pprint.op_Hat_Hat uu____5534 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5532 uu____5533  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5531  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5530  in
        FStar_Pprint.group uu____5529

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5541 = str "\\/"  in
    FStar_Pprint.separate_map uu____5541 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5547 =
      let uu____5548 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5548 p_appTerm pats  in
    FStar_Pprint.group uu____5547

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5558 =
              let uu____5559 =
                let uu____5560 = str "fun"  in
                let uu____5561 =
                  let uu____5562 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5562
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5560 uu____5561  in
              let uu____5563 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5559 uu____5563  in
            let uu____5564 = paren_if ps  in uu____5564 uu____5558
        | uu____5569 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5573  ->
      match uu____5573 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5596 =
                    let uu____5597 =
                      let uu____5598 =
                        let uu____5599 = p_tuplePattern p  in
                        let uu____5600 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5599 uu____5600  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5598
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5597  in
                  FStar_Pprint.group uu____5596
              | FStar_Pervasives_Native.Some f ->
                  let uu____5602 =
                    let uu____5603 =
                      let uu____5604 =
                        let uu____5605 =
                          let uu____5606 =
                            let uu____5607 = p_tuplePattern p  in
                            let uu____5608 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5607
                              uu____5608
                             in
                          FStar_Pprint.group uu____5606  in
                        let uu____5609 =
                          let uu____5610 =
                            let uu____5613 = p_tmFormula f  in
                            [uu____5613; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5610  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5605 uu____5609
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5604
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5603  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5602
               in
            let uu____5614 =
              let uu____5615 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5615  in
            FStar_Pprint.group uu____5614  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5624 =
                      let uu____5625 =
                        let uu____5626 =
                          let uu____5627 =
                            let uu____5628 =
                              let uu____5629 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5629  in
                            FStar_Pprint.separate_map uu____5628
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5627
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5626
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5625  in
                    FStar_Pprint.group uu____5624
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5630 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5632;_},e1::e2::[])
        ->
        let uu____5637 = str "<==>"  in
        let uu____5638 = p_tmImplies e1  in
        let uu____5639 = p_tmIff e2  in
        infix0 uu____5637 uu____5638 uu____5639
    | uu____5640 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5642;_},e1::e2::[])
        ->
        let uu____5647 = str "==>"  in
        let uu____5648 = p_tmArrow p_tmFormula e1  in
        let uu____5649 = p_tmImplies e2  in
        infix0 uu____5647 uu____5648 uu____5649
    | uu____5650 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5658 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5658 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_8 when _0_8 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5679 ->
               let uu____5680 =
                 let uu____5681 =
                   let uu____5682 =
                     let uu____5683 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5683
                      in
                   FStar_Pprint.separate uu____5682 terms  in
                 let uu____5684 =
                   let uu____5685 =
                     let uu____5686 =
                       let uu____5687 =
                         let uu____5688 =
                           let uu____5689 =
                             let uu____5690 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5690
                              in
                           FStar_Pprint.separate uu____5689 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5688 last_op  in
                       let uu____5691 =
                         let uu____5692 =
                           let uu____5693 =
                             let uu____5694 =
                               let uu____5695 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5695
                                in
                             FStar_Pprint.separate uu____5694 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5693 last_op  in
                         jump2 uu____5692  in
                       FStar_Pprint.ifflat uu____5687 uu____5691  in
                     FStar_Pprint.group uu____5686  in
                   let uu____5696 = FStar_List.hd last1  in
                   prefix2 uu____5685 uu____5696  in
                 FStar_Pprint.ifflat uu____5681 uu____5684  in
               FStar_Pprint.group uu____5680)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5709 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5714 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5709 uu____5714
      | uu____5717 -> let uu____5718 = p_Tm e  in [uu____5718]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5721 =
        let uu____5722 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5722 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5721  in
    let disj =
      let uu____5724 =
        let uu____5725 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5725 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5724  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5744;_},e1::e2::[])
        ->
        let uu____5749 = p_tmDisjunction e1  in
        let uu____5754 = let uu____5759 = p_tmConjunction e2  in [uu____5759]
           in
        FStar_List.append uu____5749 uu____5754
    | uu____5768 -> let uu____5769 = p_tmConjunction e  in [uu____5769]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5779;_},e1::e2::[])
        ->
        let uu____5784 = p_tmConjunction e1  in
        let uu____5787 = let uu____5790 = p_tmTuple e2  in [uu____5790]  in
        FStar_List.append uu____5784 uu____5787
    | uu____5791 -> let uu____5792 = p_tmTuple e  in [uu____5792]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5809 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5809
          (fun uu____5817  ->
             match uu____5817 with | (e1,uu____5823) -> p_tmEq e1) args
    | uu____5824 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5829 =
             let uu____5830 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5830  in
           FStar_Pprint.group uu____5829)

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
               (let uu____5847 = FStar_Ident.text_of_id op  in
                uu____5847 = "="))
              ||
              (let uu____5849 = FStar_Ident.text_of_id op  in
               uu____5849 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5851 = levels op1  in
            (match uu____5851 with
             | (left1,mine,right1) ->
                 let uu____5861 =
                   let uu____5862 = FStar_All.pipe_left str op1  in
                   let uu____5863 = p_tmEqWith' p_X left1 e1  in
                   let uu____5864 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5862 uu____5863 uu____5864  in
                 paren_if_gt curr mine uu____5861)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5865;_},e1::e2::[])
            ->
            let uu____5870 =
              let uu____5871 = p_tmEqWith p_X e1  in
              let uu____5872 =
                let uu____5873 =
                  let uu____5874 =
                    let uu____5875 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5875  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5874  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5873  in
              FStar_Pprint.op_Hat_Hat uu____5871 uu____5872  in
            FStar_Pprint.group uu____5870
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5876;_},e1::[])
            ->
            let uu____5880 = levels "-"  in
            (match uu____5880 with
             | (left1,mine,right1) ->
                 let uu____5890 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5890)
        | uu____5891 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5935)::(e2,uu____5937)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5957 = is_list e  in Prims.op_Negation uu____5957)
              ->
              let op = "::"  in
              let uu____5959 = levels op  in
              (match uu____5959 with
               | (left1,mine,right1) ->
                   let uu____5969 =
                     let uu____5970 = str op  in
                     let uu____5971 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5972 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5970 uu____5971 uu____5972  in
                   paren_if_gt curr mine uu____5969)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5980 = levels op  in
              (match uu____5980 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____5996 = p_binder false b  in
                     let uu____5997 =
                       let uu____5998 =
                         let uu____5999 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____5999 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5998
                        in
                     FStar_Pprint.op_Hat_Hat uu____5996 uu____5997  in
                   let uu____6000 =
                     let uu____6001 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6002 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6001 uu____6002  in
                   paren_if_gt curr mine uu____6000)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6003;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____6032 = levels op  in
              (match uu____6032 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6042 = str op  in
                     let uu____6043 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6044 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6042 uu____6043 uu____6044
                   else
                     (let uu____6046 =
                        let uu____6047 = str op  in
                        let uu____6048 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6049 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6047 uu____6048 uu____6049  in
                      paren_if_gt curr mine uu____6046))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6056 = levels op1  in
              (match uu____6056 with
               | (left1,mine,right1) ->
                   let uu____6066 =
                     let uu____6067 = str op1  in
                     let uu____6068 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6069 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6067 uu____6068 uu____6069  in
                   paren_if_gt curr mine uu____6066)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6088 =
                let uu____6089 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6090 =
                  let uu____6091 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6091 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6089 uu____6090  in
              braces_with_nesting uu____6088
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6096;_},e1::[])
              ->
              let uu____6100 =
                let uu____6101 = str "~"  in
                let uu____6102 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6101 uu____6102  in
              FStar_Pprint.group uu____6100
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6104;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6110 = levels op  in
                   (match uu____6110 with
                    | (left1,mine,right1) ->
                        let uu____6120 =
                          let uu____6121 = str op  in
                          let uu____6122 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6123 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6121 uu____6122 uu____6123  in
                        paren_if_gt curr mine uu____6120)
               | uu____6124 -> p_X e)
          | uu____6125 -> p_X e

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
        let uu____6132 =
          let uu____6133 = p_lident lid  in
          let uu____6134 =
            let uu____6135 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6135  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6133 uu____6134  in
        FStar_Pprint.group uu____6132
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6138 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6140 = p_appTerm e  in
    let uu____6141 =
      let uu____6142 =
        let uu____6143 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6143 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6142  in
    FStar_Pprint.op_Hat_Hat uu____6140 uu____6141

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6148 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6148 t phi
      | FStar_Parser_AST.TAnnotated uu____6149 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6154 ->
          let uu____6155 =
            let uu____6156 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6156
             in
          failwith uu____6155
      | FStar_Parser_AST.TVariable uu____6157 ->
          let uu____6158 =
            let uu____6159 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6159
             in
          failwith uu____6158
      | FStar_Parser_AST.NoName uu____6160 ->
          let uu____6161 =
            let uu____6162 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6162
             in
          failwith uu____6161

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6164  ->
      match uu____6164 with
      | (lid,e) ->
          let uu____6171 =
            let uu____6172 = p_qlident lid  in
            let uu____6173 =
              let uu____6174 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6174
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6172 uu____6173  in
          FStar_Pprint.group uu____6171

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6176 when is_general_application e ->
        let uu____6183 = head_and_args e  in
        (match uu____6183 with
         | (head1,args) ->
             let uu____6208 =
               let uu____6219 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6219
               then
                 let uu____6253 =
                   FStar_Util.take
                     (fun uu____6277  ->
                        match uu____6277 with
                        | (uu____6282,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6253 with
                 | (fs_typ_args,args1) ->
                     let uu____6320 =
                       let uu____6321 = p_indexingTerm head1  in
                       let uu____6322 =
                         let uu____6323 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6323 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6321 uu____6322  in
                     (uu____6320, args1)
               else
                 (let uu____6335 = p_indexingTerm head1  in
                  (uu____6335, args))
                in
             (match uu____6208 with
              | (head_doc,args1) ->
                  let uu____6356 =
                    let uu____6357 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6357 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6356))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6377 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6377)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6395 =
               let uu____6396 = p_quident lid  in
               let uu____6397 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6396 uu____6397  in
             FStar_Pprint.group uu____6395
         | hd1::tl1 ->
             let uu____6414 =
               let uu____6415 =
                 let uu____6416 =
                   let uu____6417 = p_quident lid  in
                   let uu____6418 = p_argTerm hd1  in
                   prefix2 uu____6417 uu____6418  in
                 FStar_Pprint.group uu____6416  in
               let uu____6419 =
                 let uu____6420 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6420  in
               FStar_Pprint.op_Hat_Hat uu____6415 uu____6419  in
             FStar_Pprint.group uu____6414)
    | uu____6425 -> p_indexingTerm e

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
         (let uu____6434 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6434 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6436 = str "#"  in
        let uu____6437 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6436 uu____6437
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6439  ->
    match uu____6439 with | (e,uu____6445) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6450;_},e1::e2::[])
          ->
          let uu____6455 =
            let uu____6456 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6457 =
              let uu____6458 =
                let uu____6459 = p_term false false e2  in
                soft_parens_with_nesting uu____6459  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6458  in
            FStar_Pprint.op_Hat_Hat uu____6456 uu____6457  in
          FStar_Pprint.group uu____6455
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6460;_},e1::e2::[])
          ->
          let uu____6465 =
            let uu____6466 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6467 =
              let uu____6468 =
                let uu____6469 = p_term false false e2  in
                soft_brackets_with_nesting uu____6469  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6468  in
            FStar_Pprint.op_Hat_Hat uu____6466 uu____6467  in
          FStar_Pprint.group uu____6465
      | uu____6470 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6475 = p_quident lid  in
        let uu____6476 =
          let uu____6477 =
            let uu____6478 = p_term false false e1  in
            soft_parens_with_nesting uu____6478  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6477  in
        FStar_Pprint.op_Hat_Hat uu____6475 uu____6476
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6484 =
          let uu____6485 = FStar_Ident.text_of_id op  in str uu____6485  in
        let uu____6486 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6484 uu____6486
    | uu____6487 -> p_atomicTermNotQUident e

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
         | uu____6496 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6503 =
          let uu____6504 = FStar_Ident.text_of_id op  in str uu____6504  in
        let uu____6505 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6503 uu____6505
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6509 =
          let uu____6510 =
            let uu____6511 =
              let uu____6512 = FStar_Ident.text_of_id op  in str uu____6512
               in
            let uu____6513 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6511 uu____6513  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6510  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6509
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6528 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6529 =
          let uu____6530 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6531 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6530 p_tmEq uu____6531  in
        let uu____6538 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6528 uu____6529 uu____6538
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6541 =
          let uu____6542 = p_atomicTermNotQUident e1  in
          let uu____6543 =
            let uu____6544 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6544  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6542 uu____6543
           in
        FStar_Pprint.group uu____6541
    | uu____6545 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6550 = p_quident constr_lid  in
        let uu____6551 =
          let uu____6552 =
            let uu____6553 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6553  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6552  in
        FStar_Pprint.op_Hat_Hat uu____6550 uu____6551
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6555 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6555 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6557 = p_term false false e1  in
        soft_parens_with_nesting uu____6557
    | uu____6558 when is_array e ->
        let es = extract_from_list e  in
        let uu____6562 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6563 =
          let uu____6564 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6564
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6567 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6562 uu____6563 uu____6567
    | uu____6568 when is_list e ->
        let uu____6569 =
          let uu____6570 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6571 = extract_from_list e  in
          separate_map_or_flow_last uu____6570
            (fun ps  -> p_noSeqTerm ps false) uu____6571
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6569 FStar_Pprint.rbracket
    | uu____6576 when is_lex_list e ->
        let uu____6577 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6578 =
          let uu____6579 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6580 = extract_from_list e  in
          separate_map_or_flow_last uu____6579
            (fun ps  -> p_noSeqTerm ps false) uu____6580
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6577 uu____6578 FStar_Pprint.rbracket
    | uu____6585 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6589 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6590 =
          let uu____6591 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6591 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6589 uu____6590 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6595 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6596 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6595 uu____6596
    | FStar_Parser_AST.Op (op,args) when
        let uu____6603 = handleable_op op args  in
        Prims.op_Negation uu____6603 ->
        let uu____6604 =
          let uu____6605 =
            let uu____6606 = FStar_Ident.text_of_id op  in
            let uu____6607 =
              let uu____6608 =
                let uu____6609 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6609
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6608  in
            Prims.strcat uu____6606 uu____6607  in
          Prims.strcat "Operation " uu____6605  in
        failwith uu____6604
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6611 = str "u#"  in
        let uu____6612 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6611 uu____6612
    | FStar_Parser_AST.Wild  ->
        let uu____6613 = p_term false false e  in
        soft_parens_with_nesting uu____6613
    | FStar_Parser_AST.Const uu____6614 ->
        let uu____6615 = p_term false false e  in
        soft_parens_with_nesting uu____6615
    | FStar_Parser_AST.Op uu____6616 ->
        let uu____6623 = p_term false false e  in
        soft_parens_with_nesting uu____6623
    | FStar_Parser_AST.Tvar uu____6624 ->
        let uu____6625 = p_term false false e  in
        soft_parens_with_nesting uu____6625
    | FStar_Parser_AST.Var uu____6626 ->
        let uu____6627 = p_term false false e  in
        soft_parens_with_nesting uu____6627
    | FStar_Parser_AST.Name uu____6628 ->
        let uu____6629 = p_term false false e  in
        soft_parens_with_nesting uu____6629
    | FStar_Parser_AST.Construct uu____6630 ->
        let uu____6641 = p_term false false e  in
        soft_parens_with_nesting uu____6641
    | FStar_Parser_AST.Abs uu____6642 ->
        let uu____6649 = p_term false false e  in
        soft_parens_with_nesting uu____6649
    | FStar_Parser_AST.App uu____6650 ->
        let uu____6657 = p_term false false e  in
        soft_parens_with_nesting uu____6657
    | FStar_Parser_AST.Let uu____6658 ->
        let uu____6679 = p_term false false e  in
        soft_parens_with_nesting uu____6679
    | FStar_Parser_AST.LetOpen uu____6680 ->
        let uu____6685 = p_term false false e  in
        soft_parens_with_nesting uu____6685
    | FStar_Parser_AST.Seq uu____6686 ->
        let uu____6691 = p_term false false e  in
        soft_parens_with_nesting uu____6691
    | FStar_Parser_AST.Bind uu____6692 ->
        let uu____6699 = p_term false false e  in
        soft_parens_with_nesting uu____6699
    | FStar_Parser_AST.If uu____6700 ->
        let uu____6707 = p_term false false e  in
        soft_parens_with_nesting uu____6707
    | FStar_Parser_AST.Match uu____6708 ->
        let uu____6723 = p_term false false e  in
        soft_parens_with_nesting uu____6723
    | FStar_Parser_AST.TryWith uu____6724 ->
        let uu____6739 = p_term false false e  in
        soft_parens_with_nesting uu____6739
    | FStar_Parser_AST.Ascribed uu____6740 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.Record uu____6750 ->
        let uu____6763 = p_term false false e  in
        soft_parens_with_nesting uu____6763
    | FStar_Parser_AST.Project uu____6764 ->
        let uu____6769 = p_term false false e  in
        soft_parens_with_nesting uu____6769
    | FStar_Parser_AST.Product uu____6770 ->
        let uu____6777 = p_term false false e  in
        soft_parens_with_nesting uu____6777
    | FStar_Parser_AST.Sum uu____6778 ->
        let uu____6785 = p_term false false e  in
        soft_parens_with_nesting uu____6785
    | FStar_Parser_AST.QForall uu____6786 ->
        let uu____6799 = p_term false false e  in
        soft_parens_with_nesting uu____6799
    | FStar_Parser_AST.QExists uu____6800 ->
        let uu____6813 = p_term false false e  in
        soft_parens_with_nesting uu____6813
    | FStar_Parser_AST.Refine uu____6814 ->
        let uu____6819 = p_term false false e  in
        soft_parens_with_nesting uu____6819
    | FStar_Parser_AST.NamedTyp uu____6820 ->
        let uu____6825 = p_term false false e  in
        soft_parens_with_nesting uu____6825
    | FStar_Parser_AST.Requires uu____6826 ->
        let uu____6833 = p_term false false e  in
        soft_parens_with_nesting uu____6833
    | FStar_Parser_AST.Ensures uu____6834 ->
        let uu____6841 = p_term false false e  in
        soft_parens_with_nesting uu____6841
    | FStar_Parser_AST.Attributes uu____6842 ->
        let uu____6845 = p_term false false e  in
        soft_parens_with_nesting uu____6845
    | FStar_Parser_AST.Quote uu____6846 ->
        let uu____6851 = p_term false false e  in
        soft_parens_with_nesting uu____6851
    | FStar_Parser_AST.VQuote uu____6852 ->
        let uu____6853 = p_term false false e  in
        soft_parens_with_nesting uu____6853
    | FStar_Parser_AST.Antiquote uu____6854 ->
        let uu____6859 = p_term false false e  in
        soft_parens_with_nesting uu____6859

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___115_6860  ->
    match uu___115_6860 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6866) ->
        let uu____6867 = str s  in FStar_Pprint.dquotes uu____6867
    | FStar_Const.Const_bytearray (bytes,uu____6869) ->
        let uu____6874 =
          let uu____6875 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6875  in
        let uu____6876 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6874 uu____6876
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___113_6896 =
          match uu___113_6896 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___114_6902 =
          match uu___114_6902 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6913  ->
               match uu____6913 with
               | (s,w) ->
                   let uu____6920 = signedness s  in
                   let uu____6921 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6920 uu____6921)
            sign_width_opt
           in
        let uu____6922 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6922 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6924 = FStar_Range.string_of_range r  in str uu____6924
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6926 = p_quident lid  in
        let uu____6927 =
          let uu____6928 =
            let uu____6929 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6929  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6928  in
        FStar_Pprint.op_Hat_Hat uu____6926 uu____6927

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6931 = str "u#"  in
    let uu____6932 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6931 uu____6932

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6934;_},u1::u2::[])
        ->
        let uu____6939 =
          let uu____6940 = p_universeFrom u1  in
          let uu____6941 =
            let uu____6942 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6942  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6940 uu____6941  in
        FStar_Pprint.group uu____6939
    | FStar_Parser_AST.App uu____6943 ->
        let uu____6950 = head_and_args u  in
        (match uu____6950 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6976 =
                    let uu____6977 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6978 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6986  ->
                           match uu____6986 with
                           | (u1,uu____6992) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6977 uu____6978  in
                  FStar_Pprint.group uu____6976
              | uu____6993 ->
                  let uu____6994 =
                    let uu____6995 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6995
                     in
                  failwith uu____6994))
    | uu____6996 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7019 = FStar_Ident.text_of_id id1  in str uu____7019
    | FStar_Parser_AST.Paren u1 ->
        let uu____7021 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7021
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7022;_},uu____7023::uu____7024::[])
        ->
        let uu____7027 = p_universeFrom u  in
        soft_parens_with_nesting uu____7027
    | FStar_Parser_AST.App uu____7028 ->
        let uu____7035 = p_universeFrom u  in
        soft_parens_with_nesting uu____7035
    | uu____7036 ->
        let uu____7037 =
          let uu____7038 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7038
           in
        failwith uu____7037

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
      (fun uu____7197  ->
         match uu____7197 with | (comment,range) -> str comment) comments
  
let (extract_decl_range :
  FStar_Parser_AST.decl ->
    (FStar_Range.range,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun d  ->
    let qual_lines =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____7217)) -> (Prims.parse_int "0")
      | ([],uu____7220) -> (Prims.parse_int "0")
      | uu____7223 -> (Prims.parse_int "1")  in
    ((d.FStar_Parser_AST.drange), qual_lines)
  
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
        | FStar_Parser_AST.Module (uu____7267,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7273,decls,uu____7275) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7324 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7337;
                 FStar_Parser_AST.doc = uu____7338;
                 FStar_Parser_AST.quals = uu____7339;
                 FStar_Parser_AST.attrs = uu____7340;_}::uu____7341 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7347 =
                   let uu____7350 =
                     let uu____7353 = FStar_List.tl ds  in d :: uu____7353
                      in
                   d0 :: uu____7350  in
                 (uu____7347, (d0.FStar_Parser_AST.drange))
             | uu____7358 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7324 with
            | (decls1,first_range) ->
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7416 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7416 (Prims.parse_int "0")
                      FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7524 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7524, comments1))))))
  