open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let (all_explicit :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    Prims.list -> Prims.bool)
  =
  fun args  ->
    FStar_Util.for_all
      (fun uu___107_37  ->
         match uu___107_37 with
         | (uu____42,FStar_Parser_AST.Nothing ) -> true
         | uu____43 -> false) args
  
let (unfold_tuples : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let with_fs_typ_app :
  'Auu____71 'Auu____72 .
    Prims.bool -> ('Auu____71 -> 'Auu____72) -> 'Auu____71 -> 'Auu____72
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
  fun uu___108_1254  ->
    match uu___108_1254 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___109_1279  ->
      match uu___109_1279 with
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
  let levels_from_associativity l uu___110_1466 =
    match uu___110_1466 with
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
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1660 .
    ('Auu____1660,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1705 =
        FStar_List.tryFind
          (fun uu____1735  ->
             match uu____1735 with
             | (uu____1748,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1705 with
      | FStar_Pervasives_Native.Some ((uu____1770,l1,uu____1772),uu____1773)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1808 =
            let uu____1809 =
              let uu____1810 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1810  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1809
             in
          failwith uu____1808
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1832 = assign_levels level_associativity_spec op  in
    match uu____1832 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 : associativity_level Prims.list) =
  [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1862 =
      let uu____1865 =
        let uu____1870 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1870  in
      FStar_List.tryFind uu____1865 operatorInfix0ad12  in
    uu____1862 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____1928 =
      let uu____1942 =
        let uu____1958 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1958  in
      FStar_List.tryFind uu____1942 opinfix34  in
    uu____1928 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2014 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2014
    then (Prims.parse_int "1")
    else
      (let uu____2016 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2016
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2025 . FStar_Ident.ident -> 'Auu____2025 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_1 when _0_1 = (Prims.parse_int "0") -> true
      | _0_2 when _0_2 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2041 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2041 ["-"; "~"])
      | _0_3 when _0_3 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2043 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2043
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_4 when _0_4 = (Prims.parse_int "3") ->
          let uu____2044 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2044 [".()<-"; ".[]<-"]
      | uu____2045 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2083 .
    ('Auu____2083 -> FStar_Pprint.document) ->
      'Auu____2083 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2124 = FStar_ST.op_Bang comment_stack  in
          match uu____2124 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2183 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2183
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2220 =
                    let uu____2221 =
                      let uu____2222 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2222
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2221  in
                  comments_before_pos uu____2220 print_pos lookahead_pos))
              else
                (let uu____2224 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2224))
           in
        let uu____2225 =
          let uu____2230 =
            let uu____2231 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2231  in
          let uu____2232 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2230 uu____2232  in
        match uu____2225 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2238 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2238
              else comments  in
            let uu____2244 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2244
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2265 = FStar_ST.op_Bang comment_stack  in
          match uu____2265 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2349 =
                    let uu____2350 =
                      let uu____2351 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2351  in
                    uu____2350 - lbegin  in
                  max k uu____2349  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2354 =
                    let uu____2355 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2356 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2355 uu____2356  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2354  in
                let uu____2357 =
                  let uu____2358 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2358  in
                place_comments_until_pos (Prims.parse_int "1") uu____2357
                  pos_end doc2))
          | uu____2359 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2368 =
                     let uu____2369 = FStar_Range.line_of_pos pos_end  in
                     uu____2369 - lbegin  in
                   max (Prims.parse_int "1") uu____2368  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2371 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2371)
  
let separate_map_with_comments :
  'Auu____2384 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2384 -> FStar_Pprint.document) ->
          'Auu____2384 Prims.list ->
            ('Auu____2384 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2441 x =
              match uu____2441 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2455 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2455 doc1
                     in
                  let uu____2456 =
                    let uu____2457 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2457  in
                  let uu____2458 =
                    let uu____2459 =
                      let uu____2460 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2460  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2459  in
                  (uu____2456, uu____2458)
               in
            let uu____2461 =
              let uu____2468 = FStar_List.hd xs  in
              let uu____2469 = FStar_List.tl xs  in (uu____2468, uu____2469)
               in
            match uu____2461 with
            | (x,xs1) ->
                let init1 =
                  let uu____2485 =
                    let uu____2486 =
                      let uu____2487 = extract_range x  in
                      FStar_Range.end_of_range uu____2487  in
                    FStar_Range.line_of_pos uu____2486  in
                  let uu____2488 =
                    let uu____2489 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2489  in
                  (uu____2485, uu____2488)  in
                let uu____2490 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2490
  
let separate_map_with_comments_kw :
  'Auu____2513 'Auu____2514 .
    'Auu____2513 ->
      'Auu____2513 ->
        ('Auu____2513 -> 'Auu____2514 -> FStar_Pprint.document) ->
          'Auu____2514 Prims.list ->
            ('Auu____2514 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2576 x =
              match uu____2576 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2590 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2590 doc1
                     in
                  let uu____2591 =
                    let uu____2592 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2592  in
                  let uu____2593 =
                    let uu____2594 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2594  in
                  (uu____2591, uu____2593)
               in
            let uu____2595 =
              let uu____2602 = FStar_List.hd xs  in
              let uu____2603 = FStar_List.tl xs  in (uu____2602, uu____2603)
               in
            match uu____2595 with
            | (x,xs1) ->
                let init1 =
                  let uu____2619 =
                    let uu____2620 =
                      let uu____2621 = extract_range x  in
                      FStar_Range.end_of_range uu____2621  in
                    FStar_Range.line_of_pos uu____2620  in
                  let uu____2622 = f prefix1 x  in (uu____2619, uu____2622)
                   in
                let uu____2623 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2623
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3333)) ->
          let uu____3336 =
            let uu____3337 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3337 FStar_Util.is_upper  in
          if uu____3336
          then
            let uu____3340 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3340 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3342 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3349 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3350 =
      let uu____3351 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3352 =
        let uu____3353 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3353  in
      FStar_Pprint.op_Hat_Hat uu____3351 uu____3352  in
    FStar_Pprint.op_Hat_Hat uu____3349 uu____3350

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3355 ->
        let uu____3356 =
          let uu____3357 = str "@ "  in
          let uu____3358 =
            let uu____3359 =
              let uu____3360 =
                let uu____3361 =
                  let uu____3362 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3362  in
                FStar_Pprint.op_Hat_Hat uu____3361 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3360  in
            FStar_Pprint.op_Hat_Hat uu____3359 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3357 uu____3358  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3356

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3365  ->
    match uu____3365 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3401 =
                match uu____3401 with
                | (kwd,arg) ->
                    let uu____3408 = str "@"  in
                    let uu____3409 =
                      let uu____3410 = str kwd  in
                      let uu____3411 =
                        let uu____3412 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3412
                         in
                      FStar_Pprint.op_Hat_Hat uu____3410 uu____3411  in
                    FStar_Pprint.op_Hat_Hat uu____3408 uu____3409
                 in
              let uu____3413 =
                let uu____3414 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3414 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3413
           in
        let uu____3419 =
          let uu____3420 =
            let uu____3421 =
              let uu____3422 =
                let uu____3423 = str doc1  in
                let uu____3424 =
                  let uu____3425 =
                    let uu____3426 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3426  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3425  in
                FStar_Pprint.op_Hat_Hat uu____3423 uu____3424  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3422  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3421  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3420  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3419

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3430 =
          let uu____3431 = str "val"  in
          let uu____3432 =
            let uu____3433 =
              let uu____3434 = p_lident lid  in
              let uu____3435 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3434 uu____3435  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3433  in
          FStar_Pprint.op_Hat_Hat uu____3431 uu____3432  in
        let uu____3436 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3430 uu____3436
    | FStar_Parser_AST.TopLevelLet (uu____3437,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3462 =
               let uu____3463 = str "let"  in p_letlhs uu____3463 lb  in
             FStar_Pprint.group uu____3462) lbs
    | uu____3464 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___111_3479 =
          match uu___111_3479 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3487 = f x  in
              let uu____3488 =
                let uu____3489 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3489  in
              FStar_Pprint.op_Hat_Hat uu____3487 uu____3488
           in
        let uu____3490 = str "["  in
        let uu____3491 =
          let uu____3492 = p_list' l  in
          let uu____3493 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3492 uu____3493  in
        FStar_Pprint.op_Hat_Hat uu____3490 uu____3491

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3496 =
          let uu____3497 = str "open"  in
          let uu____3498 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3497 uu____3498  in
        FStar_Pprint.group uu____3496
    | FStar_Parser_AST.Include uid ->
        let uu____3500 =
          let uu____3501 = str "include"  in
          let uu____3502 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3501 uu____3502  in
        FStar_Pprint.group uu____3500
    | FStar_Parser_AST.Friend uid ->
        let uu____3504 =
          let uu____3505 = str "friend"  in
          let uu____3506 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3505 uu____3506  in
        FStar_Pprint.group uu____3504
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3509 =
          let uu____3510 = str "module"  in
          let uu____3511 =
            let uu____3512 =
              let uu____3513 = p_uident uid1  in
              let uu____3514 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3513 uu____3514  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3512  in
          FStar_Pprint.op_Hat_Hat uu____3510 uu____3511  in
        let uu____3515 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3509 uu____3515
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3517 =
          let uu____3518 = str "module"  in
          let uu____3519 =
            let uu____3520 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3520  in
          FStar_Pprint.op_Hat_Hat uu____3518 uu____3519  in
        FStar_Pprint.group uu____3517
    | FStar_Parser_AST.Tycon
        (true
         ,uu____3521,(FStar_Parser_AST.TyconAbbrev
                      (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
                      )::[])
        ->
        let effect_prefix_doc =
          let uu____3554 = str "effect"  in
          let uu____3555 =
            let uu____3556 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3556  in
          FStar_Pprint.op_Hat_Hat uu____3554 uu____3555  in
        let uu____3557 =
          let uu____3558 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3558 FStar_Pprint.equals
           in
        let uu____3559 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3557 uu____3559
    | FStar_Parser_AST.Tycon (false ,tc,tcdefs) ->
        let s = if tc then str "class" else str "type"  in
        let uu____3580 =
          let uu____3581 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs s uu____3581  in
        let uu____3594 =
          let uu____3595 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3633 =
                    let uu____3634 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3634 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3633)) uu____3595
           in
        FStar_Pprint.op_Hat_Hat uu____3580 uu____3594
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3650 = str "let"  in
          let uu____3651 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3650 uu____3651  in
        let uu____3652 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3652 p_letbinding lbs
          (fun uu____3660  ->
             match uu____3660 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3669 = str "val"  in
        let uu____3670 =
          let uu____3671 =
            let uu____3672 = p_lident lid  in
            let uu____3673 =
              let uu____3674 =
                let uu____3675 =
                  let uu____3676 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3676  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3675  in
              FStar_Pprint.group uu____3674  in
            FStar_Pprint.op_Hat_Hat uu____3672 uu____3673  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3671  in
        FStar_Pprint.op_Hat_Hat uu____3669 uu____3670
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3680 =
            let uu____3681 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3681 FStar_Util.is_upper  in
          if uu____3680
          then FStar_Pprint.empty
          else
            (let uu____3685 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3685 FStar_Pprint.space)
           in
        let uu____3686 =
          let uu____3687 = p_ident id1  in
          let uu____3688 =
            let uu____3689 =
              let uu____3690 =
                let uu____3691 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3691  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3690  in
            FStar_Pprint.group uu____3689  in
          FStar_Pprint.op_Hat_Hat uu____3687 uu____3688  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3686
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3698 = str "exception"  in
        let uu____3699 =
          let uu____3700 =
            let uu____3701 = p_uident uid  in
            let uu____3702 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3706 =
                     let uu____3707 = str "of"  in
                     let uu____3708 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3707 uu____3708  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3706) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3701 uu____3702  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3700  in
        FStar_Pprint.op_Hat_Hat uu____3698 uu____3699
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3710 = str "new_effect"  in
        let uu____3711 =
          let uu____3712 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3712  in
        FStar_Pprint.op_Hat_Hat uu____3710 uu____3711
    | FStar_Parser_AST.SubEffect se ->
        let uu____3714 = str "sub_effect"  in
        let uu____3715 =
          let uu____3716 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3716  in
        FStar_Pprint.op_Hat_Hat uu____3714 uu____3715
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3719 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3719 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3720 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3721,uu____3722) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3745 = str "%splice"  in
        let uu____3746 =
          let uu____3747 =
            let uu____3748 = str ";"  in p_list p_uident uu____3748 ids  in
          let uu____3749 =
            let uu____3750 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3750  in
          FStar_Pprint.op_Hat_Hat uu____3747 uu____3749  in
        FStar_Pprint.op_Hat_Hat uu____3745 uu____3746

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___112_3751  ->
    match uu___112_3751 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3753 = str "#set-options"  in
        let uu____3754 =
          let uu____3755 =
            let uu____3756 = str s  in FStar_Pprint.dquotes uu____3756  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3755  in
        FStar_Pprint.op_Hat_Hat uu____3753 uu____3754
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3760 = str "#reset-options"  in
        let uu____3761 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3765 =
                 let uu____3766 = str s  in FStar_Pprint.dquotes uu____3766
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3765) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3760 uu____3761
    | FStar_Parser_AST.PushOptions s_opt ->
        let uu____3770 = str "#push-options"  in
        let uu____3771 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3775 =
                 let uu____3776 = str s  in FStar_Pprint.dquotes uu____3776
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3775) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3770 uu____3771
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
    fun uu____3801  ->
      match uu____3801 with
      | (typedecl,fsdoc_opt) ->
          let uu____3814 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3814 with
           | (decl,body) ->
               let uu____3832 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3832)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___113_3834  ->
      match uu___113_3834 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3864 = FStar_Pprint.empty  in
          let uu____3865 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3865, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3886 =
            let uu____3887 = p_typ false false t  in jump2 uu____3887  in
          let uu____3888 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3888, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3942 =
            match uu____3942 with
            | (lid1,t,doc_opt) ->
                let uu____3958 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3958
             in
          let p_fields uu____3974 =
            let uu____3975 =
              let uu____3976 =
                let uu____3977 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3977 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3976  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3975  in
          let uu____3986 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3986, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4047 =
            match uu____4047 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4073 =
                    let uu____4074 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4074  in
                  FStar_Range.extend_to_end_of_line uu____4073  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4100 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4113 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4113,
            ((fun uu____4119  ->
                let uu____4120 = datacon_doc ()  in jump2 uu____4120)))

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
  fun uu____4121  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4121 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4155 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4155  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4157 =
                        let uu____4160 =
                          let uu____4163 = p_fsdoc fsdoc  in
                          let uu____4164 =
                            let uu____4167 = cont lid_doc  in [uu____4167]
                             in
                          uu____4163 :: uu____4164  in
                        kw :: uu____4160  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4157
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4172 =
                        let uu____4173 =
                          let uu____4174 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4174 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4173
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4172
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4189 =
                          let uu____4190 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4190  in
                        prefix2 uu____4189 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4192  ->
      match uu____4192 with
      | (lid,t,doc_opt) ->
          let uu____4208 =
            let uu____4209 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4210 =
              let uu____4211 = p_lident lid  in
              let uu____4212 =
                let uu____4213 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4213  in
              FStar_Pprint.op_Hat_Hat uu____4211 uu____4212  in
            FStar_Pprint.op_Hat_Hat uu____4209 uu____4210  in
          FStar_Pprint.group uu____4208

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4214  ->
    match uu____4214 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4242 =
            let uu____4243 =
              let uu____4244 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4244  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4243  in
          FStar_Pprint.group uu____4242  in
        let uu____4245 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4246 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4250 =
                 let uu____4251 =
                   let uu____4252 =
                     let uu____4253 =
                       let uu____4254 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4254
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4253  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4252  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4251  in
               FStar_Pprint.group uu____4250) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4245 uu____4246

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4256  ->
      match uu____4256 with
      | (pat,uu____4262) ->
          let uu____4263 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4282 =
                  let uu____4283 =
                    let uu____4284 =
                      let uu____4285 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4285
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4284  in
                  FStar_Pprint.group uu____4283  in
                (pat1, uu____4282)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4297 =
                  let uu____4298 =
                    let uu____4299 =
                      let uu____4300 =
                        let uu____4301 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4301
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4300
                       in
                    FStar_Pprint.group uu____4299  in
                  let uu____4302 =
                    let uu____4303 =
                      let uu____4304 = str "by"  in
                      let uu____4305 =
                        let uu____4306 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4306
                         in
                      FStar_Pprint.op_Hat_Hat uu____4304 uu____4305  in
                    FStar_Pprint.group uu____4303  in
                  FStar_Pprint.op_Hat_Hat uu____4298 uu____4302  in
                (pat1, uu____4297)
            | uu____4307 -> (pat, FStar_Pprint.empty)  in
          (match uu____4263 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4311);
                       FStar_Parser_AST.prange = uu____4312;_},pats)
                    ->
                    let uu____4322 =
                      let uu____4323 =
                        let uu____4324 =
                          let uu____4325 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4325  in
                        FStar_Pprint.group uu____4324  in
                      let uu____4326 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4323 uu____4326  in
                    prefix2_nonempty uu____4322 ascr_doc
                | uu____4327 ->
                    let uu____4328 =
                      let uu____4329 =
                        let uu____4330 =
                          let uu____4331 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4331  in
                        FStar_Pprint.group uu____4330  in
                      FStar_Pprint.op_Hat_Hat uu____4329 ascr_doc  in
                    FStar_Pprint.group uu____4328))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4333  ->
      match uu____4333 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4342 =
            let uu____4343 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4343  in
          let uu____4344 =
            let uu____4345 =
              let uu____4346 =
                let uu____4347 =
                  let uu____4348 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4348  in
                FStar_Pprint.group uu____4347  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4346  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4345  in
          FStar_Pprint.ifflat uu____4342 uu____4344

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___114_4349  ->
    match uu___114_4349 with
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
        let uu____4374 = p_uident uid  in
        let uu____4375 = p_binders true bs  in
        let uu____4376 =
          let uu____4377 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4377  in
        surround_maybe_empty (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4374 uu____4375 uu____4376

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
          let uu____4387 =
            let uu____4388 =
              let uu____4389 =
                let uu____4390 = p_uident uid  in
                let uu____4391 = p_binders true bs  in
                let uu____4392 =
                  let uu____4393 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4393  in
                surround_maybe_empty (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4390 uu____4391 uu____4392
                 in
              FStar_Pprint.group uu____4389  in
            let uu____4394 =
              let uu____4395 = str "with"  in
              let uu____4396 =
                let uu____4397 =
                  let uu____4398 =
                    let uu____4399 =
                      let uu____4400 =
                        let uu____4401 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.semi
                            FStar_Pprint.space
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
                          uu____4401
                         in
                      separate_map_last uu____4400 p_effectDecl eff_decls  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4399  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4398  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4397  in
              FStar_Pprint.op_Hat_Hat uu____4395 uu____4396  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4388 uu____4394  in
          braces_with_nesting uu____4387

and (p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,uu____4404,(FStar_Parser_AST.TyconAbbrev
                        (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
                        )::[])
          ->
          let uu____4433 =
            let uu____4434 = p_lident lid  in
            let uu____4435 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4434 uu____4435  in
          let uu____4436 = p_simpleTerm ps false e  in
          prefix2 uu____4433 uu____4436
      | uu____4437 ->
          let uu____4438 =
            let uu____4439 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4439
             in
          failwith uu____4438

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4501 =
        match uu____4501 with
        | (kwd,t) ->
            let uu____4508 =
              let uu____4509 = str kwd  in
              let uu____4510 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4509 uu____4510  in
            let uu____4511 = p_simpleTerm ps false t  in
            prefix2 uu____4508 uu____4511
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4516 =
      let uu____4517 =
        let uu____4518 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4519 =
          let uu____4520 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4520  in
        FStar_Pprint.op_Hat_Hat uu____4518 uu____4519  in
      let uu____4521 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4517 uu____4521  in
    let uu____4522 =
      let uu____4523 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4523  in
    FStar_Pprint.op_Hat_Hat uu____4516 uu____4522

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___115_4524  ->
    match uu___115_4524 with
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
    | uu____4526 ->
        let uu____4527 =
          let uu____4528 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4528  in
        FStar_Pprint.op_Hat_Hat uu____4527 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___116_4531  ->
    match uu___116_4531 with
    | FStar_Parser_AST.Rec  ->
        let uu____4532 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4532
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___117_4533  ->
    match uu___117_4533 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"
    | FStar_Parser_AST.Meta t ->
        let uu____4535 = str "#["  in
        let uu____4536 =
          let uu____4537 = p_term false false t  in
          let uu____4538 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4537 uu____4538  in
        FStar_Pprint.op_Hat_Hat uu____4535 uu____4536

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4543 =
          let uu____4544 =
            let uu____4545 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4545  in
          FStar_Pprint.separate_map uu____4544 p_tuplePattern pats  in
        FStar_Pprint.group uu____4543
    | uu____4546 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4553 =
          let uu____4554 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4554 p_constructorPattern pats  in
        FStar_Pprint.group uu____4553
    | uu____4555 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4558;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4563 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4564 = p_constructorPattern hd1  in
        let uu____4565 = p_constructorPattern tl1  in
        infix0 uu____4563 uu____4564 uu____4565
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4567;_},pats)
        ->
        let uu____4573 = p_quident uid  in
        let uu____4574 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4573 uu____4574
    | uu____4575 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4591;
               FStar_Parser_AST.blevel = uu____4592;
               FStar_Parser_AST.aqual = uu____4593;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4601 =
               let uu____4602 = p_ident lid  in
               p_refinement aqual uu____4602 t1 phi  in
             soft_parens_with_nesting uu____4601
         | (FStar_Parser_AST.PatWild aqual,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4605;
               FStar_Parser_AST.blevel = uu____4606;
               FStar_Parser_AST.aqual = uu____4607;_},phi))
             ->
             let uu____4613 =
               p_refinement aqual FStar_Pprint.underscore t1 phi  in
             soft_parens_with_nesting uu____4613
         | uu____4614 ->
             let uu____4619 =
               let uu____4620 = p_tuplePattern pat  in
               let uu____4621 =
                 let uu____4622 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4622
                  in
               FStar_Pprint.op_Hat_Hat uu____4620 uu____4621  in
             soft_parens_with_nesting uu____4619)
    | FStar_Parser_AST.PatList pats ->
        let uu____4626 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4626 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4643 =
          match uu____4643 with
          | (lid,pat) ->
              let uu____4650 = p_qlident lid  in
              let uu____4651 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4650 uu____4651
           in
        let uu____4652 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4652
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4662 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4663 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4664 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4662 uu____4663 uu____4664
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4673 =
          let uu____4674 =
            let uu____4675 =
              let uu____4676 = FStar_Ident.text_of_id op  in str uu____4676
               in
            let uu____4677 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4675 uu____4677  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4674  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4673
    | FStar_Parser_AST.PatWild aqual ->
        let uu____4681 = FStar_Pprint.optional p_aqual aqual  in
        FStar_Pprint.op_Hat_Hat uu____4681 FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4689 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4690 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4689 uu____4690
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4692 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4695;
           FStar_Parser_AST.prange = uu____4696;_},uu____4697)
        ->
        let uu____4702 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4702
    | FStar_Parser_AST.PatTuple (uu____4703,false ) ->
        let uu____4708 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4708
    | uu____4709 ->
        let uu____4710 =
          let uu____4711 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4711  in
        failwith uu____4710

and (is_typ_tuple : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4713;_},uu____4714)
        -> true
    | uu____4719 -> false

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4723 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4724 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4723 uu____4724
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4731;
                   FStar_Parser_AST.blevel = uu____4732;
                   FStar_Parser_AST.aqual = uu____4733;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4737 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4737 t1 phi
            | uu____4738 ->
                let t' =
                  let uu____4740 = is_typ_tuple t  in
                  if uu____4740
                  then
                    let uu____4741 = p_tmFormula t  in
                    soft_parens_with_nesting uu____4741
                  else p_tmFormula t  in
                let uu____4743 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4744 =
                  let uu____4745 = p_lident lid  in
                  let uu____4746 =
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon t'  in
                  FStar_Pprint.op_Hat_Hat uu____4745 uu____4746  in
                FStar_Pprint.op_Hat_Hat uu____4743 uu____4744
             in
          if is_atomic
          then
            let uu____4747 =
              let uu____4748 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4748  in
            FStar_Pprint.group uu____4747
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4750 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4757;
                  FStar_Parser_AST.blevel = uu____4758;
                  FStar_Parser_AST.aqual = uu____4759;_},phi)
               ->
               if is_atomic
               then
                 let uu____4763 =
                   let uu____4764 =
                     let uu____4765 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4765 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4764  in
                 FStar_Pprint.group uu____4763
               else
                 (let uu____4767 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4767)
           | uu____4768 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4777 -> false
            | FStar_Parser_AST.App uu____4788 -> false
            | FStar_Parser_AST.Op uu____4795 -> false
            | uu____4802 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4806 =
            let uu____4807 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4808 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4807 uu____4808  in
          let uu____4809 =
            let uu____4810 = p_appTerm t  in
            let uu____4811 =
              let uu____4812 =
                let uu____4813 =
                  let uu____4814 = soft_braces_with_nesting_tight phi1  in
                  let uu____4815 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4814 uu____4815  in
                FStar_Pprint.group uu____4813  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4812
               in
            FStar_Pprint.op_Hat_Hat uu____4810 uu____4811  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4806 uu____4809

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4826 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4826

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4831 = FStar_Ident.text_of_id lid  in str uu____4831)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else (let uu____4834 = FStar_Ident.text_of_lid lid  in str uu____4834)

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
            let uu____4852 =
              let uu____4853 =
                let uu____4854 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4854 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4853  in
            let uu____4855 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4852 uu____4855
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4859 =
              let uu____4860 =
                let uu____4861 =
                  let uu____4862 = p_lident x  in
                  let uu____4863 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4862 uu____4863  in
                let uu____4864 =
                  let uu____4865 = p_noSeqTerm true false e1  in
                  let uu____4866 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4865 uu____4866  in
                op_Hat_Slash_Plus_Hat uu____4861 uu____4864  in
              FStar_Pprint.group uu____4860  in
            let uu____4867 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4859 uu____4867
        | uu____4868 ->
            let uu____4869 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4869

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
            let uu____4880 =
              let uu____4881 = p_tmIff e1  in
              let uu____4882 =
                let uu____4883 =
                  let uu____4884 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4884
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4883  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4881 uu____4882  in
            FStar_Pprint.group uu____4880
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4890 =
              let uu____4891 = p_tmIff e1  in
              let uu____4892 =
                let uu____4893 =
                  let uu____4894 =
                    let uu____4895 = p_typ false false t  in
                    let uu____4896 =
                      let uu____4897 = str "by"  in
                      let uu____4898 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4897 uu____4898  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4895 uu____4896  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4894
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4893  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4891 uu____4892  in
            FStar_Pprint.group uu____4890
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4899;_},e1::e2::e3::[])
            ->
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = p_atomicTermNotQUident e1  in
                  let uu____4909 =
                    let uu____4910 =
                      let uu____4911 =
                        let uu____4912 = p_term false false e2  in
                        soft_parens_with_nesting uu____4912  in
                      let uu____4913 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4911 uu____4913  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4910  in
                  FStar_Pprint.op_Hat_Hat uu____4908 uu____4909  in
                FStar_Pprint.group uu____4907  in
              let uu____4914 =
                let uu____4915 = p_noSeqTerm ps pb e3  in jump2 uu____4915
                 in
              FStar_Pprint.op_Hat_Hat uu____4906 uu____4914  in
            FStar_Pprint.group uu____4905
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4916;_},e1::e2::e3::[])
            ->
            let uu____4922 =
              let uu____4923 =
                let uu____4924 =
                  let uu____4925 = p_atomicTermNotQUident e1  in
                  let uu____4926 =
                    let uu____4927 =
                      let uu____4928 =
                        let uu____4929 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4929  in
                      let uu____4930 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4928 uu____4930  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4927  in
                  FStar_Pprint.op_Hat_Hat uu____4925 uu____4926  in
                FStar_Pprint.group uu____4924  in
              let uu____4931 =
                let uu____4932 = p_noSeqTerm ps pb e3  in jump2 uu____4932
                 in
              FStar_Pprint.op_Hat_Hat uu____4923 uu____4931  in
            FStar_Pprint.group uu____4922
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4940 =
              let uu____4941 = str "requires"  in
              let uu____4942 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4941 uu____4942  in
            FStar_Pprint.group uu____4940
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4950 =
              let uu____4951 = str "ensures"  in
              let uu____4952 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4951 uu____4952  in
            FStar_Pprint.group uu____4950
        | FStar_Parser_AST.Attributes es ->
            let uu____4956 =
              let uu____4957 = str "attributes"  in
              let uu____4958 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4957 uu____4958  in
            FStar_Pprint.group uu____4956
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4962 =
                let uu____4963 =
                  let uu____4964 = str "if"  in
                  let uu____4965 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4964 uu____4965  in
                let uu____4966 =
                  let uu____4967 = str "then"  in
                  let uu____4968 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4967 uu____4968  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4963 uu____4966  in
              FStar_Pprint.group uu____4962
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4971,uu____4972,e31) when
                     is_unit e31 ->
                     let uu____4974 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4974
                 | uu____4975 -> p_noSeqTerm false false e2  in
               let uu____4976 =
                 let uu____4977 =
                   let uu____4978 = str "if"  in
                   let uu____4979 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4978 uu____4979  in
                 let uu____4980 =
                   let uu____4981 =
                     let uu____4982 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4982 e2_doc  in
                   let uu____4983 =
                     let uu____4984 = str "else"  in
                     let uu____4985 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4984 uu____4985  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4981 uu____4983  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4977 uu____4980  in
               FStar_Pprint.group uu____4976)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5008 =
              let uu____5009 =
                let uu____5010 =
                  let uu____5011 = str "try"  in
                  let uu____5012 = p_noSeqTerm false false e1  in
                  prefix2 uu____5011 uu____5012  in
                let uu____5013 =
                  let uu____5014 = str "with"  in
                  let uu____5015 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5014 uu____5015  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5010 uu____5013  in
              FStar_Pprint.group uu____5009  in
            let uu____5024 = paren_if (ps || pb)  in uu____5024 uu____5008
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5051 =
              let uu____5052 =
                let uu____5053 =
                  let uu____5054 = str "match"  in
                  let uu____5055 = p_noSeqTerm false false e1  in
                  let uu____5056 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5054 uu____5055 uu____5056
                   in
                let uu____5057 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5053 uu____5057  in
              FStar_Pprint.group uu____5052  in
            let uu____5066 = paren_if (ps || pb)  in uu____5066 uu____5051
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5073 =
              let uu____5074 =
                let uu____5075 =
                  let uu____5076 = str "let open"  in
                  let uu____5077 = p_quident uid  in
                  let uu____5078 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5076 uu____5077 uu____5078
                   in
                let uu____5079 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5075 uu____5079  in
              FStar_Pprint.group uu____5074  in
            let uu____5080 = paren_if ps  in uu____5080 uu____5073
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5144 is_last =
              match uu____5144 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5177 =
                          let uu____5178 = str "let"  in
                          let uu____5179 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5178 uu____5179
                           in
                        FStar_Pprint.group uu____5177
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5180 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5185 =
                    if is_last
                    then
                      let uu____5186 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5187 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5186 doc_expr uu____5187
                    else
                      (let uu____5189 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5189)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5185
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5235 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5235
                     else
                       (let uu____5243 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5243)) lbs
               in
            let lbs_doc =
              let uu____5251 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5251  in
            let uu____5252 =
              let uu____5253 =
                let uu____5254 =
                  let uu____5255 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5255
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5254  in
              FStar_Pprint.group uu____5253  in
            let uu____5256 = paren_if ps  in uu____5256 uu____5252
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5263;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5266;
                                                             FStar_Parser_AST.level
                                                               = uu____5267;_})
            when matches_var maybe_x x ->
            let uu____5294 =
              let uu____5295 =
                let uu____5296 = str "function"  in
                let uu____5297 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5296 uu____5297  in
              FStar_Pprint.group uu____5295  in
            let uu____5306 = paren_if (ps || pb)  in uu____5306 uu____5294
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5312 =
              let uu____5313 = str "quote"  in
              let uu____5314 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5313 uu____5314  in
            FStar_Pprint.group uu____5312
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5316 =
              let uu____5317 = str "`"  in
              let uu____5318 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5317 uu____5318  in
            FStar_Pprint.group uu____5316
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5320 =
              let uu____5321 = str "`%"  in
              let uu____5322 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5321 uu____5322  in
            FStar_Pprint.group uu____5320
        | FStar_Parser_AST.Antiquote
            {
              FStar_Parser_AST.tm = FStar_Parser_AST.Quote
                (e1,FStar_Parser_AST.Dynamic );
              FStar_Parser_AST.range = uu____5324;
              FStar_Parser_AST.level = uu____5325;_}
            ->
            let uu____5326 =
              let uu____5327 = str "`@"  in
              let uu____5328 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5327 uu____5328  in
            FStar_Pprint.group uu____5326
        | FStar_Parser_AST.Antiquote e1 ->
            let uu____5330 =
              let uu____5331 = str "`#"  in
              let uu____5332 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5331 uu____5332  in
            FStar_Pprint.group uu____5330
        | uu____5333 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___118_5334  ->
    match uu___118_5334 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5346 =
          let uu____5347 = str "[@"  in
          let uu____5348 =
            let uu____5349 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5350 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5349 uu____5350  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5347 uu____5348  in
        FStar_Pprint.group uu____5346

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
                 let uu____5376 =
                   let uu____5377 =
                     let uu____5378 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5378 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5377 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5376 term_doc
             | pats ->
                 let uu____5384 =
                   let uu____5385 =
                     let uu____5386 =
                       let uu____5387 =
                         let uu____5388 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5388
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5387 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5389 = p_trigger trigger  in
                     prefix2 uu____5386 uu____5389  in
                   FStar_Pprint.group uu____5385  in
                 prefix2 uu____5384 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5409 =
                   let uu____5410 =
                     let uu____5411 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5411 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5410 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5409 term_doc
             | pats ->
                 let uu____5417 =
                   let uu____5418 =
                     let uu____5419 =
                       let uu____5420 =
                         let uu____5421 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5421
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5420 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5422 = p_trigger trigger  in
                     prefix2 uu____5419 uu____5422  in
                   FStar_Pprint.group uu____5418  in
                 prefix2 uu____5417 term_doc)
        | uu____5423 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5425 -> str "forall"
    | FStar_Parser_AST.QExists uu____5438 -> str "exists"
    | uu____5451 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___119_5452  ->
    match uu___119_5452 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5464 =
          let uu____5465 =
            let uu____5466 =
              let uu____5467 = str "pattern"  in
              let uu____5468 =
                let uu____5469 =
                  let uu____5470 = p_disjunctivePats pats  in
                  FStar_Pprint.jump (Prims.parse_int "2")
                    (Prims.parse_int "0") uu____5470
                   in
                FStar_Pprint.op_Hat_Hat uu____5469 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5467 uu____5468  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5466  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5465  in
        FStar_Pprint.group uu____5464

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5476 = str "\\/"  in
    FStar_Pprint.separate_map uu____5476 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5482 =
      let uu____5483 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5483 p_appTerm pats  in
    FStar_Pprint.group uu____5482

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5493 =
              let uu____5494 =
                let uu____5495 = str "fun"  in
                let uu____5496 =
                  let uu____5497 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5497
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5495 uu____5496  in
              let uu____5498 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5494 uu____5498  in
            let uu____5499 = paren_if ps  in uu____5499 uu____5493
        | uu____5504 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5508  ->
      match uu____5508 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5531 =
                    let uu____5532 =
                      let uu____5533 =
                        let uu____5534 = p_tuplePattern p  in
                        let uu____5535 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5534 uu____5535  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5533
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5532  in
                  FStar_Pprint.group uu____5531
              | FStar_Pervasives_Native.Some f ->
                  let uu____5537 =
                    let uu____5538 =
                      let uu____5539 =
                        let uu____5540 =
                          let uu____5541 =
                            let uu____5542 = p_tuplePattern p  in
                            let uu____5543 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5542
                              uu____5543
                             in
                          FStar_Pprint.group uu____5541  in
                        let uu____5544 =
                          let uu____5545 =
                            let uu____5548 = p_tmFormula f  in
                            [uu____5548; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5545  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5540 uu____5544
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5539
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5538  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5537
               in
            let uu____5549 =
              let uu____5550 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5550  in
            FStar_Pprint.group uu____5549  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5559 =
                      let uu____5560 =
                        let uu____5561 =
                          let uu____5562 =
                            let uu____5563 =
                              let uu____5564 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5564  in
                            FStar_Pprint.separate_map uu____5563
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5562
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5561
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5560  in
                    FStar_Pprint.group uu____5559
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5565 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5567;_},e1::e2::[])
        ->
        let uu____5572 = str "<==>"  in
        let uu____5573 = p_tmImplies e1  in
        let uu____5574 = p_tmIff e2  in
        infix0 uu____5572 uu____5573 uu____5574
    | uu____5575 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5577;_},e1::e2::[])
        ->
        let uu____5582 = str "==>"  in
        let uu____5583 = p_tmArrow p_tmFormula e1  in
        let uu____5584 = p_tmImplies e2  in
        infix0 uu____5582 uu____5583 uu____5584
    | uu____5585 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5593 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5593 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_5 when _0_5 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5614 ->
               let uu____5615 =
                 let uu____5616 =
                   let uu____5617 =
                     let uu____5618 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5618
                      in
                   FStar_Pprint.separate uu____5617 terms  in
                 let uu____5619 =
                   let uu____5620 =
                     let uu____5621 =
                       let uu____5622 =
                         let uu____5623 =
                           let uu____5624 =
                             let uu____5625 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5625
                              in
                           FStar_Pprint.separate uu____5624 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5623 last_op  in
                       let uu____5626 =
                         let uu____5627 =
                           let uu____5628 =
                             let uu____5629 =
                               let uu____5630 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5630
                                in
                             FStar_Pprint.separate uu____5629 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5628 last_op  in
                         jump2 uu____5627  in
                       FStar_Pprint.ifflat uu____5622 uu____5626  in
                     FStar_Pprint.group uu____5621  in
                   let uu____5631 = FStar_List.hd last1  in
                   prefix2 uu____5620 uu____5631  in
                 FStar_Pprint.ifflat uu____5616 uu____5619  in
               FStar_Pprint.group uu____5615)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5644 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5649 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5644 uu____5649
      | uu____5652 -> let uu____5653 = p_Tm e  in [uu____5653]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5656 =
        let uu____5657 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5657 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656  in
    let disj =
      let uu____5659 =
        let uu____5660 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5660 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5659  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5679;_},e1::e2::[])
        ->
        let uu____5684 = p_tmDisjunction e1  in
        let uu____5689 = let uu____5694 = p_tmConjunction e2  in [uu____5694]
           in
        FStar_List.append uu____5684 uu____5689
    | uu____5703 -> let uu____5704 = p_tmConjunction e  in [uu____5704]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5714;_},e1::e2::[])
        ->
        let uu____5719 = p_tmConjunction e1  in
        let uu____5722 = let uu____5725 = p_tmTuple e2  in [uu____5725]  in
        FStar_List.append uu____5719 uu____5722
    | uu____5726 -> let uu____5727 = p_tmTuple e  in [uu____5727]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when
        (is_tuple_constructor lid) && (all_explicit args) ->
        let uu____5744 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5744
          (fun uu____5752  ->
             match uu____5752 with | (e1,uu____5758) -> p_tmEq e1) args
    | uu____5759 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5764 =
             let uu____5765 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5765  in
           FStar_Pprint.group uu____5764)

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
               (let uu____5782 = FStar_Ident.text_of_id op  in
                uu____5782 = "="))
              ||
              (let uu____5784 = FStar_Ident.text_of_id op  in
               uu____5784 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5786 = levels op1  in
            (match uu____5786 with
             | (left1,mine,right1) ->
                 let uu____5796 =
                   let uu____5797 = FStar_All.pipe_left str op1  in
                   let uu____5798 = p_tmEqWith' p_X left1 e1  in
                   let uu____5799 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5797 uu____5798 uu____5799  in
                 paren_if_gt curr mine uu____5796)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5800;_},e1::e2::[])
            ->
            let uu____5805 =
              let uu____5806 = p_tmEqWith p_X e1  in
              let uu____5807 =
                let uu____5808 =
                  let uu____5809 =
                    let uu____5810 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5810  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5809  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5808  in
              FStar_Pprint.op_Hat_Hat uu____5806 uu____5807  in
            FStar_Pprint.group uu____5805
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5811;_},e1::[])
            ->
            let uu____5815 = levels "-"  in
            (match uu____5815 with
             | (left1,mine,right1) ->
                 let uu____5825 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5825)
        | uu____5826 -> p_tmNoEqWith p_X e

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
              (lid,(e1,uu____5870)::(e2,uu____5872)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5892 = is_list e  in Prims.op_Negation uu____5892)
              ->
              let op = "::"  in
              let uu____5894 = levels op  in
              (match uu____5894 with
               | (left1,mine,right1) ->
                   let uu____5904 =
                     let uu____5905 = str op  in
                     let uu____5906 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____5907 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____5905 uu____5906 uu____5907  in
                   paren_if_gt curr mine uu____5904)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____5923 = levels op  in
              (match uu____5923 with
               | (left1,mine,right1) ->
                   let p_dsumfst bt =
                     match bt with
                     | FStar_Util.Inl b ->
                         let uu____5948 = p_binder false b  in
                         let uu____5949 =
                           let uu____5950 =
                             let uu____5951 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____5951 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____5950
                            in
                         FStar_Pprint.op_Hat_Hat uu____5948 uu____5949
                     | FStar_Util.Inr t ->
                         let uu____5953 = p_tmNoEqWith' false p_X left1 t  in
                         let uu____5954 =
                           let uu____5955 =
                             let uu____5956 = str op  in
                             FStar_Pprint.op_Hat_Hat uu____5956 break1  in
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                             uu____5955
                            in
                         FStar_Pprint.op_Hat_Hat uu____5953 uu____5954
                      in
                   let uu____5957 =
                     let uu____5958 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____5963 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____5958 uu____5963  in
                   paren_if_gt curr mine uu____5957)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____5964;_},e1::e2::[])
              when FStar_ST.op_Bang unfold_tuples ->
              let op = "*"  in
              let uu____5989 = levels op  in
              (match uu____5989 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____5999 = str op  in
                     let uu____6000 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6001 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____5999 uu____6000 uu____6001
                   else
                     (let uu____6003 =
                        let uu____6004 = str op  in
                        let uu____6005 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6006 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6004 uu____6005 uu____6006  in
                      paren_if_gt curr mine uu____6003))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6013 = levels op1  in
              (match uu____6013 with
               | (left1,mine,right1) ->
                   let uu____6023 =
                     let uu____6024 = str op1  in
                     let uu____6025 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6026 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6024 uu____6025 uu____6026  in
                   paren_if_gt curr mine uu____6023)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6045 =
                let uu____6046 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6047 =
                  let uu____6048 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6048 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6046 uu____6047  in
              braces_with_nesting uu____6045
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6053;_},e1::[])
              ->
              let uu____6057 =
                let uu____6058 = str "~"  in
                let uu____6059 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6058 uu____6059  in
              FStar_Pprint.group uu____6057
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6061;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6067 = levels op  in
                   (match uu____6067 with
                    | (left1,mine,right1) ->
                        let uu____6077 =
                          let uu____6078 = str op  in
                          let uu____6079 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6080 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6078 uu____6079 uu____6080  in
                        paren_if_gt curr mine uu____6077)
               | uu____6081 -> p_X e)
          | uu____6082 -> p_X e

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
        let uu____6089 =
          let uu____6090 = p_lident lid  in
          let uu____6091 =
            let uu____6092 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6092  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6090 uu____6091  in
        FStar_Pprint.group uu____6089
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6095 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6097 = p_appTerm e  in
    let uu____6098 =
      let uu____6099 =
        let uu____6100 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6100 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6099  in
    FStar_Pprint.op_Hat_Hat uu____6097 uu____6098

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6105 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6105 t phi
      | FStar_Parser_AST.TAnnotated uu____6106 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6111 ->
          let uu____6112 =
            let uu____6113 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6113
             in
          failwith uu____6112
      | FStar_Parser_AST.TVariable uu____6114 ->
          let uu____6115 =
            let uu____6116 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6116
             in
          failwith uu____6115
      | FStar_Parser_AST.NoName uu____6117 ->
          let uu____6118 =
            let uu____6119 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6119
             in
          failwith uu____6118

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6121  ->
      match uu____6121 with
      | (lid,e) ->
          let uu____6128 =
            let uu____6129 = p_qlident lid  in
            let uu____6130 =
              let uu____6131 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6131
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6129 uu____6130  in
          FStar_Pprint.group uu____6128

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6133 when is_general_application e ->
        let uu____6140 = head_and_args e  in
        (match uu____6140 with
         | (head1,args) ->
             let uu____6165 =
               let uu____6176 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6176
               then
                 let uu____6206 =
                   FStar_Util.take
                     (fun uu____6230  ->
                        match uu____6230 with
                        | (uu____6235,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6206 with
                 | (fs_typ_args,args1) ->
                     let uu____6273 =
                       let uu____6274 = p_indexingTerm head1  in
                       let uu____6275 =
                         let uu____6276 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6276 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6274 uu____6275  in
                     (uu____6273, args1)
               else
                 (let uu____6288 = p_indexingTerm head1  in
                  (uu____6288, args))
                in
             (match uu____6165 with
              | (head_doc,args1) ->
                  let uu____6309 =
                    let uu____6310 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6310 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6309))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6330 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6330)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6348 =
               let uu____6349 = p_quident lid  in
               let uu____6350 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6349 uu____6350  in
             FStar_Pprint.group uu____6348
         | hd1::tl1 ->
             let uu____6367 =
               let uu____6368 =
                 let uu____6369 =
                   let uu____6370 = p_quident lid  in
                   let uu____6371 = p_argTerm hd1  in
                   prefix2 uu____6370 uu____6371  in
                 FStar_Pprint.group uu____6369  in
               let uu____6372 =
                 let uu____6373 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6373  in
               FStar_Pprint.op_Hat_Hat uu____6368 uu____6372  in
             FStar_Pprint.group uu____6367)
    | uu____6378 -> p_indexingTerm e

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
         (let uu____6387 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6387 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6389 = str "#"  in
        let uu____6390 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6389 uu____6390
    | (e,FStar_Parser_AST.HashBrace t) ->
        let uu____6393 = str "#["  in
        let uu____6394 =
          let uu____6395 = p_indexingTerm t  in
          let uu____6396 =
            let uu____6397 = str "]"  in
            let uu____6398 = p_indexingTerm e  in
            FStar_Pprint.op_Hat_Hat uu____6397 uu____6398  in
          FStar_Pprint.op_Hat_Hat uu____6395 uu____6396  in
        FStar_Pprint.op_Hat_Hat uu____6393 uu____6394
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6400  ->
    match uu____6400 with | (e,uu____6406) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6411;_},e1::e2::[])
          ->
          let uu____6416 =
            let uu____6417 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6418 =
              let uu____6419 =
                let uu____6420 = p_term false false e2  in
                soft_parens_with_nesting uu____6420  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6419  in
            FStar_Pprint.op_Hat_Hat uu____6417 uu____6418  in
          FStar_Pprint.group uu____6416
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6421;_},e1::e2::[])
          ->
          let uu____6426 =
            let uu____6427 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6428 =
              let uu____6429 =
                let uu____6430 = p_term false false e2  in
                soft_brackets_with_nesting uu____6430  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6429  in
            FStar_Pprint.op_Hat_Hat uu____6427 uu____6428  in
          FStar_Pprint.group uu____6426
      | uu____6431 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6436 = p_quident lid  in
        let uu____6437 =
          let uu____6438 =
            let uu____6439 = p_term false false e1  in
            soft_parens_with_nesting uu____6439  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6438  in
        FStar_Pprint.op_Hat_Hat uu____6436 uu____6437
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6445 =
          let uu____6446 = FStar_Ident.text_of_id op  in str uu____6446  in
        let uu____6447 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6445 uu____6447
    | uu____6448 -> p_atomicTermNotQUident e

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
         | uu____6457 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6464 =
          let uu____6465 = FStar_Ident.text_of_id op  in str uu____6465  in
        let uu____6466 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6464 uu____6466
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6470 =
          let uu____6471 =
            let uu____6472 =
              let uu____6473 = FStar_Ident.text_of_id op  in str uu____6473
               in
            let uu____6474 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6472 uu____6474  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6471  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6470
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6489 = all_explicit args  in
        if uu____6489
        then
          let uu____6490 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
          let uu____6491 =
            let uu____6492 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1  in
            let uu____6493 = FStar_List.map FStar_Pervasives_Native.fst args
               in
            FStar_Pprint.separate_map uu____6492 p_tmEq uu____6493  in
          let uu____6500 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            uu____6490 uu____6491 uu____6500
        else
          (match args with
           | [] -> p_quident lid
           | arg::[] ->
               let uu____6519 =
                 let uu____6520 = p_quident lid  in
                 let uu____6521 = p_argTerm arg  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____6520 uu____6521  in
               FStar_Pprint.group uu____6519
           | hd1::tl1 ->
               let uu____6538 =
                 let uu____6539 =
                   let uu____6540 =
                     let uu____6541 = p_quident lid  in
                     let uu____6542 = p_argTerm hd1  in
                     prefix2 uu____6541 uu____6542  in
                   FStar_Pprint.group uu____6540  in
                 let uu____6543 =
                   let uu____6544 =
                     FStar_Pprint.separate_map break1 p_argTerm tl1  in
                   jump2 uu____6544  in
                 FStar_Pprint.op_Hat_Hat uu____6539 uu____6543  in
               FStar_Pprint.group uu____6538)
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6551 =
          let uu____6552 = p_atomicTermNotQUident e1  in
          let uu____6553 =
            let uu____6554 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6554  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6552 uu____6553
           in
        FStar_Pprint.group uu____6551
    | uu____6555 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6560 = p_quident constr_lid  in
        let uu____6561 =
          let uu____6562 =
            let uu____6563 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6563  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6562  in
        FStar_Pprint.op_Hat_Hat uu____6560 uu____6561
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6565 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6565 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6567 = p_term false false e1  in
        soft_parens_with_nesting uu____6567
    | uu____6568 when is_array e ->
        let es = extract_from_list e  in
        let uu____6572 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6573 =
          let uu____6574 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6574
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6577 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6572 uu____6573 uu____6577
    | uu____6578 when is_list e ->
        let uu____6579 =
          let uu____6580 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6581 = extract_from_list e  in
          separate_map_or_flow_last uu____6580
            (fun ps  -> p_noSeqTerm ps false) uu____6581
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6579 FStar_Pprint.rbracket
    | uu____6586 when is_lex_list e ->
        let uu____6587 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6588 =
          let uu____6589 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6590 = extract_from_list e  in
          separate_map_or_flow_last uu____6589
            (fun ps  -> p_noSeqTerm ps false) uu____6590
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6587 uu____6588 FStar_Pprint.rbracket
    | uu____6595 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6599 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6600 =
          let uu____6601 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6601 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6599 uu____6600 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6605 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6606 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6605 uu____6606
    | FStar_Parser_AST.Op (op,args) when
        let uu____6613 = handleable_op op args  in
        Prims.op_Negation uu____6613 ->
        let uu____6614 =
          let uu____6615 =
            let uu____6616 = FStar_Ident.text_of_id op  in
            let uu____6617 =
              let uu____6618 =
                let uu____6619 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6619
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6618  in
            Prims.strcat uu____6616 uu____6617  in
          Prims.strcat "Operation " uu____6615  in
        failwith uu____6614
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6621 = str "u#"  in
        let uu____6622 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6621 uu____6622
    | FStar_Parser_AST.Wild  ->
        let uu____6623 = p_term false false e  in
        soft_parens_with_nesting uu____6623
    | FStar_Parser_AST.Const uu____6624 ->
        let uu____6625 = p_term false false e  in
        soft_parens_with_nesting uu____6625
    | FStar_Parser_AST.Op uu____6626 ->
        let uu____6633 = p_term false false e  in
        soft_parens_with_nesting uu____6633
    | FStar_Parser_AST.Tvar uu____6634 ->
        let uu____6635 = p_term false false e  in
        soft_parens_with_nesting uu____6635
    | FStar_Parser_AST.Var uu____6636 ->
        let uu____6637 = p_term false false e  in
        soft_parens_with_nesting uu____6637
    | FStar_Parser_AST.Name uu____6638 ->
        let uu____6639 = p_term false false e  in
        soft_parens_with_nesting uu____6639
    | FStar_Parser_AST.Construct uu____6640 ->
        let uu____6651 = p_term false false e  in
        soft_parens_with_nesting uu____6651
    | FStar_Parser_AST.Abs uu____6652 ->
        let uu____6659 = p_term false false e  in
        soft_parens_with_nesting uu____6659
    | FStar_Parser_AST.App uu____6660 ->
        let uu____6667 = p_term false false e  in
        soft_parens_with_nesting uu____6667
    | FStar_Parser_AST.Let uu____6668 ->
        let uu____6689 = p_term false false e  in
        soft_parens_with_nesting uu____6689
    | FStar_Parser_AST.LetOpen uu____6690 ->
        let uu____6695 = p_term false false e  in
        soft_parens_with_nesting uu____6695
    | FStar_Parser_AST.Seq uu____6696 ->
        let uu____6701 = p_term false false e  in
        soft_parens_with_nesting uu____6701
    | FStar_Parser_AST.Bind uu____6702 ->
        let uu____6709 = p_term false false e  in
        soft_parens_with_nesting uu____6709
    | FStar_Parser_AST.If uu____6710 ->
        let uu____6717 = p_term false false e  in
        soft_parens_with_nesting uu____6717
    | FStar_Parser_AST.Match uu____6718 ->
        let uu____6733 = p_term false false e  in
        soft_parens_with_nesting uu____6733
    | FStar_Parser_AST.TryWith uu____6734 ->
        let uu____6749 = p_term false false e  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.Ascribed uu____6750 ->
        let uu____6759 = p_term false false e  in
        soft_parens_with_nesting uu____6759
    | FStar_Parser_AST.Record uu____6760 ->
        let uu____6773 = p_term false false e  in
        soft_parens_with_nesting uu____6773
    | FStar_Parser_AST.Project uu____6774 ->
        let uu____6779 = p_term false false e  in
        soft_parens_with_nesting uu____6779
    | FStar_Parser_AST.Product uu____6780 ->
        let uu____6787 = p_term false false e  in
        soft_parens_with_nesting uu____6787
    | FStar_Parser_AST.Sum uu____6788 ->
        let uu____6799 = p_term false false e  in
        soft_parens_with_nesting uu____6799
    | FStar_Parser_AST.QForall uu____6800 ->
        let uu____6813 = p_term false false e  in
        soft_parens_with_nesting uu____6813
    | FStar_Parser_AST.QExists uu____6814 ->
        let uu____6827 = p_term false false e  in
        soft_parens_with_nesting uu____6827
    | FStar_Parser_AST.Refine uu____6828 ->
        let uu____6833 = p_term false false e  in
        soft_parens_with_nesting uu____6833
    | FStar_Parser_AST.NamedTyp uu____6834 ->
        let uu____6839 = p_term false false e  in
        soft_parens_with_nesting uu____6839
    | FStar_Parser_AST.Requires uu____6840 ->
        let uu____6847 = p_term false false e  in
        soft_parens_with_nesting uu____6847
    | FStar_Parser_AST.Ensures uu____6848 ->
        let uu____6855 = p_term false false e  in
        soft_parens_with_nesting uu____6855
    | FStar_Parser_AST.Attributes uu____6856 ->
        let uu____6859 = p_term false false e  in
        soft_parens_with_nesting uu____6859
    | FStar_Parser_AST.Quote uu____6860 ->
        let uu____6865 = p_term false false e  in
        soft_parens_with_nesting uu____6865
    | FStar_Parser_AST.VQuote uu____6866 ->
        let uu____6867 = p_term false false e  in
        soft_parens_with_nesting uu____6867
    | FStar_Parser_AST.Antiquote uu____6868 ->
        let uu____6869 = p_term false false e  in
        soft_parens_with_nesting uu____6869

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___122_6870  ->
    match uu___122_6870 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6876) ->
        let uu____6877 = str s  in FStar_Pprint.dquotes uu____6877
    | FStar_Const.Const_bytearray (bytes,uu____6879) ->
        let uu____6884 =
          let uu____6885 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6885  in
        let uu____6886 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6884 uu____6886
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___120_6906 =
          match uu___120_6906 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___121_6912 =
          match uu___121_6912 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6923  ->
               match uu____6923 with
               | (s,w) ->
                   let uu____6930 = signedness s  in
                   let uu____6931 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6930 uu____6931)
            sign_width_opt
           in
        let uu____6932 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6932 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6934 = FStar_Range.string_of_range r  in str uu____6934
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6936 = p_quident lid  in
        let uu____6937 =
          let uu____6938 =
            let uu____6939 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6939  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6938  in
        FStar_Pprint.op_Hat_Hat uu____6936 uu____6937

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6941 = str "u#"  in
    let uu____6942 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6941 uu____6942

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6944;_},u1::u2::[])
        ->
        let uu____6949 =
          let uu____6950 = p_universeFrom u1  in
          let uu____6951 =
            let uu____6952 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6952  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6950 uu____6951  in
        FStar_Pprint.group uu____6949
    | FStar_Parser_AST.App uu____6953 ->
        let uu____6960 = head_and_args u  in
        (match uu____6960 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6986 =
                    let uu____6987 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6988 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6996  ->
                           match uu____6996 with
                           | (u1,uu____7002) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6987 uu____6988  in
                  FStar_Pprint.group uu____6986
              | uu____7003 ->
                  let uu____7004 =
                    let uu____7005 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7005
                     in
                  failwith uu____7004))
    | uu____7006 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7029 = FStar_Ident.text_of_id id1  in str uu____7029
    | FStar_Parser_AST.Paren u1 ->
        let uu____7031 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7031
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7032;_},uu____7033::uu____7034::[])
        ->
        let uu____7037 = p_universeFrom u  in
        soft_parens_with_nesting uu____7037
    | FStar_Parser_AST.App uu____7038 ->
        let uu____7045 = p_universeFrom u  in
        soft_parens_with_nesting uu____7045
    | uu____7046 ->
        let uu____7047 =
          let uu____7048 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7048
           in
        failwith uu____7047

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
       | FStar_Parser_AST.Module (uu____7120,decls) ->
           let uu____7126 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7126
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7135,decls,uu____7137) ->
           let uu____7142 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7142
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7195  ->
         match uu____7195 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7239,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7245,decls,uu____7247) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7292 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7305;
                 FStar_Parser_AST.doc = uu____7306;
                 FStar_Parser_AST.quals = uu____7307;
                 FStar_Parser_AST.attrs = uu____7308;_}::uu____7309 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7315 =
                   let uu____7318 =
                     let uu____7321 = FStar_List.tl ds  in d :: uu____7321
                      in
                   d0 :: uu____7318  in
                 (uu____7315, (d0.FStar_Parser_AST.drange))
             | uu____7326 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7292 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7386 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7386 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7482 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7482, comments1))))))
  