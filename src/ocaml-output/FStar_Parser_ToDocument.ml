open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____24 'Auu____25 .
    Prims.bool -> ('Auu____24 -> 'Auu____25) -> 'Auu____24 -> 'Auu____25
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
  'Auu____134 'Auu____135 .
    'Auu____134 ->
      ('Auu____135 -> 'Auu____134) ->
        'Auu____135 FStar_Pervasives_Native.option -> 'Auu____134
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
  'Auu____218 .
    FStar_Pprint.document ->
      ('Auu____218 -> FStar_Pprint.document) ->
        'Auu____218 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____243 =
          let uu____244 =
            let uu____245 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____245  in
          FStar_Pprint.separate_map uu____244 f l  in
        FStar_Pprint.group uu____243
  
let precede_break_separate_map :
  'Auu____256 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____256 -> FStar_Pprint.document) ->
          'Auu____256 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____286 =
            let uu____287 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____288 =
              let uu____289 = FStar_List.hd l  in
              FStar_All.pipe_right uu____289 f  in
            FStar_Pprint.precede uu____287 uu____288  in
          let uu____290 =
            let uu____291 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____297 =
                   let uu____298 =
                     let uu____299 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____299  in
                   FStar_Pprint.op_Hat_Hat sep uu____298  in
                 FStar_Pprint.op_Hat_Hat break1 uu____297) uu____291
             in
          FStar_Pprint.op_Hat_Hat uu____286 uu____290
  
let concat_break_map :
  'Auu____306 .
    ('Auu____306 -> FStar_Pprint.document) ->
      'Auu____306 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____326 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____330 = f x  in FStar_Pprint.op_Hat_Hat uu____330 break1)
          l
         in
      FStar_Pprint.group uu____326
  
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
    let uu____366 = str "begin"  in
    let uu____367 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____366 contents uu____367
  
let separate_map_last :
  'Auu____376 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____376 -> FStar_Pprint.document) ->
        'Auu____376 Prims.list -> FStar_Pprint.document
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
  'Auu____428 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____428 -> FStar_Pprint.document) ->
        'Auu____428 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____458 =
          let uu____459 =
            let uu____460 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____460  in
          separate_map_last uu____459 f l  in
        FStar_Pprint.group uu____458
  
let separate_map_or_flow :
  'Auu____469 .
    FStar_Pprint.document ->
      ('Auu____469 -> FStar_Pprint.document) ->
        'Auu____469 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____503 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____503 -> FStar_Pprint.document) ->
        'Auu____503 Prims.list -> FStar_Pprint.document
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
  'Auu____555 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____555 -> FStar_Pprint.document) ->
        'Auu____555 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let soft_surround_separate_map :
  'Auu____604 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____604 -> FStar_Pprint.document) ->
                  'Auu____604 Prims.list -> FStar_Pprint.document
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
                    (let uu____657 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____657
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____676 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____676 -> FStar_Pprint.document) ->
                  'Auu____676 Prims.list -> FStar_Pprint.document
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
                    (let uu____729 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____729
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____744  ->
    match uu____744 with
    | (comment,keywords) ->
        let uu____769 =
          let uu____770 =
            let uu____773 = str comment  in
            let uu____774 =
              let uu____777 =
                let uu____780 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____789  ->
                       match uu____789 with
                       | (k,v1) ->
                           let uu____796 =
                             let uu____799 = str k  in
                             let uu____800 =
                               let uu____803 =
                                 let uu____806 = str v1  in [uu____806]  in
                               FStar_Pprint.rarrow :: uu____803  in
                             uu____799 :: uu____800  in
                           FStar_Pprint.concat uu____796) keywords
                   in
                [uu____780]  in
              FStar_Pprint.space :: uu____777  in
            uu____773 :: uu____774  in
          FStar_Pprint.concat uu____770  in
        FStar_Pprint.group uu____769
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____812 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____824 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____824
      | uu____825 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____867::(e2,uu____869)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____892 -> false  in
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
    | FStar_Parser_AST.Construct (uu____910,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____921,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____942 = extract_from_list e2  in e1 :: uu____942
    | uu____945 ->
        let uu____946 =
          let uu____947 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____947  in
        failwith uu____946
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____956;
           FStar_Parser_AST.level = uu____957;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____959 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____967;
           FStar_Parser_AST.level = uu____968;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____970;
                                                        FStar_Parser_AST.level
                                                          = uu____971;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____973;
                                                   FStar_Parser_AST.level =
                                                     uu____974;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____976;
                FStar_Parser_AST.level = uu____977;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____979;
           FStar_Parser_AST.level = uu____980;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____982 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____992 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____993;
           FStar_Parser_AST.range = uu____994;
           FStar_Parser_AST.level = uu____995;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____996;
                                                        FStar_Parser_AST.range
                                                          = uu____997;
                                                        FStar_Parser_AST.level
                                                          = uu____998;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____1000;
                                                   FStar_Parser_AST.level =
                                                     uu____1001;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1002;
                FStar_Parser_AST.range = uu____1003;
                FStar_Parser_AST.level = uu____1004;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1006;
           FStar_Parser_AST.level = uu____1007;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1009 = extract_from_ref_set e1  in
        let uu____1012 = extract_from_ref_set e2  in
        FStar_List.append uu____1009 uu____1012
    | uu____1015 ->
        let uu____1016 =
          let uu____1017 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1017  in
        failwith uu____1016
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1025 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1025
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1031 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1031
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1038 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1038 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1046 = FStar_Ident.text_of_id op  in uu____1046 <> "~"))
  
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
      | uu____1112 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1128 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1134 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1140 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___54_1160  ->
    match uu___54_1160 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___55_1181  ->
      match uu___55_1181 with
      | FStar_Util.Inl c ->
          let uu____1190 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1190 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1201 .
    Prims.string ->
      ('Auu____1201,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1222  ->
      match uu____1222 with
      | (assoc_levels,tokens) ->
          let uu____1250 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1250 <> FStar_Pervasives_Native.None
  
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
  let levels_from_associativity l uu___56_1452 =
    match uu___56_1452 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1482  ->
         match uu____1482 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1541 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1541 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1581) ->
          assoc_levels
      | uu____1610 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1646 .
    ('Auu____1646,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list
      -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1691 =
        FStar_List.tryFind
          (fun uu____1721  ->
             match uu____1721 with
             | (uu____1734,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1691 with
      | FStar_Pervasives_Native.Some ((uu____1756,l1,uu____1758),uu____1759)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1794 =
            let uu____1795 =
              let uu____1796 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1796  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1795
             in
          failwith uu____1794
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____1818 = assign_levels level_associativity_spec op  in
    match uu____1818 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let (operatorInfix0ad12 :
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2 Prims.list)
  = [opinfix0a; opinfix0b; opinfix0c; opinfix0d; opinfix1; opinfix2] 
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____1896 =
      let uu____1905 =
        let uu____1916 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____1916  in
      FStar_List.tryFind uu____1905 operatorInfix0ad12  in
    uu____1896 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3; opinfix4]  in
  fun op  ->
    let uu____2003 =
      let uu____2017 =
        let uu____2033 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2033  in
      FStar_List.tryFind uu____2017 opinfix34  in
    uu____2003 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2089 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2089
    then (Prims.parse_int "1")
    else
      (let uu____2091 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2091
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2100 . FStar_Ident.ident -> 'Auu____2100 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2116 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2116 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2118 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2118
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2119 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2119 [".()<-"; ".[]<-"]
      | uu____2120 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2158 .
    ('Auu____2158 -> FStar_Pprint.document) ->
      'Auu____2158 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2199 = FStar_ST.op_Bang comment_stack  in
          match uu____2199 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2262 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2262
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2303 =
                    let uu____2304 =
                      let uu____2305 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2305
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2304  in
                  comments_before_pos uu____2303 print_pos lookahead_pos))
              else
                (let uu____2307 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2307))
           in
        let uu____2308 =
          let uu____2313 =
            let uu____2314 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2314  in
          let uu____2315 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2313 uu____2315  in
        match uu____2308 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2321 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2321
              else comments  in
            let uu____2327 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2327
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2348 = FStar_ST.op_Bang comment_stack  in
          match uu____2348 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2440 =
                    let uu____2441 =
                      let uu____2442 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2442  in
                    uu____2441 - lbegin  in
                  max k uu____2440  in
                let doc2 =
                  let uu____2444 =
                    let uu____2445 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2446 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2445 uu____2446  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2444  in
                let uu____2447 =
                  let uu____2448 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2448  in
                place_comments_until_pos (Prims.parse_int "1") uu____2447
                  pos_end doc2))
          | uu____2449 ->
              let lnum =
                let uu____2457 =
                  let uu____2458 = FStar_Range.line_of_pos pos_end  in
                  uu____2458 - lbegin  in
                max (Prims.parse_int "1") uu____2457  in
              let uu____2459 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2459
  
let separate_map_with_comments :
  'Auu____2472 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2472 -> FStar_Pprint.document) ->
          'Auu____2472 Prims.list ->
            ('Auu____2472 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2529 x =
              match uu____2529 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2543 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2543 doc1
                     in
                  let uu____2544 =
                    let uu____2545 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2545  in
                  let uu____2546 =
                    let uu____2547 =
                      let uu____2548 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2548  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2547  in
                  (uu____2544, uu____2546)
               in
            let uu____2549 =
              let uu____2556 = FStar_List.hd xs  in
              let uu____2557 = FStar_List.tl xs  in (uu____2556, uu____2557)
               in
            match uu____2549 with
            | (x,xs1) ->
                let init1 =
                  let uu____2573 =
                    let uu____2574 =
                      let uu____2575 = extract_range x  in
                      FStar_Range.end_of_range uu____2575  in
                    FStar_Range.line_of_pos uu____2574  in
                  let uu____2576 =
                    let uu____2577 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2577  in
                  (uu____2573, uu____2576)  in
                let uu____2578 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2578
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3207 =
      let uu____3208 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3209 =
        let uu____3210 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3211 =
          let uu____3212 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3213 =
            let uu____3214 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3214
             in
          FStar_Pprint.op_Hat_Hat uu____3212 uu____3213  in
        FStar_Pprint.op_Hat_Hat uu____3210 uu____3211  in
      FStar_Pprint.op_Hat_Hat uu____3208 uu____3209  in
    FStar_Pprint.group uu____3207

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3219 =
      let uu____3220 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3220  in
    let uu____3221 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3219 FStar_Pprint.space uu____3221
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3222  ->
    match uu____3222 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3258 =
                match uu____3258 with
                | (kwd,arg) ->
                    let uu____3265 = str "@"  in
                    let uu____3266 =
                      let uu____3267 = str kwd  in
                      let uu____3268 =
                        let uu____3269 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3269
                         in
                      FStar_Pprint.op_Hat_Hat uu____3267 uu____3268  in
                    FStar_Pprint.op_Hat_Hat uu____3265 uu____3266
                 in
              let uu____3270 =
                let uu____3271 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3271 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3270
           in
        let uu____3276 =
          let uu____3277 =
            let uu____3278 =
              let uu____3279 =
                let uu____3280 = str doc1  in
                let uu____3281 =
                  let uu____3282 =
                    let uu____3283 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3283  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3282  in
                FStar_Pprint.op_Hat_Hat uu____3280 uu____3281  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3279  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3278  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3277  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3276

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3287 =
          let uu____3288 = str "val"  in
          let uu____3289 =
            let uu____3290 =
              let uu____3291 = p_lident lid  in
              let uu____3292 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3291 uu____3292  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3290  in
          FStar_Pprint.op_Hat_Hat uu____3288 uu____3289  in
        let uu____3293 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3287 uu____3293
    | FStar_Parser_AST.TopLevelLet (uu____3294,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3319 =
               let uu____3320 = str "let"  in
               let uu____3321 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3320 uu____3321  in
             FStar_Pprint.group uu____3319) lbs
    | uu____3322 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___57_3337 =
          match uu___57_3337 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3345 = f x  in
              let uu____3346 =
                let uu____3347 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3347  in
              FStar_Pprint.op_Hat_Hat uu____3345 uu____3346
           in
        let uu____3348 = str "["  in
        let uu____3349 =
          let uu____3350 = p_list' l  in
          let uu____3351 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3350 uu____3351  in
        FStar_Pprint.op_Hat_Hat uu____3348 uu____3349

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3354 =
          let uu____3355 = str "open"  in
          let uu____3356 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3355 uu____3356  in
        FStar_Pprint.group uu____3354
    | FStar_Parser_AST.Include uid ->
        let uu____3358 =
          let uu____3359 = str "include"  in
          let uu____3360 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3359 uu____3360  in
        FStar_Pprint.group uu____3358
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3363 =
          let uu____3364 = str "module"  in
          let uu____3365 =
            let uu____3366 =
              let uu____3367 = p_uident uid1  in
              let uu____3368 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3367 uu____3368  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3366  in
          FStar_Pprint.op_Hat_Hat uu____3364 uu____3365  in
        let uu____3369 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3363 uu____3369
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3371 =
          let uu____3372 = str "module"  in
          let uu____3373 =
            let uu____3374 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3374  in
          FStar_Pprint.op_Hat_Hat uu____3372 uu____3373  in
        FStar_Pprint.group uu____3371
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3407 = str "effect"  in
          let uu____3408 =
            let uu____3409 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3409  in
          FStar_Pprint.op_Hat_Hat uu____3407 uu____3408  in
        let uu____3410 =
          let uu____3411 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3411 FStar_Pprint.equals
           in
        let uu____3412 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3410 uu____3412
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3430 = str "type"  in
        let uu____3431 = str "and"  in
        precede_break_separate_map uu____3430 uu____3431 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3453 = str "let"  in
          let uu____3454 =
            let uu____3455 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3455 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3453 uu____3454  in
        let uu____3456 =
          let uu____3457 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3457 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3456 p_letbinding lbs
          (fun uu____3465  ->
             match uu____3465 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3474 =
          let uu____3475 = str "val"  in
          let uu____3476 =
            let uu____3477 =
              let uu____3478 = p_lident lid  in
              let uu____3479 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3478 uu____3479  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3477  in
          FStar_Pprint.op_Hat_Hat uu____3475 uu____3476  in
        let uu____3480 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3474 uu____3480
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3484 =
            let uu____3485 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3485 FStar_Util.is_upper  in
          if uu____3484
          then FStar_Pprint.empty
          else
            (let uu____3487 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3487 FStar_Pprint.space)
           in
        let uu____3488 =
          let uu____3489 =
            let uu____3490 = p_ident id1  in
            let uu____3491 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3490 uu____3491  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3489  in
        let uu____3492 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3488 uu____3492
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3499 = str "exception"  in
        let uu____3500 =
          let uu____3501 =
            let uu____3502 = p_uident uid  in
            let uu____3503 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3507 =
                     let uu____3508 = str "of"  in
                     let uu____3509 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3508 uu____3509  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3507) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3502 uu____3503  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3501  in
        FStar_Pprint.op_Hat_Hat uu____3499 uu____3500
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3511 = str "new_effect"  in
        let uu____3512 =
          let uu____3513 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3513  in
        FStar_Pprint.op_Hat_Hat uu____3511 uu____3512
    | FStar_Parser_AST.SubEffect se ->
        let uu____3515 = str "sub_effect"  in
        let uu____3516 =
          let uu____3517 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3517  in
        FStar_Pprint.op_Hat_Hat uu____3515 uu____3516
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3520 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3520 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3521 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3522) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3545 = str "%splice"  in
        let uu____3546 =
          let uu____3547 =
            let uu____3548 = str ";"  in p_list p_uident uu____3548 ids  in
          let uu____3549 =
            let uu____3550 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3550  in
          FStar_Pprint.op_Hat_Hat uu____3547 uu____3549  in
        FStar_Pprint.op_Hat_Hat uu____3545 uu____3546

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___58_3551  ->
    match uu___58_3551 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3553 = str "#set-options"  in
        let uu____3554 =
          let uu____3555 =
            let uu____3556 = str s  in FStar_Pprint.dquotes uu____3556  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3555  in
        FStar_Pprint.op_Hat_Hat uu____3553 uu____3554
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3560 = str "#reset-options"  in
        let uu____3561 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3565 =
                 let uu____3566 = str s  in FStar_Pprint.dquotes uu____3566
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3565) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3560 uu____3561
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3594  ->
    match uu____3594 with
    | (typedecl,fsdoc_opt) ->
        let uu____3607 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3608 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3607 uu____3608

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___59_3609  ->
    match uu___59_3609 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3626 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3644 =
          let uu____3645 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3645  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3696 =
          match uu____3696 with
          | (lid1,t,doc_opt) ->
              let uu____3712 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3712
           in
        let p_fields uu____3728 =
          let uu____3729 =
            let uu____3730 =
              let uu____3731 =
                let uu____3732 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3732 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3731  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3730  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3729  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3798 =
          match uu____3798 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3824 =
                  let uu____3825 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3825  in
                FStar_Range.extend_to_end_of_line uu____3824  in
              let p_constructorBranch decl =
                let uu____3860 =
                  let uu____3861 =
                    let uu____3862 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3862  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3861  in
                FStar_Pprint.group uu____3860  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3884 =
          let uu____3885 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3885  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3900  ->
             let uu____3901 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3901)

and (p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (unit -> FStar_Pprint.document) -> FStar_Pprint.document)
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____3916 = p_ident lid  in
            let uu____3917 =
              let uu____3918 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3918  in
            FStar_Pprint.op_Hat_Hat uu____3916 uu____3917
          else
            (let binders_doc =
               let uu____3921 = p_typars bs  in
               let uu____3922 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3926 =
                        let uu____3927 =
                          let uu____3928 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3928
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3927
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3926) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3921 uu____3922  in
             let uu____3929 = p_ident lid  in
             let uu____3930 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3929 binders_doc uu____3930)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____3932  ->
      match uu____3932 with
      | (lid,t,doc_opt) ->
          let uu____3948 =
            let uu____3949 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____3950 =
              let uu____3951 = p_lident lid  in
              let uu____3952 =
                let uu____3953 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3953  in
              FStar_Pprint.op_Hat_Hat uu____3951 uu____3952  in
            FStar_Pprint.op_Hat_Hat uu____3949 uu____3950  in
          FStar_Pprint.group uu____3948

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____3954  ->
    match uu____3954 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3982 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3983 =
          let uu____3984 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3985 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3990 =
                   let uu____3991 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3991  in
                 let uu____3992 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____3990 uu____3992) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3984 uu____3985  in
        FStar_Pprint.op_Hat_Hat uu____3982 uu____3983

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3993  ->
    match uu____3993 with
    | (pat,uu____3999) ->
        let uu____4000 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4019 =
                let uu____4020 =
                  let uu____4021 =
                    let uu____4022 =
                      let uu____4023 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4023
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4022  in
                  FStar_Pprint.group uu____4021  in
                FStar_Pprint.op_Hat_Hat break1 uu____4020  in
              (pat1, uu____4019)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4035 =
                let uu____4036 =
                  let uu____4037 =
                    let uu____4038 =
                      let uu____4039 =
                        let uu____4040 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4040
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4039
                       in
                    FStar_Pprint.group uu____4038  in
                  let uu____4041 =
                    let uu____4042 =
                      let uu____4043 = str "by"  in
                      let uu____4044 =
                        let uu____4045 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4045
                         in
                      FStar_Pprint.op_Hat_Hat uu____4043 uu____4044  in
                    FStar_Pprint.group uu____4042  in
                  FStar_Pprint.op_Hat_Hat uu____4037 uu____4041  in
                FStar_Pprint.op_Hat_Hat break1 uu____4036  in
              (pat1, uu____4035)
          | uu____4046 -> (pat, FStar_Pprint.empty)  in
        (match uu____4000 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4050);
                     FStar_Parser_AST.prange = uu____4051;_},pats)
                  ->
                  let uu____4061 =
                    let uu____4062 = p_lident x  in
                    let uu____4063 =
                      let uu____4064 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4064 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4062 uu____4063  in
                  FStar_Pprint.group uu____4061
              | uu____4065 ->
                  let uu____4066 =
                    let uu____4067 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4067 ascr_doc  in
                  FStar_Pprint.group uu____4066))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4068  ->
    match uu____4068 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4076 =
          let uu____4077 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4077  in
        let uu____4078 = p_term false false e  in
        prefix2 uu____4076 uu____4078

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___60_4079  ->
    match uu___60_4079 with
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
        let uu____4104 = p_uident uid  in
        let uu____4105 = p_binders true bs  in
        let uu____4106 =
          let uu____4107 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4107  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4104 uu____4105 uu____4106

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
          let uu____4116 =
            let uu____4117 =
              let uu____4118 =
                let uu____4119 = p_uident uid  in
                let uu____4120 = p_binders true bs  in
                let uu____4121 =
                  let uu____4122 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4122  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4119 uu____4120 uu____4121
                 in
              FStar_Pprint.group uu____4118  in
            let uu____4123 =
              let uu____4124 = str "with"  in
              let uu____4125 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4124 uu____4125  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4117 uu____4123  in
          braces_with_nesting uu____4116

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
          let uu____4156 =
            let uu____4157 = p_lident lid  in
            let uu____4158 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4157 uu____4158  in
          let uu____4159 = p_simpleTerm ps false e  in
          prefix2 uu____4156 uu____4159
      | uu____4160 ->
          let uu____4161 =
            let uu____4162 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4162
             in
          failwith uu____4161

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4224 =
        match uu____4224 with
        | (kwd,t) ->
            let uu____4231 =
              let uu____4232 = str kwd  in
              let uu____4233 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4232 uu____4233  in
            let uu____4234 = p_simpleTerm ps false t  in
            prefix2 uu____4231 uu____4234
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4239 =
      let uu____4240 =
        let uu____4241 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4242 =
          let uu____4243 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4243  in
        FStar_Pprint.op_Hat_Hat uu____4241 uu____4242  in
      let uu____4244 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4240 uu____4244  in
    let uu____4245 =
      let uu____4246 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4246  in
    FStar_Pprint.op_Hat_Hat uu____4239 uu____4245

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___61_4247  ->
    match uu___61_4247 with
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
    let uu____4249 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4249

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___62_4250  ->
    match uu___62_4250 with
    | FStar_Parser_AST.Rec  ->
        let uu____4251 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4251
    | FStar_Parser_AST.Mutable  ->
        let uu____4252 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4252
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___63_4253  ->
    match uu___63_4253 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4258 =
          let uu____4259 =
            let uu____4260 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4260  in
          FStar_Pprint.separate_map uu____4259 p_tuplePattern pats  in
        FStar_Pprint.group uu____4258
    | uu____4261 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4268 =
          let uu____4269 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4269 p_constructorPattern pats  in
        FStar_Pprint.group uu____4268
    | uu____4270 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4273;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4278 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4279 = p_constructorPattern hd1  in
        let uu____4280 = p_constructorPattern tl1  in
        infix0 uu____4278 uu____4279 uu____4280
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4282;_},pats)
        ->
        let uu____4288 = p_quident uid  in
        let uu____4289 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4288 uu____4289
    | uu____4290 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4306;
               FStar_Parser_AST.blevel = uu____4307;
               FStar_Parser_AST.aqual = uu____4308;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4314 =
               let uu____4315 = p_ident lid  in
               p_refinement aqual uu____4315 t1 phi  in
             soft_parens_with_nesting uu____4314
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4317;
               FStar_Parser_AST.blevel = uu____4318;
               FStar_Parser_AST.aqual = uu____4319;_},phi))
             ->
             let uu____4321 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4321
         | uu____4322 ->
             let uu____4327 =
               let uu____4328 = p_tuplePattern pat  in
               let uu____4329 =
                 let uu____4330 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4331 =
                   let uu____4332 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4332  in
                 FStar_Pprint.op_Hat_Hat uu____4330 uu____4331  in
               FStar_Pprint.op_Hat_Hat uu____4328 uu____4329  in
             soft_parens_with_nesting uu____4327)
    | FStar_Parser_AST.PatList pats ->
        let uu____4336 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4336 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4353 =
          match uu____4353 with
          | (lid,pat) ->
              let uu____4360 = p_qlident lid  in
              let uu____4361 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4360 uu____4361
           in
        let uu____4362 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4362
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4372 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4373 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4374 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4372 uu____4373 uu____4374
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4383 =
          let uu____4384 =
            let uu____4385 =
              let uu____4386 = FStar_Ident.text_of_id op  in str uu____4386
               in
            let uu____4387 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4385 uu____4387  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4384  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4383
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4395 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4396 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4395 uu____4396
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4398 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4401;
           FStar_Parser_AST.prange = uu____4402;_},uu____4403)
        ->
        let uu____4408 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4408
    | FStar_Parser_AST.PatTuple (uu____4409,false ) ->
        let uu____4414 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4414
    | uu____4415 ->
        let uu____4416 =
          let uu____4417 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4417  in
        failwith uu____4416

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4421 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4422 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4421 uu____4422
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4429;
                   FStar_Parser_AST.blevel = uu____4430;
                   FStar_Parser_AST.aqual = uu____4431;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4433 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4433 t1 phi
            | uu____4434 ->
                let uu____4435 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4436 =
                  let uu____4437 = p_lident lid  in
                  let uu____4438 =
                    let uu____4439 =
                      let uu____4440 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4441 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4440 uu____4441  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4439  in
                  FStar_Pprint.op_Hat_Hat uu____4437 uu____4438  in
                FStar_Pprint.op_Hat_Hat uu____4435 uu____4436
             in
          if is_atomic
          then
            let uu____4442 =
              let uu____4443 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4443  in
            FStar_Pprint.group uu____4442
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4445 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4452;
                  FStar_Parser_AST.blevel = uu____4453;
                  FStar_Parser_AST.aqual = uu____4454;_},phi)
               ->
               if is_atomic
               then
                 let uu____4456 =
                   let uu____4457 =
                     let uu____4458 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4458 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4457  in
                 FStar_Pprint.group uu____4456
               else
                 (let uu____4460 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4460)
           | uu____4461 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4469 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4470 =
            let uu____4471 =
              let uu____4472 =
                let uu____4473 = p_appTerm t  in
                let uu____4474 =
                  let uu____4475 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4475  in
                FStar_Pprint.op_Hat_Hat uu____4473 uu____4474  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4472  in
            FStar_Pprint.op_Hat_Hat binder uu____4471  in
          FStar_Pprint.op_Hat_Hat uu____4469 uu____4470

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____4481 = FStar_Ident.text_of_lid lid  in str uu____4481

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____4483 = FStar_Ident.text_of_lid lid  in str uu____4483

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4485 = FStar_Ident.text_of_id lid  in str uu____4485

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4487 = FStar_Ident.text_of_id lid  in str uu____4487

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4489 = FStar_Ident.text_of_id lid  in str uu____4489

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4491 = FStar_Ident.text_of_id lid  in str uu____4491

and (p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1

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
            let uu____4510 =
              let uu____4511 =
                let uu____4512 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4512 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4511  in
            let uu____4513 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4510 uu____4513
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4517 =
              let uu____4518 =
                let uu____4519 =
                  let uu____4520 = p_lident x  in
                  let uu____4521 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4520 uu____4521  in
                let uu____4522 =
                  let uu____4523 = p_noSeqTerm true false e1  in
                  let uu____4524 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4523 uu____4524  in
                op_Hat_Slash_Plus_Hat uu____4519 uu____4522  in
              FStar_Pprint.group uu____4518  in
            let uu____4525 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4517 uu____4525
        | uu____4526 ->
            let uu____4527 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4527

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
            let uu____4538 =
              let uu____4539 = p_tmIff e1  in
              let uu____4540 =
                let uu____4541 =
                  let uu____4542 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4542
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4541  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4539 uu____4540  in
            FStar_Pprint.group uu____4538
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4548 =
              let uu____4549 = p_tmIff e1  in
              let uu____4550 =
                let uu____4551 =
                  let uu____4552 =
                    let uu____4553 = p_typ false false t  in
                    let uu____4554 =
                      let uu____4555 = str "by"  in
                      let uu____4556 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4555 uu____4556  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4553 uu____4554  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4552
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4551  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4549 uu____4550  in
            FStar_Pprint.group uu____4548
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4557;_},e1::e2::e3::[])
            ->
            let uu____4563 =
              let uu____4564 =
                let uu____4565 =
                  let uu____4566 = p_atomicTermNotQUident e1  in
                  let uu____4567 =
                    let uu____4568 =
                      let uu____4569 =
                        let uu____4570 = p_term false false e2  in
                        soft_parens_with_nesting uu____4570  in
                      let uu____4571 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4569 uu____4571  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4568  in
                  FStar_Pprint.op_Hat_Hat uu____4566 uu____4567  in
                FStar_Pprint.group uu____4565  in
              let uu____4572 =
                let uu____4573 = p_noSeqTerm ps pb e3  in jump2 uu____4573
                 in
              FStar_Pprint.op_Hat_Hat uu____4564 uu____4572  in
            FStar_Pprint.group uu____4563
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4574;_},e1::e2::e3::[])
            ->
            let uu____4580 =
              let uu____4581 =
                let uu____4582 =
                  let uu____4583 = p_atomicTermNotQUident e1  in
                  let uu____4584 =
                    let uu____4585 =
                      let uu____4586 =
                        let uu____4587 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4587  in
                      let uu____4588 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4586 uu____4588  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4585  in
                  FStar_Pprint.op_Hat_Hat uu____4583 uu____4584  in
                FStar_Pprint.group uu____4582  in
              let uu____4589 =
                let uu____4590 = p_noSeqTerm ps pb e3  in jump2 uu____4590
                 in
              FStar_Pprint.op_Hat_Hat uu____4581 uu____4589  in
            FStar_Pprint.group uu____4580
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4598 =
              let uu____4599 = str "requires"  in
              let uu____4600 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4599 uu____4600  in
            FStar_Pprint.group uu____4598
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4608 =
              let uu____4609 = str "ensures"  in
              let uu____4610 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4609 uu____4610  in
            FStar_Pprint.group uu____4608
        | FStar_Parser_AST.Attributes es ->
            let uu____4614 =
              let uu____4615 = str "attributes"  in
              let uu____4616 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4615 uu____4616  in
            FStar_Pprint.group uu____4614
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4620 =
                let uu____4621 =
                  let uu____4622 = str "if"  in
                  let uu____4623 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4622 uu____4623  in
                let uu____4624 =
                  let uu____4625 = str "then"  in
                  let uu____4626 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4625 uu____4626  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4621 uu____4624  in
              FStar_Pprint.group uu____4620
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4629,uu____4630,e31) when
                     is_unit e31 ->
                     let uu____4632 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4632
                 | uu____4633 -> p_noSeqTerm false false e2  in
               let uu____4634 =
                 let uu____4635 =
                   let uu____4636 = str "if"  in
                   let uu____4637 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4636 uu____4637  in
                 let uu____4638 =
                   let uu____4639 =
                     let uu____4640 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4640 e2_doc  in
                   let uu____4641 =
                     let uu____4642 = str "else"  in
                     let uu____4643 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4642 uu____4643  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4639 uu____4641  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4635 uu____4638  in
               FStar_Pprint.group uu____4634)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4666 =
              let uu____4667 =
                let uu____4668 =
                  let uu____4669 = str "try"  in
                  let uu____4670 = p_noSeqTerm false false e1  in
                  prefix2 uu____4669 uu____4670  in
                let uu____4671 =
                  let uu____4672 = str "with"  in
                  let uu____4673 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4672 uu____4673  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4668 uu____4671  in
              FStar_Pprint.group uu____4667  in
            let uu____4682 = paren_if (ps || pb)  in uu____4682 uu____4666
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4709 =
              let uu____4710 =
                let uu____4711 =
                  let uu____4712 = str "match"  in
                  let uu____4713 = p_noSeqTerm false false e1  in
                  let uu____4714 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4712 uu____4713 uu____4714
                   in
                let uu____4715 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4711 uu____4715  in
              FStar_Pprint.group uu____4710  in
            let uu____4724 = paren_if (ps || pb)  in uu____4724 uu____4709
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4731 =
              let uu____4732 =
                let uu____4733 =
                  let uu____4734 = str "let open"  in
                  let uu____4735 = p_quident uid  in
                  let uu____4736 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4734 uu____4735 uu____4736
                   in
                let uu____4737 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4733 uu____4737  in
              FStar_Pprint.group uu____4732  in
            let uu____4738 = paren_if ps  in uu____4738 uu____4731
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____4802 is_last =
              match uu____4802 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____4835 =
                          let uu____4836 = str "let"  in
                          let uu____4837 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4836 uu____4837
                           in
                        FStar_Pprint.group uu____4835
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____4838 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____4843 =
                    if is_last
                    then
                      let uu____4844 =
                        let uu____4845 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____4846 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____4845 doc_expr
                          uu____4846
                         in
                      FStar_Pprint.group uu____4844
                    else
                      (let uu____4848 =
                         let uu____4849 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____4849 doc_expr
                          in
                       FStar_Pprint.group uu____4848)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____4843
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____4895 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____4895
                     else
                       (let uu____4903 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____4903)) lbs
               in
            let lbs_doc =
              let uu____4911 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____4911  in
            let uu____4912 =
              let uu____4913 =
                let uu____4914 =
                  let uu____4915 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4915
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____4914  in
              FStar_Pprint.group uu____4913  in
            let uu____4916 = paren_if ps  in uu____4916 uu____4912
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4923;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____4926;
                                                             FStar_Parser_AST.level
                                                               = uu____4927;_})
            when matches_var maybe_x x ->
            let uu____4954 =
              let uu____4955 =
                let uu____4956 = str "function"  in
                let uu____4957 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4956 uu____4957  in
              FStar_Pprint.group uu____4955  in
            let uu____4966 = paren_if (ps || pb)  in uu____4966 uu____4954
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____4972 =
              let uu____4973 = str "quote"  in
              let uu____4974 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4973 uu____4974  in
            FStar_Pprint.group uu____4972
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____4976 =
              let uu____4977 = str "`"  in
              let uu____4978 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4977 uu____4978  in
            FStar_Pprint.group uu____4976
        | FStar_Parser_AST.VQuote e1 ->
            let uu____4980 =
              let uu____4981 = str "%`"  in
              let uu____4982 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4981 uu____4982  in
            FStar_Pprint.group uu____4980
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____4984 =
              let uu____4985 = str "`#"  in
              let uu____4986 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4985 uu____4986  in
            FStar_Pprint.group uu____4984
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____4988 =
              let uu____4989 = str "`@"  in
              let uu____4990 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4989 uu____4990  in
            FStar_Pprint.group uu____4988
        | uu____4991 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___64_4992  ->
    match uu___64_4992 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5004 =
          let uu____5005 =
            let uu____5006 = str "[@"  in
            let uu____5007 =
              let uu____5008 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5009 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5008 uu____5009  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5006 uu____5007  in
          FStar_Pprint.group uu____5005  in
        FStar_Pprint.op_Hat_Hat uu____5004 break1

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
            let uu____5031 =
              let uu____5032 =
                let uu____5033 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5033 FStar_Pprint.space  in
              let uu____5034 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5032 uu____5034 FStar_Pprint.dot
               in
            let uu____5035 =
              let uu____5036 = p_trigger trigger  in
              let uu____5037 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5036 uu____5037  in
            prefix2 uu____5031 uu____5035
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5053 =
              let uu____5054 =
                let uu____5055 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5055 FStar_Pprint.space  in
              let uu____5056 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5054 uu____5056 FStar_Pprint.dot
               in
            let uu____5057 =
              let uu____5058 = p_trigger trigger  in
              let uu____5059 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5058 uu____5059  in
            prefix2 uu____5053 uu____5057
        | uu____5060 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5062 -> str "forall"
    | FStar_Parser_AST.QExists uu____5075 -> str "exists"
    | uu____5088 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___65_5089  ->
    match uu___65_5089 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5101 =
          let uu____5102 =
            let uu____5103 = str "pattern"  in
            let uu____5104 =
              let uu____5105 =
                let uu____5106 = p_disjunctivePats pats  in jump2 uu____5106
                 in
              let uu____5107 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5105 uu____5107  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5103 uu____5104  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5102  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5101

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5113 = str "\\/"  in
    FStar_Pprint.separate_map uu____5113 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5119 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5119

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5129 =
              let uu____5130 =
                let uu____5131 = str "fun"  in
                let uu____5132 =
                  let uu____5133 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5133
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5131 uu____5132  in
              let uu____5134 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5130 uu____5134  in
            let uu____5135 = paren_if ps  in uu____5135 uu____5129
        | uu____5140 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5144  ->
      match uu____5144 with
      | (pat,when_opt,e) ->
          let uu____5160 =
            let uu____5161 =
              let uu____5162 =
                let uu____5163 =
                  let uu____5164 =
                    let uu____5165 = p_disjunctivePattern pat  in
                    let uu____5166 =
                      let uu____5167 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5167 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5165 uu____5166  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5164  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5163  in
              FStar_Pprint.group uu____5162  in
            let uu____5168 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5161 uu____5168  in
          FStar_Pprint.group uu____5160

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___66_5169  ->
    match uu___66_5169 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5173 = str "when"  in
        let uu____5174 =
          let uu____5175 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5175 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5173 uu____5174

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5177;_},e1::e2::[])
        ->
        let uu____5182 = str "<==>"  in
        let uu____5183 = p_tmImplies e1  in
        let uu____5184 = p_tmIff e2  in
        infix0 uu____5182 uu____5183 uu____5184
    | uu____5185 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5187;_},e1::e2::[])
        ->
        let uu____5192 = str "==>"  in
        let uu____5193 = p_tmArrow p_tmFormula e1  in
        let uu____5194 = p_tmImplies e2  in
        infix0 uu____5192 uu____5193 uu____5194
    | uu____5195 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5206 =
            let uu____5207 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5212 = p_binder false b  in
                   let uu____5213 =
                     let uu____5214 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5214
                      in
                   FStar_Pprint.op_Hat_Hat uu____5212 uu____5213) bs
               in
            let uu____5215 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5207 uu____5215  in
          FStar_Pprint.group uu____5206
      | uu____5216 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5218;_},e1::e2::[])
        ->
        let uu____5223 = str "\\/"  in
        let uu____5224 = p_tmFormula e1  in
        let uu____5225 = p_tmConjunction e2  in
        infix0 uu____5223 uu____5224 uu____5225
    | uu____5226 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5228;_},e1::e2::[])
        ->
        let uu____5233 = str "/\\"  in
        let uu____5234 = p_tmConjunction e1  in
        let uu____5235 = p_tmTuple e2  in
        infix0 uu____5233 uu____5234 uu____5235
    | uu____5236 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5253 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5253
          (fun uu____5261  ->
             match uu____5261 with | (e1,uu____5267) -> p_tmEq e1) args
    | uu____5268 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5273 =
             let uu____5274 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5274  in
           FStar_Pprint.group uu____5273)

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
               (let uu____5315 = FStar_Ident.text_of_id op  in
                uu____5315 = "="))
              ||
              (let uu____5317 = FStar_Ident.text_of_id op  in
               uu____5317 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5319 = levels op1  in
            (match uu____5319 with
             | (left1,mine,right1) ->
                 let uu____5329 =
                   let uu____5330 = FStar_All.pipe_left str op1  in
                   let uu____5331 = p_tmEqWith' p_X left1 e1  in
                   let uu____5332 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5330 uu____5331 uu____5332  in
                 paren_if_gt curr mine uu____5329)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5333;_},e1::e2::[])
            ->
            let uu____5338 =
              let uu____5339 = p_tmEqWith p_X e1  in
              let uu____5340 =
                let uu____5341 =
                  let uu____5342 =
                    let uu____5343 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5343  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5342  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5341  in
              FStar_Pprint.op_Hat_Hat uu____5339 uu____5340  in
            FStar_Pprint.group uu____5338
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5344;_},e1::[])
            ->
            let uu____5348 = levels "-"  in
            (match uu____5348 with
             | (left1,mine,right1) ->
                 let uu____5358 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5358)
        | uu____5359 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon; amp; opinfix3; opinfix4]  in
      p_tmNoEqWith' p_X n1 e

and (p_tmNoEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct
            (lid,(e1,uu____5402)::(e2,uu____5404)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5424 = is_list e  in Prims.op_Negation uu____5424)
            ->
            let op = "::"  in
            let uu____5426 = levels op  in
            (match uu____5426 with
             | (left1,mine,right1) ->
                 let uu____5436 =
                   let uu____5437 = str op  in
                   let uu____5438 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5439 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5437 uu____5438 uu____5439  in
                 paren_if_gt curr mine uu____5436)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5447 = levels op  in
            (match uu____5447 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5463 = p_binder false b  in
                   let uu____5464 =
                     let uu____5465 =
                       let uu____5466 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5466 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5465
                      in
                   FStar_Pprint.op_Hat_Hat uu____5463 uu____5464  in
                 let uu____5467 =
                   let uu____5468 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5469 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5468 uu____5469  in
                 paren_if_gt curr mine uu____5467)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5476 = levels op1  in
            (match uu____5476 with
             | (left1,mine,right1) ->
                 let uu____5486 =
                   let uu____5487 = str op1  in
                   let uu____5488 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5489 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5487 uu____5488 uu____5489  in
                 paren_if_gt curr mine uu____5486)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5508 =
              let uu____5509 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5510 =
                let uu____5511 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5511 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5509 uu____5510  in
            braces_with_nesting uu____5508
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5516;_},e1::[])
            ->
            let uu____5520 =
              let uu____5521 = str "~"  in
              let uu____5522 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5521 uu____5522  in
            FStar_Pprint.group uu____5520
        | uu____5523 -> p_X e

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
        let uu____5530 =
          let uu____5531 = p_lidentOrUnderscore lid  in
          let uu____5532 =
            let uu____5533 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5533  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5531 uu____5532  in
        FStar_Pprint.group uu____5530
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5536 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5538 = p_appTerm e  in
    let uu____5539 =
      let uu____5540 =
        let uu____5541 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5541 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5540  in
    FStar_Pprint.op_Hat_Hat uu____5538 uu____5539

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5546 =
            let uu____5547 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5547 t phi  in
          soft_parens_with_nesting uu____5546
      | FStar_Parser_AST.TAnnotated uu____5548 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5553 ->
          let uu____5554 =
            let uu____5555 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5555
             in
          failwith uu____5554
      | FStar_Parser_AST.TVariable uu____5556 ->
          let uu____5557 =
            let uu____5558 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5558
             in
          failwith uu____5557
      | FStar_Parser_AST.NoName uu____5559 ->
          let uu____5560 =
            let uu____5561 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5561
             in
          failwith uu____5560

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5563  ->
      match uu____5563 with
      | (lid,e) ->
          let uu____5570 =
            let uu____5571 = p_qlident lid  in
            let uu____5572 =
              let uu____5573 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5573
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5571 uu____5572  in
          FStar_Pprint.group uu____5570

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5575 when is_general_application e ->
        let uu____5582 = head_and_args e  in
        (match uu____5582 with
         | (head1,args) ->
             let uu____5607 =
               let uu____5618 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5618
               then
                 let uu____5652 =
                   FStar_Util.take
                     (fun uu____5676  ->
                        match uu____5676 with
                        | (uu____5681,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5652 with
                 | (fs_typ_args,args1) ->
                     let uu____5719 =
                       let uu____5720 = p_indexingTerm head1  in
                       let uu____5721 =
                         let uu____5722 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5722 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5720 uu____5721  in
                     (uu____5719, args1)
               else
                 (let uu____5734 = p_indexingTerm head1  in
                  (uu____5734, args))
                in
             (match uu____5607 with
              | (head_doc,args1) ->
                  let uu____5755 =
                    let uu____5756 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5756 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5755))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5776 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5776)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5794 =
               let uu____5795 = p_quident lid  in
               let uu____5796 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5795 uu____5796  in
             FStar_Pprint.group uu____5794
         | hd1::tl1 ->
             let uu____5813 =
               let uu____5814 =
                 let uu____5815 =
                   let uu____5816 = p_quident lid  in
                   let uu____5817 = p_argTerm hd1  in
                   prefix2 uu____5816 uu____5817  in
                 FStar_Pprint.group uu____5815  in
               let uu____5818 =
                 let uu____5819 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5819  in
               FStar_Pprint.op_Hat_Hat uu____5814 uu____5818  in
             FStar_Pprint.group uu____5813)
    | uu____5824 -> p_indexingTerm e

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
         (let uu____5833 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5833 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5835 = str "#"  in
        let uu____5836 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5835 uu____5836
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5838  ->
    match uu____5838 with | (e,uu____5844) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5849;_},e1::e2::[])
          ->
          let uu____5854 =
            let uu____5855 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5856 =
              let uu____5857 =
                let uu____5858 = p_term false false e2  in
                soft_parens_with_nesting uu____5858  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5857  in
            FStar_Pprint.op_Hat_Hat uu____5855 uu____5856  in
          FStar_Pprint.group uu____5854
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5859;_},e1::e2::[])
          ->
          let uu____5864 =
            let uu____5865 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5866 =
              let uu____5867 =
                let uu____5868 = p_term false false e2  in
                soft_brackets_with_nesting uu____5868  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5867  in
            FStar_Pprint.op_Hat_Hat uu____5865 uu____5866  in
          FStar_Pprint.group uu____5864
      | uu____5869 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5874 = p_quident lid  in
        let uu____5875 =
          let uu____5876 =
            let uu____5877 = p_term false false e1  in
            soft_parens_with_nesting uu____5877  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5876  in
        FStar_Pprint.op_Hat_Hat uu____5874 uu____5875
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5883 =
          let uu____5884 = FStar_Ident.text_of_id op  in str uu____5884  in
        let uu____5885 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5883 uu____5885
    | uu____5886 -> p_atomicTermNotQUident e

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
         | uu____5894 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5901 =
          let uu____5902 = FStar_Ident.text_of_id op  in str uu____5902  in
        let uu____5903 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5901 uu____5903
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5907 =
          let uu____5908 =
            let uu____5909 =
              let uu____5910 = FStar_Ident.text_of_id op  in str uu____5910
               in
            let uu____5911 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5909 uu____5911  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5908  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5907
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5926 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5927 =
          let uu____5928 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5929 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5928 p_tmEq uu____5929  in
        let uu____5936 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5926 uu____5927 uu____5936
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5939 =
          let uu____5940 = p_atomicTermNotQUident e1  in
          let uu____5941 =
            let uu____5942 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5942  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5940 uu____5941
           in
        FStar_Pprint.group uu____5939
    | uu____5943 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5948 = p_quident constr_lid  in
        let uu____5949 =
          let uu____5950 =
            let uu____5951 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5951  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5950  in
        FStar_Pprint.op_Hat_Hat uu____5948 uu____5949
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5953 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5953 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5955 = p_term false false e1  in
        soft_parens_with_nesting uu____5955
    | uu____5956 when is_array e ->
        let es = extract_from_list e  in
        let uu____5960 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5961 =
          let uu____5962 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____5962
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____5965 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5960 uu____5961 uu____5965
    | uu____5966 when is_list e ->
        let uu____5967 =
          let uu____5968 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5969 = extract_from_list e  in
          separate_map_or_flow_last uu____5968
            (fun ps  -> p_noSeqTerm ps false) uu____5969
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5967 FStar_Pprint.rbracket
    | uu____5974 when is_lex_list e ->
        let uu____5975 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5976 =
          let uu____5977 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5978 = extract_from_list e  in
          separate_map_or_flow_last uu____5977
            (fun ps  -> p_noSeqTerm ps false) uu____5978
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5975 uu____5976 FStar_Pprint.rbracket
    | uu____5983 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5987 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5988 =
          let uu____5989 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5989 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5987 uu____5988 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5993 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5994 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5993 uu____5994
    | FStar_Parser_AST.Op (op,args) when
        let uu____6001 = handleable_op op args  in
        Prims.op_Negation uu____6001 ->
        let uu____6002 =
          let uu____6003 =
            let uu____6004 = FStar_Ident.text_of_id op  in
            let uu____6005 =
              let uu____6006 =
                let uu____6007 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6007
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6006  in
            Prims.strcat uu____6004 uu____6005  in
          Prims.strcat "Operation " uu____6003  in
        failwith uu____6002
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6009 = str "u#"  in
        let uu____6010 = str id1.FStar_Ident.idText  in
        FStar_Pprint.op_Hat_Hat uu____6009 uu____6010
    | FStar_Parser_AST.Wild  ->
        let uu____6011 = p_term false false e  in
        soft_parens_with_nesting uu____6011
    | FStar_Parser_AST.Const uu____6012 ->
        let uu____6013 = p_term false false e  in
        soft_parens_with_nesting uu____6013
    | FStar_Parser_AST.Op uu____6014 ->
        let uu____6021 = p_term false false e  in
        soft_parens_with_nesting uu____6021
    | FStar_Parser_AST.Tvar uu____6022 ->
        let uu____6023 = p_term false false e  in
        soft_parens_with_nesting uu____6023
    | FStar_Parser_AST.Var uu____6024 ->
        let uu____6025 = p_term false false e  in
        soft_parens_with_nesting uu____6025
    | FStar_Parser_AST.Name uu____6026 ->
        let uu____6027 = p_term false false e  in
        soft_parens_with_nesting uu____6027
    | FStar_Parser_AST.Construct uu____6028 ->
        let uu____6039 = p_term false false e  in
        soft_parens_with_nesting uu____6039
    | FStar_Parser_AST.Abs uu____6040 ->
        let uu____6047 = p_term false false e  in
        soft_parens_with_nesting uu____6047
    | FStar_Parser_AST.App uu____6048 ->
        let uu____6055 = p_term false false e  in
        soft_parens_with_nesting uu____6055
    | FStar_Parser_AST.Let uu____6056 ->
        let uu____6077 = p_term false false e  in
        soft_parens_with_nesting uu____6077
    | FStar_Parser_AST.LetOpen uu____6078 ->
        let uu____6083 = p_term false false e  in
        soft_parens_with_nesting uu____6083
    | FStar_Parser_AST.Seq uu____6084 ->
        let uu____6089 = p_term false false e  in
        soft_parens_with_nesting uu____6089
    | FStar_Parser_AST.Bind uu____6090 ->
        let uu____6097 = p_term false false e  in
        soft_parens_with_nesting uu____6097
    | FStar_Parser_AST.If uu____6098 ->
        let uu____6105 = p_term false false e  in
        soft_parens_with_nesting uu____6105
    | FStar_Parser_AST.Match uu____6106 ->
        let uu____6121 = p_term false false e  in
        soft_parens_with_nesting uu____6121
    | FStar_Parser_AST.TryWith uu____6122 ->
        let uu____6137 = p_term false false e  in
        soft_parens_with_nesting uu____6137
    | FStar_Parser_AST.Ascribed uu____6138 ->
        let uu____6147 = p_term false false e  in
        soft_parens_with_nesting uu____6147
    | FStar_Parser_AST.Record uu____6148 ->
        let uu____6161 = p_term false false e  in
        soft_parens_with_nesting uu____6161
    | FStar_Parser_AST.Project uu____6162 ->
        let uu____6167 = p_term false false e  in
        soft_parens_with_nesting uu____6167
    | FStar_Parser_AST.Product uu____6168 ->
        let uu____6175 = p_term false false e  in
        soft_parens_with_nesting uu____6175
    | FStar_Parser_AST.Sum uu____6176 ->
        let uu____6183 = p_term false false e  in
        soft_parens_with_nesting uu____6183
    | FStar_Parser_AST.QForall uu____6184 ->
        let uu____6197 = p_term false false e  in
        soft_parens_with_nesting uu____6197
    | FStar_Parser_AST.QExists uu____6198 ->
        let uu____6211 = p_term false false e  in
        soft_parens_with_nesting uu____6211
    | FStar_Parser_AST.Refine uu____6212 ->
        let uu____6217 = p_term false false e  in
        soft_parens_with_nesting uu____6217
    | FStar_Parser_AST.NamedTyp uu____6218 ->
        let uu____6223 = p_term false false e  in
        soft_parens_with_nesting uu____6223
    | FStar_Parser_AST.Requires uu____6224 ->
        let uu____6231 = p_term false false e  in
        soft_parens_with_nesting uu____6231
    | FStar_Parser_AST.Ensures uu____6232 ->
        let uu____6239 = p_term false false e  in
        soft_parens_with_nesting uu____6239
    | FStar_Parser_AST.Attributes uu____6240 ->
        let uu____6243 = p_term false false e  in
        soft_parens_with_nesting uu____6243
    | FStar_Parser_AST.Quote uu____6244 ->
        let uu____6249 = p_term false false e  in
        soft_parens_with_nesting uu____6249
    | FStar_Parser_AST.VQuote uu____6250 ->
        let uu____6251 = p_term false false e  in
        soft_parens_with_nesting uu____6251
    | FStar_Parser_AST.Antiquote uu____6252 ->
        let uu____6257 = p_term false false e  in
        soft_parens_with_nesting uu____6257

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___69_6258  ->
    match uu___69_6258 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6262 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6262
    | FStar_Const.Const_string (s,uu____6264) ->
        let uu____6265 = str s  in FStar_Pprint.dquotes uu____6265
    | FStar_Const.Const_bytearray (bytes,uu____6267) ->
        let uu____6272 =
          let uu____6273 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6273  in
        let uu____6274 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6272 uu____6274
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___67_6294 =
          match uu___67_6294 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___68_6300 =
          match uu___68_6300 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6311  ->
               match uu____6311 with
               | (s,w) ->
                   let uu____6318 = signedness s  in
                   let uu____6319 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6318 uu____6319)
            sign_width_opt
           in
        let uu____6320 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6320 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6322 = FStar_Range.string_of_range r  in str uu____6322
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6324 = p_quident lid  in
        let uu____6325 =
          let uu____6326 =
            let uu____6327 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6327  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6326  in
        FStar_Pprint.op_Hat_Hat uu____6324 uu____6325

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6329 = str "u#"  in
    let uu____6330 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6329 uu____6330

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6332;_},u1::u2::[])
        ->
        let uu____6337 =
          let uu____6338 = p_universeFrom u1  in
          let uu____6339 =
            let uu____6340 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6340  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6338 uu____6339  in
        FStar_Pprint.group uu____6337
    | FStar_Parser_AST.App uu____6341 ->
        let uu____6348 = head_and_args u  in
        (match uu____6348 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6374 =
                    let uu____6375 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6376 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6384  ->
                           match uu____6384 with
                           | (u1,uu____6390) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6375 uu____6376  in
                  FStar_Pprint.group uu____6374
              | uu____6391 ->
                  let uu____6392 =
                    let uu____6393 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6393
                     in
                  failwith uu____6392))
    | uu____6394 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6417 = FStar_Ident.text_of_id id1  in str uu____6417
    | FStar_Parser_AST.Paren u1 ->
        let uu____6419 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6419
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6420;_},uu____6421::uu____6422::[])
        ->
        let uu____6425 = p_universeFrom u  in
        soft_parens_with_nesting uu____6425
    | FStar_Parser_AST.App uu____6426 ->
        let uu____6433 = p_universeFrom u  in
        soft_parens_with_nesting uu____6433
    | uu____6434 ->
        let uu____6435 =
          let uu____6436 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6436
           in
        failwith uu____6435

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_term false false e 
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
       | FStar_Parser_AST.Module (uu____6492,decls) ->
           let uu____6498 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6498
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6507,decls,uu____6509) ->
           let uu____6514 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6514
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6571  ->
         match uu____6571 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6615,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6621,decls,uu____6623) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6672 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6685;
                 FStar_Parser_AST.doc = uu____6686;
                 FStar_Parser_AST.quals = uu____6687;
                 FStar_Parser_AST.attrs = uu____6688;_}::uu____6689 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6695 =
                   let uu____6698 =
                     let uu____6701 = FStar_List.tl ds  in d :: uu____6701
                      in
                   d0 :: uu____6698  in
                 (uu____6695, (d0.FStar_Parser_AST.drange))
             | uu____6706 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6672 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6770 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6770 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6878 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6878, comments1))))))
  