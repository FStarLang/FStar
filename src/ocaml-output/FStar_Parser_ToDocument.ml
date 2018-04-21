open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
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
  
let str : Prims.string -> FStar_Pprint.document =
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
  
let prefix2 :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  ->
    fun body  ->
      FStar_Pprint.prefix (Prims.lift_native_int (2))
        (Prims.lift_native_int (1)) prefix_ body
  
let op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let jump2 : FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.lift_native_int (2)) (Prims.lift_native_int (1))
      body
  
let infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  =
  FStar_Pprint.infix (Prims.lift_native_int (2)) (Prims.lift_native_int (1)) 
let infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  =
  FStar_Pprint.infix (Prims.lift_native_int (0)) (Prims.lift_native_int (1)) 
let break1 : FStar_Pprint.document =
  FStar_Pprint.break_ (Prims.lift_native_int (1)) 
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
  
let parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (0)) FStar_Pprint.lparen contents
      FStar_Pprint.rparen
  
let soft_parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (0)) FStar_Pprint.lparen contents
      FStar_Pprint.rparen
  
let braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (1)) FStar_Pprint.lbrace contents
      FStar_Pprint.rbrace
  
let soft_braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (1)) FStar_Pprint.lbrace contents
      FStar_Pprint.rbrace
  
let brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (1)) FStar_Pprint.lbracket contents
      FStar_Pprint.rbracket
  
let soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (1)) FStar_Pprint.lbracket contents
      FStar_Pprint.rbracket
  
let soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____366 = str "begin"  in
    let uu____367 = str "end"  in
    FStar_Pprint.soft_surround (Prims.lift_native_int (2))
      (Prims.lift_native_int (1)) uu____366 contents uu____367
  
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
            (fun i  -> fun e  -> f (i <> (l - (Prims.lift_native_int (1)))) e)
            es
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
        if (FStar_List.length l) < (Prims.lift_native_int (10))
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
            (fun i  -> fun e  -> f (i <> (l - (Prims.lift_native_int (1)))) e)
            es
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
        if (FStar_List.length l) < (Prims.lift_native_int (10))
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
  
let doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
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
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____812 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____824 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____824
      | uu____825 -> false
  
let is_tuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_tuple_data_lid' 
let is_dtuple_constructor : FStar_Ident.lident -> Prims.bool =
  FStar_Parser_Const.is_dtuple_data_lid' 
let is_list_structure :
  FStar_Ident.lident ->
    FStar_Ident.lident -> FStar_Parser_AST.term -> Prims.bool
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
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
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
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
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
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
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
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
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
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____1025 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1025
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____1031 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1031
  
let is_general_prefix_op : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      let uu____1038 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1038 (Prims.lift_native_int (0))  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1043 = FStar_Ident.text_of_id op  in uu____1043 <> "~"))
  
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      match e1.FStar_Parser_AST.tm with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____1109 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1125 -> false
  
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1131 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1137 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___54_1157  ->
    match uu___54_1157 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___55_1178  ->
      match uu___55_1178 with
      | FStar_Util.Inl c ->
          let uu____1187 = FStar_String.get s (Prims.lift_native_int (0))  in
          uu____1187 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1198 .
    Prims.string ->
      ('Auu____1198,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1219  ->
      match uu____1219 with
      | (assoc_levels,tokens) ->
          let uu____1247 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1247 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1274 .
    unit ->
      (associativity,('Auu____1274,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1285  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1302 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1302) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1314  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1350 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1350) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1362  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1391 .
    unit ->
      (associativity,('Auu____1391,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1402  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1419 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1419) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1431  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1460 .
    unit ->
      (associativity,('Auu____1460,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1471  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1488 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1488) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1500  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1522 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1522) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1534  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1570 .
    unit ->
      (associativity,('Auu____1570,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1581  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1598 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1598) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1610  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1632 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____1632) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1644  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1666 .
    unit ->
      (associativity,('Auu____1666,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1677  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1694 .
    unit ->
      (associativity,('Auu____1694,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1705  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1722 .
    unit ->
      (associativity,('Auu____1722,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1733  -> (Right, [FStar_Util.Inr "::"]) 
let level_associativity_spec :
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
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
let level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  let levels_from_associativity l uu___56_1944 =
    match uu___56_1944 with
    | Left  -> (l, l, (l - (Prims.lift_native_int (1))))
    | Right  -> ((l - (Prims.lift_native_int (1))), l, l)
    | NonAssoc  ->
        ((l - (Prims.lift_native_int (1))), l,
          (l - (Prims.lift_native_int (1))))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1984  ->
         match uu____1984 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2068 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2068 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2118) ->
          assoc_levels
      | uu____2162 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____2203 .
    ('Auu____2203,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2268 =
        FStar_List.tryFind
          (fun uu____2308  ->
             match uu____2308 with
             | (uu____2326,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2268 with
      | FStar_Pervasives_Native.Some ((uu____2368,l1,uu____2370),uu____2371)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2426 =
            let uu____2427 =
              let uu____2428 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2428  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2427
             in
          failwith uu____2426
       in
    FStar_List.fold_left find_level_and_max (Prims.lift_native_int (0)) l
  
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun op  ->
    let uu____2464 = assign_levels level_associativity_spec op  in
    match uu____2464 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.lift_native_int (1))), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2489 .
    unit ->
      (associativity,(FStar_Char.char,'Auu____2489) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2503  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2586 =
      let uu____2600 =
        let uu____2616 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2616  in
      FStar_List.tryFind uu____2600 (operatorInfix0ad12 ())  in
    uu____2586 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2719 =
      let uu____2733 =
        let uu____2749 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2749  in
      FStar_List.tryFind uu____2733 opinfix34  in
    uu____2719 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2805 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2805
    then (Prims.lift_native_int (1))
    else
      (let uu____2807 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2807
       then (Prims.lift_native_int (2))
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.lift_native_int (3))
         else (Prims.lift_native_int (0)))
  
let handleable_op :
  'Auu____2816 . FStar_Ident.ident -> 'Auu____2816 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.lift_native_int (0)) -> true
      | _0_5 when _0_5 = (Prims.lift_native_int (1)) ->
          (is_general_prefix_op op) ||
            (let uu____2832 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2832 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.lift_native_int (2)) ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2834 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2834
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.lift_native_int (3)) ->
          let uu____2835 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2835 [".()<-"; ".[]<-"]
      | uu____2836 -> false
  
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2874 .
    ('Auu____2874 -> FStar_Pprint.document) ->
      'Auu____2874 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2915 = FStar_ST.op_Bang comment_stack  in
          match uu____2915 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2978 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2978
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____3019 =
                    let uu____3020 =
                      let uu____3021 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____3021
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____3020  in
                  comments_before_pos uu____3019 print_pos lookahead_pos))
              else
                (let uu____3023 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3023))
           in
        let uu____3024 =
          let uu____3029 =
            let uu____3030 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3030  in
          let uu____3031 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3029 uu____3031  in
        match uu____3024 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3037 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3037
              else comments  in
            let uu____3043 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____3043
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____3064 = FStar_ST.op_Bang comment_stack  in
          match uu____3064 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____3156 =
                    let uu____3157 =
                      let uu____3158 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____3158  in
                    uu____3157 - lbegin  in
                  max k uu____3156  in
                let doc2 =
                  let uu____3160 =
                    let uu____3161 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____3162 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____3161 uu____3162  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____3160  in
                let uu____3163 =
                  let uu____3164 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____3164  in
                place_comments_until_pos (Prims.lift_native_int (1))
                  uu____3163 pos_end doc2))
          | uu____3165 ->
              let lnum =
                let uu____3173 =
                  let uu____3174 = FStar_Range.line_of_pos pos_end  in
                  uu____3174 - lbegin  in
                max (Prims.lift_native_int (1)) uu____3173  in
              let uu____3175 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____3175
  
let separate_map_with_comments :
  'Auu____3188 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3188 -> FStar_Pprint.document) ->
          'Auu____3188 Prims.list ->
            ('Auu____3188 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3245 x =
              match uu____3245 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3259 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.lift_native_int (1))
                      last_line uu____3259 doc1
                     in
                  let uu____3260 =
                    let uu____3261 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3261  in
                  let uu____3262 =
                    let uu____3263 =
                      let uu____3264 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3264  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3263  in
                  (uu____3260, uu____3262)
               in
            let uu____3265 =
              let uu____3272 = FStar_List.hd xs  in
              let uu____3273 = FStar_List.tl xs  in (uu____3272, uu____3273)
               in
            match uu____3265 with
            | (x,xs1) ->
                let init1 =
                  let uu____3289 =
                    let uu____3290 =
                      let uu____3291 = extract_range x  in
                      FStar_Range.end_of_range uu____3291  in
                    FStar_Range.line_of_pos uu____3290  in
                  let uu____3292 =
                    let uu____3293 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3293  in
                  (uu____3289, uu____3292)  in
                let uu____3294 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3294
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3923 =
      let uu____3924 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3925 =
        let uu____3926 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3927 =
          let uu____3928 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3929 =
            let uu____3930 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3930
             in
          FStar_Pprint.op_Hat_Hat uu____3928 uu____3929  in
        FStar_Pprint.op_Hat_Hat uu____3926 uu____3927  in
      FStar_Pprint.op_Hat_Hat uu____3924 uu____3925  in
    FStar_Pprint.group uu____3923

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3933 =
      let uu____3934 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3934  in
    let uu____3935 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.lift_native_int (0))
      (Prims.lift_native_int (2)) FStar_Pprint.empty uu____3933
      FStar_Pprint.space uu____3935 p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3936  ->
    match uu____3936 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3972 =
                match uu____3972 with
                | (kwd,arg) ->
                    let uu____3979 = str "@"  in
                    let uu____3980 =
                      let uu____3981 = str kwd  in
                      let uu____3982 =
                        let uu____3983 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3983
                         in
                      FStar_Pprint.op_Hat_Hat uu____3981 uu____3982  in
                    FStar_Pprint.op_Hat_Hat uu____3979 uu____3980
                 in
              let uu____3984 =
                let uu____3985 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3985 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3984
           in
        let uu____3990 =
          let uu____3991 =
            let uu____3992 =
              let uu____3993 =
                let uu____3994 = str doc1  in
                let uu____3995 =
                  let uu____3996 =
                    let uu____3997 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3997  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3996  in
                FStar_Pprint.op_Hat_Hat uu____3994 uu____3995  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3993  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3992  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3991  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3990

and p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4001 =
          let uu____4002 = str "val"  in
          let uu____4003 =
            let uu____4004 =
              let uu____4005 = p_lident lid  in
              let uu____4006 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4005 uu____4006  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4004  in
          FStar_Pprint.op_Hat_Hat uu____4002 uu____4003  in
        let uu____4007 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4001 uu____4007
    | FStar_Parser_AST.TopLevelLet (uu____4008,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4033 =
               let uu____4034 = str "let"  in
               let uu____4035 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4034 uu____4035  in
             FStar_Pprint.group uu____4033) lbs
    | uu____4036 -> FStar_Pprint.empty

and p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___57_4051 =
          match uu___57_4051 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4059 = f x  in
              let uu____4060 =
                let uu____4061 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4061  in
              FStar_Pprint.op_Hat_Hat uu____4059 uu____4060
           in
        let uu____4062 = str "["  in
        let uu____4063 =
          let uu____4064 = p_list' l  in
          let uu____4065 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4064 uu____4065  in
        FStar_Pprint.op_Hat_Hat uu____4062 uu____4063

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4068 =
          let uu____4069 = str "open"  in
          let uu____4070 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4069 uu____4070  in
        FStar_Pprint.group uu____4068
    | FStar_Parser_AST.Include uid ->
        let uu____4072 =
          let uu____4073 = str "include"  in
          let uu____4074 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4073 uu____4074  in
        FStar_Pprint.group uu____4072
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4077 =
          let uu____4078 = str "module"  in
          let uu____4079 =
            let uu____4080 =
              let uu____4081 = p_uident uid1  in
              let uu____4082 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4081 uu____4082  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4080  in
          FStar_Pprint.op_Hat_Hat uu____4078 uu____4079  in
        let uu____4083 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4077 uu____4083
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4085 =
          let uu____4086 = str "module"  in
          let uu____4087 =
            let uu____4088 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4088  in
          FStar_Pprint.op_Hat_Hat uu____4086 uu____4087  in
        FStar_Pprint.group uu____4085
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____4121 = str "effect"  in
          let uu____4122 =
            let uu____4123 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4123  in
          FStar_Pprint.op_Hat_Hat uu____4121 uu____4122  in
        let uu____4124 =
          let uu____4125 = p_typars tpars  in
          FStar_Pprint.surround (Prims.lift_native_int (2))
            (Prims.lift_native_int (1)) effect_prefix_doc uu____4125
            FStar_Pprint.equals
           in
        let uu____4126 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4124 uu____4126
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____4144 = str "type"  in
        let uu____4145 = str "and"  in
        precede_break_separate_map uu____4144 uu____4145 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4167 = str "let"  in
          let uu____4168 =
            let uu____4169 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____4169 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____4167 uu____4168  in
        let uu____4170 =
          let uu____4171 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____4171 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____4170 p_letbinding lbs
          (fun uu____4179  ->
             match uu____4179 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4188 =
          let uu____4189 = str "val"  in
          let uu____4190 =
            let uu____4191 =
              let uu____4192 = p_lident lid  in
              let uu____4193 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4192 uu____4193  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4191  in
          FStar_Pprint.op_Hat_Hat uu____4189 uu____4190  in
        let uu____4194 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4188 uu____4194
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4198 =
            let uu____4199 =
              FStar_Util.char_at id1.FStar_Ident.idText
                (Prims.lift_native_int (0))
               in
            FStar_All.pipe_right uu____4199 FStar_Util.is_upper  in
          if uu____4198
          then FStar_Pprint.empty
          else
            (let uu____4201 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4201 FStar_Pprint.space)
           in
        let uu____4202 =
          let uu____4203 =
            let uu____4204 = p_ident id1  in
            let uu____4205 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____4204 uu____4205  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____4203  in
        let uu____4206 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4202 uu____4206
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4213 = str "exception"  in
        let uu____4214 =
          let uu____4215 =
            let uu____4216 = p_uident uid  in
            let uu____4217 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4221 =
                     let uu____4222 = str "of"  in
                     let uu____4223 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4222 uu____4223  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4221) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4216 uu____4217  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4215  in
        FStar_Pprint.op_Hat_Hat uu____4213 uu____4214
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4225 = str "new_effect"  in
        let uu____4226 =
          let uu____4227 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4227  in
        FStar_Pprint.op_Hat_Hat uu____4225 uu____4226
    | FStar_Parser_AST.SubEffect se ->
        let uu____4229 = str "sub_effect"  in
        let uu____4230 =
          let uu____4231 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4231  in
        FStar_Pprint.op_Hat_Hat uu____4229 uu____4230
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4234 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4234 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4235 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4236) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4259 = str "%splice"  in
        let uu____4260 =
          let uu____4261 =
            let uu____4262 = str ";"  in p_list p_uident uu____4262 ids  in
          let uu____4263 =
            let uu____4264 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4264  in
          FStar_Pprint.op_Hat_Hat uu____4261 uu____4263  in
        FStar_Pprint.op_Hat_Hat uu____4259 uu____4260

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___58_4265  ->
    match uu___58_4265 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4267 = str "#set-options"  in
        let uu____4268 =
          let uu____4269 =
            let uu____4270 = str s  in FStar_Pprint.dquotes uu____4270  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4269  in
        FStar_Pprint.op_Hat_Hat uu____4267 uu____4268
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4274 = str "#reset-options"  in
        let uu____4275 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4279 =
                 let uu____4280 = str s  in FStar_Pprint.dquotes uu____4280
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4279) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4274 uu____4275
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4308  ->
    match uu____4308 with
    | (typedecl,fsdoc_opt) ->
        let uu____4321 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____4322 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____4321 uu____4322

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___59_4323  ->
    match uu___59_4323 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____4340 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____4358 =
          let uu____4359 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____4359  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____4410 =
          match uu____4410 with
          | (lid1,t,doc_opt) ->
              let uu____4426 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____4426
           in
        let p_fields uu____4442 =
          let uu____4443 =
            let uu____4444 =
              let uu____4445 =
                let uu____4446 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4446 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4445  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4444  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4443  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____4512 =
          match uu____4512 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____4538 =
                  let uu____4539 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____4539  in
                FStar_Range.extend_to_end_of_line uu____4538  in
              let p_constructorBranch decl =
                let uu____4574 =
                  let uu____4575 =
                    let uu____4576 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4576  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4575  in
                FStar_Pprint.group uu____4574  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____4598 =
          let uu____4599 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____4599  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4614  ->
             let uu____4615 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____4615)

and p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____4630 = p_ident lid  in
            let uu____4631 =
              let uu____4632 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4632  in
            FStar_Pprint.op_Hat_Hat uu____4630 uu____4631
          else
            (let binders_doc =
               let uu____4635 = p_typars bs  in
               let uu____4636 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4640 =
                        let uu____4641 =
                          let uu____4642 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4642
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4641
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____4640) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____4635 uu____4636  in
             let uu____4643 = p_ident lid  in
             let uu____4644 = cont ()  in
             FStar_Pprint.surround (Prims.lift_native_int (2))
               (Prims.lift_native_int (1)) uu____4643 binders_doc uu____4644)

and p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun ps  ->
    fun uu____4646  ->
      match uu____4646 with
      | (lid,t,doc_opt) ->
          let uu____4662 =
            let uu____4663 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4664 =
              let uu____4665 = p_lident lid  in
              let uu____4666 =
                let uu____4667 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4667  in
              FStar_Pprint.op_Hat_Hat uu____4665 uu____4666  in
            FStar_Pprint.op_Hat_Hat uu____4663 uu____4664  in
          FStar_Pprint.group uu____4662

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____4668  ->
    match uu____4668 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4696 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4697 =
          let uu____4698 = FStar_Pprint.break_ (Prims.lift_native_int (0))
             in
          let uu____4699 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4704 =
                   let uu____4705 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4705  in
                 let uu____4706 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4704 uu____4706) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4698 uu____4699  in
        FStar_Pprint.op_Hat_Hat uu____4696 uu____4697

and p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4707  ->
    match uu____4707 with
    | (pat,uu____4713) ->
        let uu____4714 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4733 =
                let uu____4734 =
                  let uu____4735 =
                    let uu____4736 =
                      let uu____4737 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4737
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4736  in
                  FStar_Pprint.group uu____4735  in
                FStar_Pprint.op_Hat_Hat break1 uu____4734  in
              (pat1, uu____4733)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4749 =
                let uu____4750 =
                  let uu____4751 =
                    let uu____4752 =
                      let uu____4753 =
                        let uu____4754 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4754
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4753
                       in
                    FStar_Pprint.group uu____4752  in
                  let uu____4755 =
                    let uu____4756 =
                      let uu____4757 = str "by"  in
                      let uu____4758 =
                        let uu____4759 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4759
                         in
                      FStar_Pprint.op_Hat_Hat uu____4757 uu____4758  in
                    FStar_Pprint.group uu____4756  in
                  FStar_Pprint.op_Hat_Hat uu____4751 uu____4755  in
                FStar_Pprint.op_Hat_Hat break1 uu____4750  in
              (pat1, uu____4749)
          | uu____4760 -> (pat, FStar_Pprint.empty)  in
        (match uu____4714 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4764);
                     FStar_Parser_AST.prange = uu____4765;_},pats)
                  ->
                  let uu____4775 =
                    let uu____4776 = p_lident x  in
                    let uu____4777 =
                      let uu____4778 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4778 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4776 uu____4777  in
                  FStar_Pprint.group uu____4775
              | uu____4779 ->
                  let uu____4780 =
                    let uu____4781 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4781 ascr_doc  in
                  FStar_Pprint.group uu____4780))

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4782  ->
    match uu____4782 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4790 =
          let uu____4791 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4791  in
        let uu____4792 = p_term false false e  in
        prefix2 uu____4790 uu____4792

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___60_4793  ->
    match uu___60_4793 with
    | FStar_Parser_AST.RedefineEffect (lid,bs,t) ->
        p_effectRedefinition lid bs t
    | FStar_Parser_AST.DefineEffect (lid,bs,t,eff_decls) ->
        p_effectDefinition lid bs t eff_decls

and p_effectRedefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        let uu____4818 = p_uident uid  in
        let uu____4819 = p_binders true bs  in
        let uu____4820 =
          let uu____4821 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4821  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (1)) uu____4818 uu____4819 uu____4820

and p_effectDefinition :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.term ->
        FStar_Parser_AST.decl Prims.list -> FStar_Pprint.document
  =
  fun uid  ->
    fun bs  ->
      fun t  ->
        fun eff_decls  ->
          let uu____4830 =
            let uu____4831 =
              let uu____4832 =
                let uu____4833 = p_uident uid  in
                let uu____4834 = p_binders true bs  in
                let uu____4835 =
                  let uu____4836 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4836  in
                FStar_Pprint.surround (Prims.lift_native_int (2))
                  (Prims.lift_native_int (1)) uu____4833 uu____4834
                  uu____4835
                 in
              FStar_Pprint.group uu____4832  in
            let uu____4837 =
              let uu____4838 = str "with"  in
              let uu____4839 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4838 uu____4839  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4831 uu____4837  in
          braces_with_nesting uu____4830

and p_effectDecl :
  Prims.bool -> FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun ps  ->
    fun d  ->
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Tycon
          (false
           ,(FStar_Parser_AST.TyconAbbrev
             (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
             )::[])
          ->
          let uu____4870 =
            let uu____4871 = p_lident lid  in
            let uu____4872 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4871 uu____4872  in
          let uu____4873 = p_simpleTerm ps false e  in
          prefix2 uu____4870 uu____4873
      | uu____4874 ->
          let uu____4875 =
            let uu____4876 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4876
             in
          failwith uu____4875

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4938 =
        match uu____4938 with
        | (kwd,t) ->
            let uu____4945 =
              let uu____4946 = str kwd  in
              let uu____4947 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4946 uu____4947  in
            let uu____4948 = p_simpleTerm ps false t  in
            prefix2 uu____4945 uu____4948
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4953 =
      let uu____4954 =
        let uu____4955 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4956 =
          let uu____4957 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4957  in
        FStar_Pprint.op_Hat_Hat uu____4955 uu____4956  in
      let uu____4958 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4954 uu____4958  in
    let uu____4959 =
      let uu____4960 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4960  in
    FStar_Pprint.op_Hat_Hat uu____4953 uu____4959

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___61_4961  ->
    match uu___61_4961 with
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

and p_qualifiers : FStar_Parser_AST.qualifiers -> FStar_Pprint.document =
  fun qs  ->
    let uu____4963 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4963

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___62_4964  ->
    match uu___62_4964 with
    | FStar_Parser_AST.Rec  ->
        let uu____4965 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4965
    | FStar_Parser_AST.Mutable  ->
        let uu____4966 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4966
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___63_4967  ->
    match uu___63_4967 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4972 =
          let uu____4973 =
            let uu____4974 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4974  in
          FStar_Pprint.separate_map uu____4973 p_tuplePattern pats  in
        FStar_Pprint.group uu____4972
    | uu____4975 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4982 =
          let uu____4983 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4983 p_constructorPattern pats  in
        FStar_Pprint.group uu____4982
    | uu____4984 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4987;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4992 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4993 = p_constructorPattern hd1  in
        let uu____4994 = p_constructorPattern tl1  in
        infix0 uu____4992 uu____4993 uu____4994
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4996;_},pats)
        ->
        let uu____5002 = p_quident uid  in
        let uu____5003 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____5002 uu____5003
    | uu____5004 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____5020;
               FStar_Parser_AST.blevel = uu____5021;
               FStar_Parser_AST.aqual = uu____5022;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5028 =
               let uu____5029 = p_ident lid  in
               p_refinement aqual uu____5029 t1 phi  in
             soft_parens_with_nesting uu____5028
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5031;
               FStar_Parser_AST.blevel = uu____5032;
               FStar_Parser_AST.aqual = uu____5033;_},phi))
             ->
             let uu____5035 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____5035
         | uu____5036 ->
             let uu____5041 =
               let uu____5042 = p_tuplePattern pat  in
               let uu____5043 =
                 let uu____5044 =
                   FStar_Pprint.break_ (Prims.lift_native_int (0))  in
                 let uu____5045 =
                   let uu____5046 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5046  in
                 FStar_Pprint.op_Hat_Hat uu____5044 uu____5045  in
               FStar_Pprint.op_Hat_Hat uu____5042 uu____5043  in
             soft_parens_with_nesting uu____5041)
    | FStar_Parser_AST.PatList pats ->
        let uu____5050 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (0)) FStar_Pprint.lbracket uu____5050
          FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5067 =
          match uu____5067 with
          | (lid,pat) ->
              let uu____5074 = p_qlident lid  in
              let uu____5075 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5074 uu____5075
           in
        let uu____5076 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5076
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5086 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5087 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5088 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (1)) uu____5086 uu____5087 uu____5088
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5097 =
          let uu____5098 =
            let uu____5099 =
              let uu____5100 = FStar_Ident.text_of_id op  in str uu____5100
               in
            let uu____5101 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5099 uu____5101  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5098  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5097
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5109 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5110 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5109 uu____5110
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5112 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5115;
           FStar_Parser_AST.prange = uu____5116;_},uu____5117)
        ->
        let uu____5122 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5122
    | FStar_Parser_AST.PatTuple (uu____5123,false ) ->
        let uu____5128 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5128
    | uu____5129 ->
        let uu____5130 =
          let uu____5131 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5131  in
        failwith uu____5130

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5135 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5136 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5135 uu____5136
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5143;
                   FStar_Parser_AST.blevel = uu____5144;
                   FStar_Parser_AST.aqual = uu____5145;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5147 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5147 t1 phi
            | uu____5148 ->
                let uu____5149 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5150 =
                  let uu____5151 = p_lident lid  in
                  let uu____5152 =
                    let uu____5153 =
                      let uu____5154 =
                        FStar_Pprint.break_ (Prims.lift_native_int (0))  in
                      let uu____5155 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____5154 uu____5155  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5153  in
                  FStar_Pprint.op_Hat_Hat uu____5151 uu____5152  in
                FStar_Pprint.op_Hat_Hat uu____5149 uu____5150
             in
          if is_atomic
          then
            let uu____5156 =
              let uu____5157 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5157  in
            FStar_Pprint.group uu____5156
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5159 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5166;
                  FStar_Parser_AST.blevel = uu____5167;
                  FStar_Parser_AST.aqual = uu____5168;_},phi)
               ->
               if is_atomic
               then
                 let uu____5170 =
                   let uu____5171 =
                     let uu____5172 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5172 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5171  in
                 FStar_Pprint.group uu____5170
               else
                 (let uu____5174 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5174)
           | uu____5175 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____5183 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____5184 =
            let uu____5185 =
              let uu____5186 =
                let uu____5187 = p_appTerm t  in
                let uu____5188 =
                  let uu____5189 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____5189  in
                FStar_Pprint.op_Hat_Hat uu____5187 uu____5188  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5186  in
            FStar_Pprint.op_Hat_Hat binder uu____5185  in
          FStar_Pprint.op_Hat_Hat uu____5183 uu____5184

and p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and p_qlident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> let uu____5195 = FStar_Ident.text_of_lid lid  in str uu____5195

and p_quident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> let uu____5197 = FStar_Ident.text_of_lid lid  in str uu____5197

and p_ident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> let uu____5199 = FStar_Ident.text_of_id lid  in str uu____5199

and p_lident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> let uu____5201 = FStar_Ident.text_of_id lid  in str uu____5201

and p_uident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> let uu____5203 = FStar_Ident.text_of_id lid  in str uu____5203

and p_tvar : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> let uu____5205 = FStar_Ident.text_of_id lid  in str uu____5205

and p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document =
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1

and paren_if : Prims.bool -> FStar_Pprint.document -> FStar_Pprint.document =
  fun b  -> if b then soft_parens_with_nesting else (fun x  -> x)

and p_term :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Seq (e1,e2) ->
            let uu____5219 =
              let uu____5220 =
                let uu____5221 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5221 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5220  in
            let uu____5222 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5219 uu____5222
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5226 =
              let uu____5227 =
                let uu____5228 =
                  let uu____5229 = p_lident x  in
                  let uu____5230 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5229 uu____5230  in
                let uu____5231 =
                  let uu____5232 = p_noSeqTerm true false e1  in
                  let uu____5233 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5232 uu____5233  in
                op_Hat_Slash_Plus_Hat uu____5228 uu____5231  in
              FStar_Pprint.group uu____5227  in
            let uu____5234 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5226 uu____5234
        | uu____5235 ->
            let uu____5236 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5236

and p_noSeqTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_noSeqTerm' ps pb) e e.FStar_Parser_AST.range

and p_noSeqTerm' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
            let uu____5247 =
              let uu____5248 = p_tmIff e1  in
              let uu____5249 =
                let uu____5250 =
                  let uu____5251 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5251
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5250  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5248 uu____5249  in
            FStar_Pprint.group uu____5247
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5257 =
              let uu____5258 = p_tmIff e1  in
              let uu____5259 =
                let uu____5260 =
                  let uu____5261 =
                    let uu____5262 = p_typ false false t  in
                    let uu____5263 =
                      let uu____5264 = str "by"  in
                      let uu____5265 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5264 uu____5265  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5262 uu____5263  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5261
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5260  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5258 uu____5259  in
            FStar_Pprint.group uu____5257
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5266;_},e1::e2::e3::[])
            ->
            let uu____5272 =
              let uu____5273 =
                let uu____5274 =
                  let uu____5275 = p_atomicTermNotQUident e1  in
                  let uu____5276 =
                    let uu____5277 =
                      let uu____5278 =
                        let uu____5279 = p_term false false e2  in
                        soft_parens_with_nesting uu____5279  in
                      let uu____5280 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5278 uu____5280  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5277  in
                  FStar_Pprint.op_Hat_Hat uu____5275 uu____5276  in
                FStar_Pprint.group uu____5274  in
              let uu____5281 =
                let uu____5282 = p_noSeqTerm ps pb e3  in jump2 uu____5282
                 in
              FStar_Pprint.op_Hat_Hat uu____5273 uu____5281  in
            FStar_Pprint.group uu____5272
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5283;_},e1::e2::e3::[])
            ->
            let uu____5289 =
              let uu____5290 =
                let uu____5291 =
                  let uu____5292 = p_atomicTermNotQUident e1  in
                  let uu____5293 =
                    let uu____5294 =
                      let uu____5295 =
                        let uu____5296 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5296  in
                      let uu____5297 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5295 uu____5297  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5294  in
                  FStar_Pprint.op_Hat_Hat uu____5292 uu____5293  in
                FStar_Pprint.group uu____5291  in
              let uu____5298 =
                let uu____5299 = p_noSeqTerm ps pb e3  in jump2 uu____5299
                 in
              FStar_Pprint.op_Hat_Hat uu____5290 uu____5298  in
            FStar_Pprint.group uu____5289
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5307 =
              let uu____5308 = str "requires"  in
              let uu____5309 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5308 uu____5309  in
            FStar_Pprint.group uu____5307
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5317 =
              let uu____5318 = str "ensures"  in
              let uu____5319 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5318 uu____5319  in
            FStar_Pprint.group uu____5317
        | FStar_Parser_AST.Attributes es ->
            let uu____5323 =
              let uu____5324 = str "attributes"  in
              let uu____5325 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5324 uu____5325  in
            FStar_Pprint.group uu____5323
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5329 =
                let uu____5330 =
                  let uu____5331 = str "if"  in
                  let uu____5332 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5331 uu____5332  in
                let uu____5333 =
                  let uu____5334 = str "then"  in
                  let uu____5335 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5334 uu____5335  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5330 uu____5333  in
              FStar_Pprint.group uu____5329
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5338,uu____5339,e31) when
                     is_unit e31 ->
                     let uu____5341 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5341
                 | uu____5342 -> p_noSeqTerm false false e2  in
               let uu____5343 =
                 let uu____5344 =
                   let uu____5345 = str "if"  in
                   let uu____5346 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5345 uu____5346  in
                 let uu____5347 =
                   let uu____5348 =
                     let uu____5349 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5349 e2_doc  in
                   let uu____5350 =
                     let uu____5351 = str "else"  in
                     let uu____5352 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5351 uu____5352  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5348 uu____5350  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5344 uu____5347  in
               FStar_Pprint.group uu____5343)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5375 =
              let uu____5376 =
                let uu____5377 =
                  let uu____5378 = str "try"  in
                  let uu____5379 = p_noSeqTerm false false e1  in
                  prefix2 uu____5378 uu____5379  in
                let uu____5380 =
                  let uu____5381 = str "with"  in
                  let uu____5382 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5381 uu____5382  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5377 uu____5380  in
              FStar_Pprint.group uu____5376  in
            let uu____5391 = paren_if (ps || pb)  in uu____5391 uu____5375
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5418 =
              let uu____5419 =
                let uu____5420 =
                  let uu____5421 = str "match"  in
                  let uu____5422 = p_noSeqTerm false false e1  in
                  let uu____5423 = str "with"  in
                  FStar_Pprint.surround (Prims.lift_native_int (2))
                    (Prims.lift_native_int (1)) uu____5421 uu____5422
                    uu____5423
                   in
                let uu____5424 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5420 uu____5424  in
              FStar_Pprint.group uu____5419  in
            let uu____5433 = paren_if (ps || pb)  in uu____5433 uu____5418
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5440 =
              let uu____5441 =
                let uu____5442 =
                  let uu____5443 = str "let open"  in
                  let uu____5444 = p_quident uid  in
                  let uu____5445 = str "in"  in
                  FStar_Pprint.surround (Prims.lift_native_int (2))
                    (Prims.lift_native_int (1)) uu____5443 uu____5444
                    uu____5445
                   in
                let uu____5446 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5442 uu____5446  in
              FStar_Pprint.group uu____5441  in
            let uu____5447 = paren_if ps  in uu____5447 uu____5440
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5511 is_last =
              match uu____5511 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5544 =
                          let uu____5545 = str "let"  in
                          let uu____5546 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5545 uu____5546
                           in
                        FStar_Pprint.group uu____5544
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5547 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5552 =
                    if is_last
                    then
                      let uu____5553 =
                        let uu____5554 =
                          FStar_Pprint.surround (Prims.lift_native_int (2))
                            (Prims.lift_native_int (1)) doc_let_or_and
                            doc_pat FStar_Pprint.equals
                           in
                        let uu____5555 = str "in"  in
                        FStar_Pprint.surround (Prims.lift_native_int (2))
                          (Prims.lift_native_int (1)) uu____5554 doc_expr
                          uu____5555
                         in
                      FStar_Pprint.group uu____5553
                    else
                      (let uu____5557 =
                         let uu____5558 =
                           FStar_Pprint.surround (Prims.lift_native_int (2))
                             (Prims.lift_native_int (1)) doc_let_or_and
                             doc_pat FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.lift_native_int (2))
                           (Prims.lift_native_int (1)) uu____5558 doc_expr
                          in
                       FStar_Pprint.group uu____5557)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5552
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.lift_native_int (0))
                     then
                       let uu____5604 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.lift_native_int (1))))
                          in
                       FStar_Pprint.group uu____5604
                     else
                       (let uu____5612 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.lift_native_int (1))))
                           in
                        FStar_Pprint.group uu____5612)) lbs
               in
            let lbs_doc =
              let uu____5620 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5620  in
            let uu____5621 =
              let uu____5622 =
                let uu____5623 =
                  let uu____5624 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5624
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5623  in
              FStar_Pprint.group uu____5622  in
            let uu____5625 = paren_if ps  in uu____5625 uu____5621
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5632;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5635;
                                                             FStar_Parser_AST.level
                                                               = uu____5636;_})
            when matches_var maybe_x x ->
            let uu____5663 =
              let uu____5664 =
                let uu____5665 = str "function"  in
                let uu____5666 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5665 uu____5666  in
              FStar_Pprint.group uu____5664  in
            let uu____5675 = paren_if (ps || pb)  in uu____5675 uu____5663
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5681 =
              let uu____5682 = str "quote"  in
              let uu____5683 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5682 uu____5683  in
            FStar_Pprint.group uu____5681
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5685 =
              let uu____5686 = str "`"  in
              let uu____5687 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5686 uu____5687  in
            FStar_Pprint.group uu____5685
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5689 =
              let uu____5690 = str "%`"  in
              let uu____5691 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5690 uu____5691  in
            FStar_Pprint.group uu____5689
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5693 =
              let uu____5694 = str "`#"  in
              let uu____5695 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5694 uu____5695  in
            FStar_Pprint.group uu____5693
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5697 =
              let uu____5698 = str "`@"  in
              let uu____5699 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5698 uu____5699  in
            FStar_Pprint.group uu____5697
        | uu____5700 -> p_typ ps pb e

and p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___64_5701  ->
    match uu___64_5701 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5713 =
          let uu____5714 =
            let uu____5715 = str "[@"  in
            let uu____5716 =
              let uu____5717 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5718 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5717 uu____5718  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5715 uu____5716  in
          FStar_Pprint.group uu____5714  in
        FStar_Pprint.op_Hat_Hat uu____5713 break1

and p_typ :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  -> with_comment (p_typ' ps pb) e e.FStar_Parser_AST.range

and p_typ' :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.QForall (bs,trigger,e1) ->
            let uu____5740 =
              let uu____5741 =
                let uu____5742 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5742 FStar_Pprint.space  in
              let uu____5743 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.lift_native_int (2))
                (Prims.lift_native_int (0)) uu____5741 uu____5743
                FStar_Pprint.dot
               in
            let uu____5744 =
              let uu____5745 = p_trigger trigger  in
              let uu____5746 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5745 uu____5746  in
            prefix2 uu____5740 uu____5744
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5762 =
              let uu____5763 =
                let uu____5764 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5764 FStar_Pprint.space  in
              let uu____5765 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.lift_native_int (2))
                (Prims.lift_native_int (0)) uu____5763 uu____5765
                FStar_Pprint.dot
               in
            let uu____5766 =
              let uu____5767 = p_trigger trigger  in
              let uu____5768 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5767 uu____5768  in
            prefix2 uu____5762 uu____5766
        | uu____5769 -> p_simpleTerm ps pb e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5771 -> str "forall"
    | FStar_Parser_AST.QExists uu____5784 -> str "exists"
    | uu____5797 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___65_5798  ->
    match uu___65_5798 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5810 =
          let uu____5811 =
            let uu____5812 = str "pattern"  in
            let uu____5813 =
              let uu____5814 =
                let uu____5815 = p_disjunctivePats pats  in jump2 uu____5815
                 in
              let uu____5816 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5814 uu____5816  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5812 uu____5813  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5811  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5810

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____5822 = str "\\/"  in
    FStar_Pprint.separate_map uu____5822 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____5828 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5828

and p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5838 =
              let uu____5839 =
                let uu____5840 = str "fun"  in
                let uu____5841 =
                  let uu____5842 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5842
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5840 uu____5841  in
              let uu____5843 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5839 uu____5843  in
            let uu____5844 = paren_if ps  in uu____5844 uu____5838
        | uu____5849 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun pb  ->
    fun uu____5853  ->
      match uu____5853 with
      | (pat,when_opt,e) ->
          let uu____5869 =
            let uu____5870 =
              let uu____5871 =
                let uu____5872 =
                  let uu____5873 =
                    let uu____5874 = p_disjunctivePattern pat  in
                    let uu____5875 =
                      let uu____5876 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5876 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5874 uu____5875  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5873  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5872  in
              FStar_Pprint.group uu____5871  in
            let uu____5877 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5870 uu____5877  in
          FStar_Pprint.group uu____5869

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___66_5878  ->
    match uu___66_5878 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5882 = str "when"  in
        let uu____5883 =
          let uu____5884 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5884 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5882 uu____5883

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5886;_},e1::e2::[])
        ->
        let uu____5891 = str "<==>"  in
        let uu____5892 = p_tmImplies e1  in
        let uu____5893 = p_tmIff e2  in
        infix0 uu____5891 uu____5892 uu____5893
    | uu____5894 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5896;_},e1::e2::[])
        ->
        let uu____5901 = str "==>"  in
        let uu____5902 = p_tmArrow p_tmFormula e1  in
        let uu____5903 = p_tmImplies e2  in
        infix0 uu____5901 uu____5902 uu____5903
    | uu____5904 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5915 =
            let uu____5916 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5921 = p_binder false b  in
                   let uu____5922 =
                     let uu____5923 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5923
                      in
                   FStar_Pprint.op_Hat_Hat uu____5921 uu____5922) bs
               in
            let uu____5924 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5916 uu____5924  in
          FStar_Pprint.group uu____5915
      | uu____5925 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5927;_},e1::e2::[])
        ->
        let uu____5932 = str "\\/"  in
        let uu____5933 = p_tmFormula e1  in
        let uu____5934 = p_tmConjunction e2  in
        infix0 uu____5932 uu____5933 uu____5934
    | uu____5935 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5937;_},e1::e2::[])
        ->
        let uu____5942 = str "/\\"  in
        let uu____5943 = p_tmConjunction e1  in
        let uu____5944 = p_tmTuple e2  in
        infix0 uu____5942 uu____5943 uu____5944
    | uu____5945 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5962 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5962
          (fun uu____5970  ->
             match uu____5970 with | (e1,uu____5976) -> p_tmEq e1) args
    | uu____5977 -> p_tmEq e

and paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5982 =
             let uu____5983 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5983  in
           FStar_Pprint.group uu____5982)

and p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals (); pipe_right ()]
             (operatorInfix0ad12 ()))
         in
      p_tmEqWith' p_X n1 e

and p_tmEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Op (op,e1::e2::[]) when
            ((is_operatorInfix0ad12 op) ||
               (let uu____6046 = FStar_Ident.text_of_id op  in
                uu____6046 = "="))
              ||
              (let uu____6048 = FStar_Ident.text_of_id op  in
               uu____6048 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6050 = levels op1  in
            (match uu____6050 with
             | (left1,mine,right1) ->
                 let uu____6060 =
                   let uu____6061 = FStar_All.pipe_left str op1  in
                   let uu____6062 = p_tmEqWith' p_X left1 e1  in
                   let uu____6063 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6061 uu____6062 uu____6063  in
                 paren_if_gt curr mine uu____6060)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6064;_},e1::e2::[])
            ->
            let uu____6069 =
              let uu____6070 = p_tmEqWith p_X e1  in
              let uu____6071 =
                let uu____6072 =
                  let uu____6073 =
                    let uu____6074 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6074  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6073  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6072  in
              FStar_Pprint.op_Hat_Hat uu____6070 uu____6071  in
            FStar_Pprint.group uu____6069
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6075;_},e1::[])
            ->
            let uu____6079 = levels "-"  in
            (match uu____6079 with
             | (left1,mine,right1) ->
                 let uu____6089 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6089)
        | uu____6090 -> p_tmNoEqWith p_X e

and p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]
         in
      p_tmNoEqWith' p_X n1 e

and p_tmNoEqWith' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_X  ->
    fun curr  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Construct
            (lid,(e1,uu____6161)::(e2,uu____6163)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____6183 = is_list e  in Prims.op_Negation uu____6183)
            ->
            let op = "::"  in
            let uu____6185 = levels op  in
            (match uu____6185 with
             | (left1,mine,right1) ->
                 let uu____6195 =
                   let uu____6196 = str op  in
                   let uu____6197 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6198 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6196 uu____6197 uu____6198  in
                 paren_if_gt curr mine uu____6195)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____6206 = levels op  in
            (match uu____6206 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____6222 = p_binder false b  in
                   let uu____6223 =
                     let uu____6224 =
                       let uu____6225 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____6225 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6224
                      in
                   FStar_Pprint.op_Hat_Hat uu____6222 uu____6223  in
                 let uu____6226 =
                   let uu____6227 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____6228 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____6227 uu____6228  in
                 paren_if_gt curr mine uu____6226)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6235 = levels op1  in
            (match uu____6235 with
             | (left1,mine,right1) ->
                 let uu____6245 =
                   let uu____6246 = str op1  in
                   let uu____6247 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6248 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6246 uu____6247 uu____6248  in
                 paren_if_gt curr mine uu____6245)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____6267 =
              let uu____6268 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____6269 =
                let uu____6270 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____6270 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____6268 uu____6269  in
            braces_with_nesting uu____6267
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6275;_},e1::[])
            ->
            let uu____6279 =
              let uu____6280 = str "~"  in
              let uu____6281 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____6280 uu____6281  in
            FStar_Pprint.group uu____6279
        | uu____6282 -> p_X e

and p_tmEqNoRefinement : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_tmEqWith p_appTerm e

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_tmEqWith p_tmRefinement e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_tmNoEqWith p_tmRefinement e

and p_tmRefinement : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.NamedTyp (lid,e1) ->
        let uu____6289 =
          let uu____6290 = p_lidentOrUnderscore lid  in
          let uu____6291 =
            let uu____6292 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6292  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6290 uu____6291  in
        FStar_Pprint.group uu____6289
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6295 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____6297 = p_appTerm e  in
    let uu____6298 =
      let uu____6299 =
        let uu____6300 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6300 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6299  in
    FStar_Pprint.op_Hat_Hat uu____6297 uu____6298

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6305 =
            let uu____6306 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____6306 t phi  in
          soft_parens_with_nesting uu____6305
      | FStar_Parser_AST.TAnnotated uu____6307 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6312 ->
          let uu____6313 =
            let uu____6314 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6314
             in
          failwith uu____6313
      | FStar_Parser_AST.TVariable uu____6315 ->
          let uu____6316 =
            let uu____6317 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6317
             in
          failwith uu____6316
      | FStar_Parser_AST.NoName uu____6318 ->
          let uu____6319 =
            let uu____6320 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6320
             in
          failwith uu____6319

and p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document
  =
  fun ps  ->
    fun uu____6322  ->
      match uu____6322 with
      | (lid,e) ->
          let uu____6329 =
            let uu____6330 = p_qlident lid  in
            let uu____6331 =
              let uu____6332 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6332
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6330 uu____6331  in
          FStar_Pprint.group uu____6329

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6334 when is_general_application e ->
        let uu____6341 = head_and_args e  in
        (match uu____6341 with
         | (head1,args) ->
             let uu____6366 =
               let uu____6377 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6377
               then
                 let uu____6411 =
                   FStar_Util.take
                     (fun uu____6435  ->
                        match uu____6435 with
                        | (uu____6440,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6411 with
                 | (fs_typ_args,args1) ->
                     let uu____6478 =
                       let uu____6479 = p_indexingTerm head1  in
                       let uu____6480 =
                         let uu____6481 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow
                           (Prims.lift_native_int (2))
                           (Prims.lift_native_int (0)) FStar_Pprint.empty
                           FStar_Pprint.langle uu____6481 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6479 uu____6480  in
                     (uu____6478, args1)
               else
                 (let uu____6493 = p_indexingTerm head1  in
                  (uu____6493, args))
                in
             (match uu____6366 with
              | (head_doc,args1) ->
                  let uu____6514 =
                    let uu____6515 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.lift_native_int (2))
                      (Prims.lift_native_int (0)) head_doc uu____6515 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6514))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6535 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6535)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6553 =
               let uu____6554 = p_quident lid  in
               let uu____6555 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6554 uu____6555  in
             FStar_Pprint.group uu____6553
         | hd1::tl1 ->
             let uu____6572 =
               let uu____6573 =
                 let uu____6574 =
                   let uu____6575 = p_quident lid  in
                   let uu____6576 = p_argTerm hd1  in
                   prefix2 uu____6575 uu____6576  in
                 FStar_Pprint.group uu____6574  in
               let uu____6577 =
                 let uu____6578 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6578  in
               FStar_Pprint.op_Hat_Hat uu____6573 uu____6577  in
             FStar_Pprint.group uu____6572)
    | uu____6583 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____6592 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.lift_native_int (2))
            (Prims.lift_native_int (1)) FStar_Pprint.langle uu____6592
            FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6594 = str "#"  in
        let uu____6595 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6594 uu____6595
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____6597  ->
    match uu____6597 with | (e,uu____6603) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6608;_},e1::e2::[])
          ->
          let uu____6613 =
            let uu____6614 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6615 =
              let uu____6616 =
                let uu____6617 = p_term false false e2  in
                soft_parens_with_nesting uu____6617  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6616  in
            FStar_Pprint.op_Hat_Hat uu____6614 uu____6615  in
          FStar_Pprint.group uu____6613
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6618;_},e1::e2::[])
          ->
          let uu____6623 =
            let uu____6624 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6625 =
              let uu____6626 =
                let uu____6627 = p_term false false e2  in
                soft_brackets_with_nesting uu____6627  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6626  in
            FStar_Pprint.op_Hat_Hat uu____6624 uu____6625  in
          FStar_Pprint.group uu____6623
      | uu____6628 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6633 = p_quident lid  in
        let uu____6634 =
          let uu____6635 =
            let uu____6636 = p_term false false e1  in
            soft_parens_with_nesting uu____6636  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6635  in
        FStar_Pprint.op_Hat_Hat uu____6633 uu____6634
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6642 =
          let uu____6643 = FStar_Ident.text_of_id op  in str uu____6643  in
        let uu____6644 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6642 uu____6644
    | uu____6645 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
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
         | uu____6652 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6659 =
          let uu____6660 = FStar_Ident.text_of_id op  in str uu____6660  in
        let uu____6661 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6659 uu____6661
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6665 =
          let uu____6666 =
            let uu____6667 =
              let uu____6668 = FStar_Ident.text_of_id op  in str uu____6668
               in
            let uu____6669 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6667 uu____6669  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6666  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6665
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6684 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6685 =
          let uu____6686 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6687 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6686 p_tmEq uu____6687  in
        let uu____6694 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (1)) uu____6684 uu____6685 uu____6694
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6697 =
          let uu____6698 = p_atomicTermNotQUident e1  in
          let uu____6699 =
            let uu____6700 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6700  in
          FStar_Pprint.prefix (Prims.lift_native_int (2))
            (Prims.lift_native_int (0)) uu____6698 uu____6699
           in
        FStar_Pprint.group uu____6697
    | uu____6701 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6706 = p_quident constr_lid  in
        let uu____6707 =
          let uu____6708 =
            let uu____6709 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6709  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6708  in
        FStar_Pprint.op_Hat_Hat uu____6706 uu____6707
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6711 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6711 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6713 = p_term false false e1  in
        soft_parens_with_nesting uu____6713
    | uu____6714 when is_array e ->
        let es = extract_from_list e  in
        let uu____6718 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6719 =
          let uu____6720 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6720
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6723 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (0)) uu____6718 uu____6719 uu____6723
    | uu____6724 when is_list e ->
        let uu____6725 =
          let uu____6726 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6727 = extract_from_list e  in
          separate_map_or_flow_last uu____6726
            (fun ps  -> p_noSeqTerm ps false) uu____6727
           in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (0)) FStar_Pprint.lbracket uu____6725
          FStar_Pprint.rbracket
    | uu____6732 when is_lex_list e ->
        let uu____6733 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6734 =
          let uu____6735 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6736 = extract_from_list e  in
          separate_map_or_flow_last uu____6735
            (fun ps  -> p_noSeqTerm ps false) uu____6736
           in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (1)) uu____6733 uu____6734
          FStar_Pprint.rbracket
    | uu____6741 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6745 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6746 =
          let uu____6747 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6747 p_appTerm es  in
        FStar_Pprint.surround (Prims.lift_native_int (2))
          (Prims.lift_native_int (0)) uu____6745 uu____6746
          FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6751 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6752 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6751 uu____6752
    | FStar_Parser_AST.Op (op,args) when
        let uu____6759 = handleable_op op args  in
        Prims.op_Negation uu____6759 ->
        let uu____6760 =
          let uu____6761 =
            let uu____6762 = FStar_Ident.text_of_id op  in
            let uu____6763 =
              let uu____6764 =
                let uu____6765 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6765
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6764  in
            Prims.strcat uu____6762 uu____6763  in
          Prims.strcat "Operation " uu____6761  in
        failwith uu____6760
    | FStar_Parser_AST.Uvar uu____6766 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6767 = p_term false false e  in
        soft_parens_with_nesting uu____6767
    | FStar_Parser_AST.Const uu____6768 ->
        let uu____6769 = p_term false false e  in
        soft_parens_with_nesting uu____6769
    | FStar_Parser_AST.Op uu____6770 ->
        let uu____6777 = p_term false false e  in
        soft_parens_with_nesting uu____6777
    | FStar_Parser_AST.Tvar uu____6778 ->
        let uu____6779 = p_term false false e  in
        soft_parens_with_nesting uu____6779
    | FStar_Parser_AST.Var uu____6780 ->
        let uu____6781 = p_term false false e  in
        soft_parens_with_nesting uu____6781
    | FStar_Parser_AST.Name uu____6782 ->
        let uu____6783 = p_term false false e  in
        soft_parens_with_nesting uu____6783
    | FStar_Parser_AST.Construct uu____6784 ->
        let uu____6795 = p_term false false e  in
        soft_parens_with_nesting uu____6795
    | FStar_Parser_AST.Abs uu____6796 ->
        let uu____6803 = p_term false false e  in
        soft_parens_with_nesting uu____6803
    | FStar_Parser_AST.App uu____6804 ->
        let uu____6811 = p_term false false e  in
        soft_parens_with_nesting uu____6811
    | FStar_Parser_AST.Let uu____6812 ->
        let uu____6833 = p_term false false e  in
        soft_parens_with_nesting uu____6833
    | FStar_Parser_AST.LetOpen uu____6834 ->
        let uu____6839 = p_term false false e  in
        soft_parens_with_nesting uu____6839
    | FStar_Parser_AST.Seq uu____6840 ->
        let uu____6845 = p_term false false e  in
        soft_parens_with_nesting uu____6845
    | FStar_Parser_AST.Bind uu____6846 ->
        let uu____6853 = p_term false false e  in
        soft_parens_with_nesting uu____6853
    | FStar_Parser_AST.If uu____6854 ->
        let uu____6861 = p_term false false e  in
        soft_parens_with_nesting uu____6861
    | FStar_Parser_AST.Match uu____6862 ->
        let uu____6877 = p_term false false e  in
        soft_parens_with_nesting uu____6877
    | FStar_Parser_AST.TryWith uu____6878 ->
        let uu____6893 = p_term false false e  in
        soft_parens_with_nesting uu____6893
    | FStar_Parser_AST.Ascribed uu____6894 ->
        let uu____6903 = p_term false false e  in
        soft_parens_with_nesting uu____6903
    | FStar_Parser_AST.Record uu____6904 ->
        let uu____6917 = p_term false false e  in
        soft_parens_with_nesting uu____6917
    | FStar_Parser_AST.Project uu____6918 ->
        let uu____6923 = p_term false false e  in
        soft_parens_with_nesting uu____6923
    | FStar_Parser_AST.Product uu____6924 ->
        let uu____6931 = p_term false false e  in
        soft_parens_with_nesting uu____6931
    | FStar_Parser_AST.Sum uu____6932 ->
        let uu____6939 = p_term false false e  in
        soft_parens_with_nesting uu____6939
    | FStar_Parser_AST.QForall uu____6940 ->
        let uu____6953 = p_term false false e  in
        soft_parens_with_nesting uu____6953
    | FStar_Parser_AST.QExists uu____6954 ->
        let uu____6967 = p_term false false e  in
        soft_parens_with_nesting uu____6967
    | FStar_Parser_AST.Refine uu____6968 ->
        let uu____6973 = p_term false false e  in
        soft_parens_with_nesting uu____6973
    | FStar_Parser_AST.NamedTyp uu____6974 ->
        let uu____6979 = p_term false false e  in
        soft_parens_with_nesting uu____6979
    | FStar_Parser_AST.Requires uu____6980 ->
        let uu____6987 = p_term false false e  in
        soft_parens_with_nesting uu____6987
    | FStar_Parser_AST.Ensures uu____6988 ->
        let uu____6995 = p_term false false e  in
        soft_parens_with_nesting uu____6995
    | FStar_Parser_AST.Attributes uu____6996 ->
        let uu____6999 = p_term false false e  in
        soft_parens_with_nesting uu____6999
    | FStar_Parser_AST.Quote uu____7000 ->
        let uu____7005 = p_term false false e  in
        soft_parens_with_nesting uu____7005
    | FStar_Parser_AST.VQuote uu____7006 ->
        let uu____7007 = p_term false false e  in
        soft_parens_with_nesting uu____7007
    | FStar_Parser_AST.Antiquote uu____7008 ->
        let uu____7013 = p_term false false e  in
        soft_parens_with_nesting uu____7013

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___69_7014  ->
    match uu___69_7014 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____7018 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____7018
    | FStar_Const.Const_string (s,uu____7020) ->
        let uu____7021 = str s  in FStar_Pprint.dquotes uu____7021
    | FStar_Const.Const_bytearray (bytes,uu____7023) ->
        let uu____7028 =
          let uu____7029 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____7029  in
        let uu____7030 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____7028 uu____7030
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___67_7050 =
          match uu___67_7050 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___68_7056 =
          match uu___68_7056 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7067  ->
               match uu____7067 with
               | (s,w) ->
                   let uu____7074 = signedness s  in
                   let uu____7075 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7074 uu____7075)
            sign_width_opt
           in
        let uu____7076 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7076 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7078 = FStar_Range.string_of_range r  in str uu____7078
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7080 = p_quident lid  in
        let uu____7081 =
          let uu____7082 =
            let uu____7083 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7083  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7082  in
        FStar_Pprint.op_Hat_Hat uu____7080 uu____7081

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____7085 = str "u#"  in
    let uu____7086 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7085 uu____7086

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7088;_},u1::u2::[])
        ->
        let uu____7093 =
          let uu____7094 = p_universeFrom u1  in
          let uu____7095 =
            let uu____7096 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7096  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7094 uu____7095  in
        FStar_Pprint.group uu____7093
    | FStar_Parser_AST.App uu____7097 ->
        let uu____7104 = head_and_args u  in
        (match uu____7104 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7130 =
                    let uu____7131 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7132 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7140  ->
                           match uu____7140 with
                           | (u1,uu____7146) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7131 uu____7132  in
                  FStar_Pprint.group uu____7130
              | uu____7147 ->
                  let uu____7148 =
                    let uu____7149 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7149
                     in
                  failwith uu____7148))
    | uu____7150 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7173 = FStar_Ident.text_of_id id1  in str uu____7173
    | FStar_Parser_AST.Paren u1 ->
        let uu____7175 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7175
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7176;_},uu____7177::uu____7178::[])
        ->
        let uu____7181 = p_universeFrom u  in
        soft_parens_with_nesting uu____7181
    | FStar_Parser_AST.App uu____7182 ->
        let uu____7189 = p_universeFrom u  in
        soft_parens_with_nesting uu____7189
    | uu____7190 ->
        let uu____7191 =
          let uu____7192 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7192
           in
        failwith uu____7191

let term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term false false e 
let signature_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_justSig e 
let decl_to_document : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun e  -> p_decl e 
let pat_to_document : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  -> p_disjunctivePattern p 
let binder_to_document : FStar_Parser_AST.binder -> FStar_Pprint.document =
  fun b  -> p_binder true b 
let modul_to_document : FStar_Parser_AST.modul -> FStar_Pprint.document =
  fun m  ->
    FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____7248,decls) ->
           let uu____7254 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7254
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7263,decls,uu____7265) ->
           let uu____7270 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7270
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7327  ->
         match uu____7327 with | (comment,range) -> str comment) comments
  
let modul_with_comments_to_document :
  FStar_Parser_AST.modul ->
    (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
      Prims.list ->
      (FStar_Pprint.document,(Prims.string,FStar_Range.range)
                               FStar_Pervasives_Native.tuple2 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun m  ->
    fun comments  ->
      let decls =
        match m with
        | FStar_Parser_AST.Module (uu____7371,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7377,decls,uu____7379) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7428 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7441;
                 FStar_Parser_AST.doc = uu____7442;
                 FStar_Parser_AST.quals = uu____7443;
                 FStar_Parser_AST.attrs = uu____7444;_}::uu____7445 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7451 =
                   let uu____7454 =
                     let uu____7457 = FStar_List.tl ds  in d :: uu____7457
                      in
                   d0 :: uu____7454  in
                 (uu____7451, (d0.FStar_Parser_AST.drange))
             | uu____7462 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7428 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7526 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.lift_native_int (0))
                      (Prims.lift_native_int (1)) uu____7526
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
                  (let uu____7634 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7634, comments1))))))
  