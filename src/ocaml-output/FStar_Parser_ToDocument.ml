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
        let uu____70 = FStar_ST.op_Colon_Equals should_print_fs_typ_app b  in
        let res = printer t  in
        let uu____95 = FStar_ST.op_Colon_Equals should_print_fs_typ_app b0
           in
        res
  
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
        | FStar_Parser_AST.Construct (lid,uu____866::(e2,uu____868)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____891 -> false  in
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
    | FStar_Parser_AST.Construct (uu____909,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____920,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____941 = extract_from_list e2  in e1 :: uu____941
    | uu____944 ->
        let uu____945 =
          let uu____946 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____946  in
        failwith uu____945
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____955;
           FStar_Parser_AST.level = uu____956;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____958 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____966;
           FStar_Parser_AST.level = uu____967;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____969;
                                                        FStar_Parser_AST.level
                                                          = uu____970;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____972;
                                                   FStar_Parser_AST.level =
                                                     uu____973;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____975;
                FStar_Parser_AST.level = uu____976;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____978;
           FStar_Parser_AST.level = uu____979;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____981 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____991 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____992;
           FStar_Parser_AST.range = uu____993;
           FStar_Parser_AST.level = uu____994;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____995;
                                                        FStar_Parser_AST.range
                                                          = uu____996;
                                                        FStar_Parser_AST.level
                                                          = uu____997;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____999;
                                                   FStar_Parser_AST.level =
                                                     uu____1000;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____1001;
                FStar_Parser_AST.range = uu____1002;
                FStar_Parser_AST.level = uu____1003;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____1005;
           FStar_Parser_AST.level = uu____1006;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____1008 = extract_from_ref_set e1  in
        let uu____1011 = extract_from_ref_set e2  in
        FStar_List.append uu____1008 uu____1011
    | uu____1014 ->
        let uu____1015 =
          let uu____1016 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____1016  in
        failwith uu____1015
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1024 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____1024
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____1030 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____1030
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____1037 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____1037 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____1042 = FStar_Ident.text_of_id op  in uu____1042 <> "~"))
  
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
      | uu____1106 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Left  -> true | uu____1122 -> false
  
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____1128 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____1134 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___54_1154  ->
    match uu___54_1154 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___55_1175  ->
      match uu___55_1175 with
      | FStar_Util.Inl c ->
          let uu____1184 = FStar_String.get s (Prims.parse_int "0")  in
          uu____1184 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____1195 .
    Prims.string ->
      ('Auu____1195,(FStar_Char.char,Prims.string) FStar_Util.either
                      Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1216  ->
      match uu____1216 with
      | (assoc_levels,tokens) ->
          let uu____1244 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1244 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1271 .
    Prims.unit ->
      (associativity,('Auu____1271,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a234  ->
    (Obj.magic (fun uu____1282  -> (Right, [FStar_Util.Inr "**"]))) a234
  
let opinfix3 :
  'Auu____1299 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1299) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a235  ->
    (Obj.magic
       (fun uu____1311  ->
          (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])))
      a235
  
let opinfix2 :
  'Auu____1347 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1347) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a236  ->
    (Obj.magic
       (fun uu____1359  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45])))
      a236
  
let minus_lvl :
  'Auu____1388 .
    Prims.unit ->
      (associativity,('Auu____1388,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a237  ->
    (Obj.magic (fun uu____1399  -> (Left, [FStar_Util.Inr "-"]))) a237
  
let opinfix1 :
  'Auu____1416 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1416) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a238  ->
    (Obj.magic
       (fun uu____1428  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94])))
      a238
  
let pipe_right :
  'Auu____1457 .
    Prims.unit ->
      (associativity,('Auu____1457,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a239  ->
    (Obj.magic (fun uu____1468  -> (Left, [FStar_Util.Inr "|>"]))) a239
  
let opinfix0d :
  'Auu____1485 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1485) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a240  ->
    (Obj.magic (fun uu____1497  -> (Left, [FStar_Util.Inl 36]))) a240
  
let opinfix0c :
  'Auu____1519 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1519) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a241  ->
    (Obj.magic
       (fun uu____1531  ->
          (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])))
      a241
  
let equal :
  'Auu____1567 .
    Prims.unit ->
      (associativity,('Auu____1567,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a242  ->
    (Obj.magic (fun uu____1578  -> (Left, [FStar_Util.Inr "="]))) a242
  
let opinfix0b :
  'Auu____1595 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1595) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a243  ->
    (Obj.magic (fun uu____1607  -> (Left, [FStar_Util.Inl 38]))) a243
  
let opinfix0a :
  'Auu____1629 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1629) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a244  ->
    (Obj.magic (fun uu____1641  -> (Left, [FStar_Util.Inl 124]))) a244
  
let colon_equals :
  'Auu____1663 .
    Prims.unit ->
      (associativity,('Auu____1663,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a245  ->
    (Obj.magic (fun uu____1674  -> (NonAssoc, [FStar_Util.Inr ":="]))) a245
  
let amp :
  'Auu____1691 .
    Prims.unit ->
      (associativity,('Auu____1691,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a246  ->
    (Obj.magic (fun uu____1702  -> (Right, [FStar_Util.Inr "&"]))) a246
  
let colon_colon :
  'Auu____1719 .
    Prims.unit ->
      (associativity,('Auu____1719,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun a247  ->
    (Obj.magic (fun uu____1730  -> (Right, [FStar_Util.Inr "::"]))) a247
  
let (level_associativity_spec :
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
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
let (level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list)
  =
  let levels_from_associativity l uu___56_1939 =
    match uu___56_1939 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1979  ->
         match uu____1979 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____2063 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____2063 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____2113) ->
          assoc_levels
      | uu____2157 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____2198 .
    ('Auu____2198,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2261 =
        FStar_List.tryFind
          (fun uu____2301  ->
             match uu____2301 with
             | (uu____2319,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2261 with
      | FStar_Pervasives_Native.Some ((uu____2361,l1,uu____2363),uu____2364)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2419 =
            let uu____2420 =
              let uu____2421 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2421  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2420
             in
          failwith uu____2419
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2457 = assign_levels level_associativity_spec op  in
    match uu____2457 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2482 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2482) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun a248  ->
    (Obj.magic
       (fun uu____2496  ->
          [opinfix0a ();
          opinfix0b ();
          opinfix0c ();
          opinfix0d ();
          opinfix1 ();
          opinfix2 ()])) a248
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2579 =
      let uu____2593 =
        let uu____2608 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2608  in
      FStar_List.tryFind uu____2593 (operatorInfix0ad12 ())  in
    uu____2579 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2711 =
      let uu____2725 =
        let uu____2740 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2740  in
      FStar_List.tryFind uu____2725 opinfix34  in
    uu____2711 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2796 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2796
    then (Prims.parse_int "1")
    else
      (let uu____2798 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2798
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2807 . FStar_Ident.ident -> 'Auu____2807 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_4 when _0_4 = (Prims.parse_int "0") -> true
      | _0_5 when _0_5 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2823 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2823 ["-"; "~"])
      | _0_6 when _0_6 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2825 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2825
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_7 when _0_7 = (Prims.parse_int "3") ->
          let uu____2826 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2826 [".()<-"; ".[]<-"]
      | uu____2827 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2865 .
    ('Auu____2865 -> FStar_Pprint.document) ->
      'Auu____2865 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2903 = FStar_ST.op_Bang comment_stack  in
          match uu____2903 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2966 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2966
              then
                let uu____2971 = FStar_ST.op_Colon_Equals comment_stack cs
                   in
                let uu____3007 =
                  let uu____3008 =
                    let uu____3009 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____3009 FStar_Pprint.hardline
                     in
                  FStar_Pprint.op_Hat_Hat acc uu____3008  in
                comments_before_pos uu____3007 print_pos lookahead_pos
              else
                (let uu____3011 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____3011))
           in
        let uu____3012 =
          let uu____3017 =
            let uu____3018 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____3018  in
          let uu____3019 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____3017 uu____3019  in
        match uu____3012 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____3025 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____3025
              else comments  in
            let uu____3031 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____3031
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____3052 = FStar_ST.op_Bang comment_stack  in
          match uu____3052 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              let uu____3107 = FStar_ST.op_Colon_Equals comment_stack cs  in
              let lnum =
                let uu____3144 =
                  let uu____3145 =
                    let uu____3146 = FStar_Range.start_of_range crange  in
                    FStar_Range.line_of_pos uu____3146  in
                  uu____3145 - lbegin  in
                max k uu____3144  in
              let doc2 =
                let uu____3148 =
                  let uu____3149 =
                    FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                  let uu____3150 = str comment  in
                  FStar_Pprint.op_Hat_Hat uu____3149 uu____3150  in
                FStar_Pprint.op_Hat_Hat doc1 uu____3148  in
              let uu____3151 =
                let uu____3152 = FStar_Range.end_of_range crange  in
                FStar_Range.line_of_pos uu____3152  in
              place_comments_until_pos (Prims.parse_int "1") uu____3151
                pos_end doc2
          | uu____3153 ->
              let lnum =
                let uu____3161 =
                  let uu____3162 = FStar_Range.line_of_pos pos_end  in
                  uu____3162 - lbegin  in
                max (Prims.parse_int "1") uu____3161  in
              let uu____3163 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____3163
  
let separate_map_with_comments :
  'Auu____3176 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____3176 -> FStar_Pprint.document) ->
          'Auu____3176 Prims.list ->
            ('Auu____3176 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3231 x =
              match uu____3231 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3245 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3245 doc1
                     in
                  let uu____3246 =
                    let uu____3247 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3247  in
                  let uu____3248 =
                    let uu____3249 =
                      let uu____3250 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3250  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3249  in
                  (uu____3246, uu____3248)
               in
            let uu____3251 =
              let uu____3258 = FStar_List.hd xs  in
              let uu____3259 = FStar_List.tl xs  in (uu____3258, uu____3259)
               in
            match uu____3251 with
            | (x,xs1) ->
                let init1 =
                  let uu____3275 =
                    let uu____3276 =
                      let uu____3277 = extract_range x  in
                      FStar_Range.end_of_range uu____3277  in
                    FStar_Range.line_of_pos uu____3276  in
                  let uu____3278 =
                    let uu____3279 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3279  in
                  (uu____3275, uu____3278)  in
                let uu____3280 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3280
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3909 =
      let uu____3910 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3911 =
        let uu____3912 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3913 =
          let uu____3914 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3915 =
            let uu____3916 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3916
             in
          FStar_Pprint.op_Hat_Hat uu____3914 uu____3915  in
        FStar_Pprint.op_Hat_Hat uu____3912 uu____3913  in
      FStar_Pprint.op_Hat_Hat uu____3910 uu____3911  in
    FStar_Pprint.group uu____3909

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3919 =
      let uu____3920 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3920  in
    let uu____3921 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3919 FStar_Pprint.space uu____3921
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3922  ->
    match uu____3922 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3957 =
                match uu____3957 with
                | (kwd,arg) ->
                    let uu____3964 = str "@"  in
                    let uu____3965 =
                      let uu____3966 = str kwd  in
                      let uu____3967 =
                        let uu____3968 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3968
                         in
                      FStar_Pprint.op_Hat_Hat uu____3966 uu____3967  in
                    FStar_Pprint.op_Hat_Hat uu____3964 uu____3965
                 in
              let uu____3969 =
                let uu____3970 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3970 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3969
           in
        let uu____3975 =
          let uu____3976 =
            let uu____3977 =
              let uu____3978 =
                let uu____3979 = str doc1  in
                let uu____3980 =
                  let uu____3981 =
                    let uu____3982 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3982  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3981  in
                FStar_Pprint.op_Hat_Hat uu____3979 uu____3980  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3978  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3977  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3976  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3975

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3986 =
          let uu____3987 = str "val"  in
          let uu____3988 =
            let uu____3989 =
              let uu____3990 = p_lident lid  in
              let uu____3991 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3990 uu____3991  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3989  in
          FStar_Pprint.op_Hat_Hat uu____3987 uu____3988  in
        let uu____3992 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3986 uu____3992
    | FStar_Parser_AST.TopLevelLet (uu____3993,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____4018 =
               let uu____4019 = str "let"  in
               let uu____4020 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4019 uu____4020  in
             FStar_Pprint.group uu____4018) lbs
    | uu____4021 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___57_4035 =
          match uu___57_4035 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____4043 = f x  in
              let uu____4044 =
                let uu____4045 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____4045  in
              FStar_Pprint.op_Hat_Hat uu____4043 uu____4044
           in
        let uu____4046 = str "["  in
        let uu____4047 =
          let uu____4048 = p_list' l  in
          let uu____4049 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____4048 uu____4049  in
        FStar_Pprint.op_Hat_Hat uu____4046 uu____4047

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____4052 =
          let uu____4053 = str "open"  in
          let uu____4054 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4053 uu____4054  in
        FStar_Pprint.group uu____4052
    | FStar_Parser_AST.Include uid ->
        let uu____4056 =
          let uu____4057 = str "include"  in
          let uu____4058 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4057 uu____4058  in
        FStar_Pprint.group uu____4056
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____4061 =
          let uu____4062 = str "module"  in
          let uu____4063 =
            let uu____4064 =
              let uu____4065 = p_uident uid1  in
              let uu____4066 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4065 uu____4066  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4064  in
          FStar_Pprint.op_Hat_Hat uu____4062 uu____4063  in
        let uu____4067 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____4061 uu____4067
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____4069 =
          let uu____4070 = str "module"  in
          let uu____4071 =
            let uu____4072 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4072  in
          FStar_Pprint.op_Hat_Hat uu____4070 uu____4071  in
        FStar_Pprint.group uu____4069
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____4105 = str "effect"  in
          let uu____4106 =
            let uu____4107 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4107  in
          FStar_Pprint.op_Hat_Hat uu____4105 uu____4106  in
        let uu____4108 =
          let uu____4109 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____4109 FStar_Pprint.equals
           in
        let uu____4110 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4108 uu____4110
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____4128 = str "type"  in
        let uu____4129 = str "and"  in
        precede_break_separate_map uu____4128 uu____4129 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____4151 = str "let"  in
          let uu____4152 =
            let uu____4153 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____4153 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____4151 uu____4152  in
        let uu____4154 =
          let uu____4155 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____4155 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____4154 p_letbinding lbs
          (fun uu____4163  ->
             match uu____4163 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____4172 =
          let uu____4173 = str "val"  in
          let uu____4174 =
            let uu____4175 =
              let uu____4176 = p_lident lid  in
              let uu____4177 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____4176 uu____4177  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4175  in
          FStar_Pprint.op_Hat_Hat uu____4173 uu____4174  in
        let uu____4178 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4172 uu____4178
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____4182 =
            let uu____4183 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____4183 FStar_Util.is_upper  in
          if uu____4182
          then FStar_Pprint.empty
          else
            (let uu____4185 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____4185 FStar_Pprint.space)
           in
        let uu____4186 =
          let uu____4187 =
            let uu____4188 = p_ident id1  in
            let uu____4189 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____4188 uu____4189  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____4187  in
        let uu____4190 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____4186 uu____4190
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____4197 = str "exception"  in
        let uu____4198 =
          let uu____4199 =
            let uu____4200 = p_uident uid  in
            let uu____4201 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____4205 =
                     let uu____4206 = str "of"  in
                     let uu____4207 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____4206 uu____4207  in
                   FStar_Pprint.op_Hat_Hat break1 uu____4205) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____4200 uu____4201  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4199  in
        FStar_Pprint.op_Hat_Hat uu____4197 uu____4198
    | FStar_Parser_AST.NewEffect ne ->
        let uu____4209 = str "new_effect"  in
        let uu____4210 =
          let uu____4211 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4211  in
        FStar_Pprint.op_Hat_Hat uu____4209 uu____4210
    | FStar_Parser_AST.SubEffect se ->
        let uu____4213 = str "sub_effect"  in
        let uu____4214 =
          let uu____4215 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4215  in
        FStar_Pprint.op_Hat_Hat uu____4213 uu____4214
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____4218 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____4218 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____4219 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____4220) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____4243 = str "%splice"  in
        let uu____4244 =
          let uu____4245 =
            let uu____4246 = str ";"  in p_list p_uident uu____4246 ids  in
          let uu____4247 =
            let uu____4248 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4248  in
          FStar_Pprint.op_Hat_Hat uu____4245 uu____4247  in
        FStar_Pprint.op_Hat_Hat uu____4243 uu____4244

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___58_4249  ->
    match uu___58_4249 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____4251 = str "#set-options"  in
        let uu____4252 =
          let uu____4253 =
            let uu____4254 = str s  in FStar_Pprint.dquotes uu____4254  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4253  in
        FStar_Pprint.op_Hat_Hat uu____4251 uu____4252
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____4258 = str "#reset-options"  in
        let uu____4259 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____4263 =
                 let uu____4264 = str s  in FStar_Pprint.dquotes uu____4264
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4263) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4258 uu____4259
    | FStar_Parser_AST.LightOff  ->
        let uu____4265 =
          FStar_ST.op_Colon_Equals should_print_fs_typ_app true  in
        str "#light \"off\""

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4292  ->
    match uu____4292 with
    | (typedecl,fsdoc_opt) ->
        let uu____4305 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____4306 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____4305 uu____4306

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___59_4307  ->
    match uu___59_4307 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____4323 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____4340 =
          let uu____4341 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____4341  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____4390 =
          match uu____4390 with
          | (lid1,t,doc_opt) ->
              let uu____4406 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____4406
           in
        let p_fields uu____4421 =
          let uu____4422 =
            let uu____4423 =
              let uu____4424 =
                let uu____4425 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4425 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4424  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4423  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4422  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____4490 =
          match uu____4490 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____4516 =
                  let uu____4517 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____4517  in
                FStar_Range.extend_to_end_of_line uu____4516  in
              let p_constructorBranch decl =
                let uu____4551 =
                  let uu____4552 =
                    let uu____4553 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4553  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4552  in
                FStar_Pprint.group uu____4551  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____4574 =
          let uu____4575 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____4575  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4590  ->
             let uu____4591 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____4591)

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
            let uu____4606 = p_ident lid  in
            let uu____4607 =
              let uu____4608 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4608  in
            FStar_Pprint.op_Hat_Hat uu____4606 uu____4607
          else
            (let binders_doc =
               let uu____4611 = p_typars bs  in
               let uu____4612 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4616 =
                        let uu____4617 =
                          let uu____4618 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4618
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4617
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____4616) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____4611 uu____4612  in
             let uu____4619 = p_ident lid  in
             let uu____4620 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4619 binders_doc uu____4620)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4622  ->
      match uu____4622 with
      | (lid,t,doc_opt) ->
          let uu____4638 =
            let uu____4639 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4640 =
              let uu____4641 = p_lident lid  in
              let uu____4642 =
                let uu____4643 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4643  in
              FStar_Pprint.op_Hat_Hat uu____4641 uu____4642  in
            FStar_Pprint.op_Hat_Hat uu____4639 uu____4640  in
          FStar_Pprint.group uu____4638

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4644  ->
    match uu____4644 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4672 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4673 =
          let uu____4674 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4675 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4680 =
                   let uu____4681 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4681  in
                 let uu____4682 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4680 uu____4682) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4674 uu____4675  in
        FStar_Pprint.op_Hat_Hat uu____4672 uu____4673

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4683  ->
    match uu____4683 with
    | (pat,uu____4689) ->
        let uu____4690 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4709 =
                let uu____4710 =
                  let uu____4711 =
                    let uu____4712 =
                      let uu____4713 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4713
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4712  in
                  FStar_Pprint.group uu____4711  in
                FStar_Pprint.op_Hat_Hat break1 uu____4710  in
              (pat1, uu____4709)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4725 =
                let uu____4726 =
                  let uu____4727 =
                    let uu____4728 =
                      let uu____4729 =
                        let uu____4730 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4730
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4729
                       in
                    FStar_Pprint.group uu____4728  in
                  let uu____4731 =
                    let uu____4732 =
                      let uu____4733 = str "by"  in
                      let uu____4734 =
                        let uu____4735 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4735
                         in
                      FStar_Pprint.op_Hat_Hat uu____4733 uu____4734  in
                    FStar_Pprint.group uu____4732  in
                  FStar_Pprint.op_Hat_Hat uu____4727 uu____4731  in
                FStar_Pprint.op_Hat_Hat break1 uu____4726  in
              (pat1, uu____4725)
          | uu____4736 -> (pat, FStar_Pprint.empty)  in
        (match uu____4690 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4740);
                     FStar_Parser_AST.prange = uu____4741;_},pats)
                  ->
                  let uu____4751 =
                    let uu____4752 = p_lident x  in
                    let uu____4753 =
                      let uu____4754 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4754 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4752 uu____4753  in
                  FStar_Pprint.group uu____4751
              | uu____4755 ->
                  let uu____4756 =
                    let uu____4757 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4757 ascr_doc  in
                  FStar_Pprint.group uu____4756))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4758  ->
    match uu____4758 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4766 =
          let uu____4767 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4767  in
        let uu____4768 = p_term false false e  in
        prefix2 uu____4766 uu____4768

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___60_4769  ->
    match uu___60_4769 with
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
        let uu____4794 = p_uident uid  in
        let uu____4795 = p_binders true bs  in
        let uu____4796 =
          let uu____4797 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4797  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4794 uu____4795 uu____4796

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
          let uu____4806 =
            let uu____4807 =
              let uu____4808 =
                let uu____4809 = p_uident uid  in
                let uu____4810 = p_binders true bs  in
                let uu____4811 =
                  let uu____4812 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4812  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4809 uu____4810 uu____4811
                 in
              FStar_Pprint.group uu____4808  in
            let uu____4813 =
              let uu____4814 = str "with"  in
              let uu____4815 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4814 uu____4815  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4807 uu____4813  in
          braces_with_nesting uu____4806

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
          let uu____4846 =
            let uu____4847 = p_lident lid  in
            let uu____4848 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4847 uu____4848  in
          let uu____4849 = p_simpleTerm ps false e  in
          prefix2 uu____4846 uu____4849
      | uu____4850 ->
          let uu____4851 =
            let uu____4852 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4852
             in
          failwith uu____4851

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4912 =
        match uu____4912 with
        | (kwd,t) ->
            let uu____4919 =
              let uu____4920 = str kwd  in
              let uu____4921 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4920 uu____4921  in
            let uu____4922 = p_simpleTerm ps false t  in
            prefix2 uu____4919 uu____4922
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4927 =
      let uu____4928 =
        let uu____4929 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4930 =
          let uu____4931 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4931  in
        FStar_Pprint.op_Hat_Hat uu____4929 uu____4930  in
      let uu____4932 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4928 uu____4932  in
    let uu____4933 =
      let uu____4934 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4934  in
    FStar_Pprint.op_Hat_Hat uu____4927 uu____4933

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___61_4935  ->
    match uu___61_4935 with
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
    let uu____4937 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4937

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___62_4938  ->
    match uu___62_4938 with
    | FStar_Parser_AST.Rec  ->
        let uu____4939 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4939
    | FStar_Parser_AST.Mutable  ->
        let uu____4940 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4940
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___63_4941  ->
    match uu___63_4941 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4946 =
          let uu____4947 =
            let uu____4948 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4948  in
          FStar_Pprint.separate_map uu____4947 p_tuplePattern pats  in
        FStar_Pprint.group uu____4946
    | uu____4949 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4956 =
          let uu____4957 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4957 p_constructorPattern pats  in
        FStar_Pprint.group uu____4956
    | uu____4958 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4961;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4966 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4967 = p_constructorPattern hd1  in
        let uu____4968 = p_constructorPattern tl1  in
        infix0 uu____4966 uu____4967 uu____4968
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4970;_},pats)
        ->
        let uu____4976 = p_quident uid  in
        let uu____4977 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4976 uu____4977
    | uu____4978 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4994;
               FStar_Parser_AST.blevel = uu____4995;
               FStar_Parser_AST.aqual = uu____4996;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____5002 =
               let uu____5003 = p_ident lid  in
               p_refinement aqual uu____5003 t1 phi  in
             soft_parens_with_nesting uu____5002
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____5005;
               FStar_Parser_AST.blevel = uu____5006;
               FStar_Parser_AST.aqual = uu____5007;_},phi))
             ->
             let uu____5009 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____5009
         | uu____5010 ->
             let uu____5015 =
               let uu____5016 = p_tuplePattern pat  in
               let uu____5017 =
                 let uu____5018 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____5019 =
                   let uu____5020 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5020  in
                 FStar_Pprint.op_Hat_Hat uu____5018 uu____5019  in
               FStar_Pprint.op_Hat_Hat uu____5016 uu____5017  in
             soft_parens_with_nesting uu____5015)
    | FStar_Parser_AST.PatList pats ->
        let uu____5024 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5024 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____5040 =
          match uu____5040 with
          | (lid,pat) ->
              let uu____5047 = p_qlident lid  in
              let uu____5048 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____5047 uu____5048
           in
        let uu____5049 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____5049
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____5059 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5060 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____5061 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5059 uu____5060 uu____5061
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) ->
        let uu____5068 = ()  in p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____5070 =
          let uu____5071 =
            let uu____5072 =
              let uu____5073 = FStar_Ident.text_of_id op  in str uu____5073
               in
            let uu____5074 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5072 uu____5074  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5071  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5070
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____5082 = FStar_Pprint.optional p_aqual aqual  in
        let uu____5083 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____5082 uu____5083
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____5085 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____5088;
           FStar_Parser_AST.prange = uu____5089;_},uu____5090)
        ->
        let uu____5095 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5095
    | FStar_Parser_AST.PatTuple (uu____5096,false ) ->
        let uu____5101 = p_tuplePattern p  in
        soft_parens_with_nesting uu____5101
    | uu____5102 ->
        let uu____5103 =
          let uu____5104 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____5104  in
        failwith uu____5103

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____5108 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____5109 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____5108 uu____5109
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____5116;
                   FStar_Parser_AST.blevel = uu____5117;
                   FStar_Parser_AST.aqual = uu____5118;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____5120 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____5120 t1 phi
            | uu____5121 ->
                let uu____5122 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____5123 =
                  let uu____5124 = p_lident lid  in
                  let uu____5125 =
                    let uu____5126 =
                      let uu____5127 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____5128 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____5127 uu____5128  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5126  in
                  FStar_Pprint.op_Hat_Hat uu____5124 uu____5125  in
                FStar_Pprint.op_Hat_Hat uu____5122 uu____5123
             in
          if is_atomic
          then
            let uu____5129 =
              let uu____5130 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5130  in
            FStar_Pprint.group uu____5129
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____5132 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____5139;
                  FStar_Parser_AST.blevel = uu____5140;
                  FStar_Parser_AST.aqual = uu____5141;_},phi)
               ->
               if is_atomic
               then
                 let uu____5143 =
                   let uu____5144 =
                     let uu____5145 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____5145 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5144  in
                 FStar_Pprint.group uu____5143
               else
                 (let uu____5147 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____5147)
           | uu____5148 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____5156 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____5157 =
            let uu____5158 =
              let uu____5159 =
                let uu____5160 = p_appTerm t  in
                let uu____5161 =
                  let uu____5162 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____5162  in
                FStar_Pprint.op_Hat_Hat uu____5160 uu____5161  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5159  in
            FStar_Pprint.op_Hat_Hat binder uu____5158  in
          FStar_Pprint.op_Hat_Hat uu____5156 uu____5157

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____5168 = FStar_Ident.text_of_lid lid  in str uu____5168

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____5170 = FStar_Ident.text_of_lid lid  in str uu____5170

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____5172 = FStar_Ident.text_of_id lid  in str uu____5172

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____5174 = FStar_Ident.text_of_id lid  in str uu____5174

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____5176 = FStar_Ident.text_of_id lid  in str uu____5176

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____5178 = FStar_Ident.text_of_id lid  in str uu____5178

and (p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1

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
            let uu____5192 =
              let uu____5193 =
                let uu____5194 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____5194 FStar_Pprint.semi  in
              FStar_Pprint.group uu____5193  in
            let uu____5195 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5192 uu____5195
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____5199 =
              let uu____5200 =
                let uu____5201 =
                  let uu____5202 = p_lident x  in
                  let uu____5203 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____5202 uu____5203  in
                let uu____5204 =
                  let uu____5205 = p_noSeqTerm true false e1  in
                  let uu____5206 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____5205 uu____5206  in
                op_Hat_Slash_Plus_Hat uu____5201 uu____5204  in
              FStar_Pprint.group uu____5200  in
            let uu____5207 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5199 uu____5207
        | uu____5208 ->
            let uu____5209 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____5209

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
            let uu____5220 =
              let uu____5221 = p_tmIff e1  in
              let uu____5222 =
                let uu____5223 =
                  let uu____5224 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5224
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5223  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5221 uu____5222  in
            FStar_Pprint.group uu____5220
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____5230 =
              let uu____5231 = p_tmIff e1  in
              let uu____5232 =
                let uu____5233 =
                  let uu____5234 =
                    let uu____5235 = p_typ false false t  in
                    let uu____5236 =
                      let uu____5237 = str "by"  in
                      let uu____5238 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____5237 uu____5238  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____5235 uu____5236  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5234
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____5233  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5231 uu____5232  in
            FStar_Pprint.group uu____5230
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____5239;_},e1::e2::e3::[])
            ->
            let uu____5245 =
              let uu____5246 =
                let uu____5247 =
                  let uu____5248 = p_atomicTermNotQUident e1  in
                  let uu____5249 =
                    let uu____5250 =
                      let uu____5251 =
                        let uu____5252 = p_term false false e2  in
                        soft_parens_with_nesting uu____5252  in
                      let uu____5253 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5251 uu____5253  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5250  in
                  FStar_Pprint.op_Hat_Hat uu____5248 uu____5249  in
                FStar_Pprint.group uu____5247  in
              let uu____5254 =
                let uu____5255 = p_noSeqTerm ps pb e3  in jump2 uu____5255
                 in
              FStar_Pprint.op_Hat_Hat uu____5246 uu____5254  in
            FStar_Pprint.group uu____5245
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____5256;_},e1::e2::e3::[])
            ->
            let uu____5262 =
              let uu____5263 =
                let uu____5264 =
                  let uu____5265 = p_atomicTermNotQUident e1  in
                  let uu____5266 =
                    let uu____5267 =
                      let uu____5268 =
                        let uu____5269 = p_term false false e2  in
                        soft_brackets_with_nesting uu____5269  in
                      let uu____5270 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____5268 uu____5270  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5267  in
                  FStar_Pprint.op_Hat_Hat uu____5265 uu____5266  in
                FStar_Pprint.group uu____5264  in
              let uu____5271 =
                let uu____5272 = p_noSeqTerm ps pb e3  in jump2 uu____5272
                 in
              FStar_Pprint.op_Hat_Hat uu____5263 uu____5271  in
            FStar_Pprint.group uu____5262
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____5279 = ()  in
            let uu____5280 =
              let uu____5281 = str "requires"  in
              let uu____5282 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5281 uu____5282  in
            FStar_Pprint.group uu____5280
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5289 = ()  in
            let uu____5290 =
              let uu____5291 = str "ensures"  in
              let uu____5292 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5291 uu____5292  in
            FStar_Pprint.group uu____5290
        | FStar_Parser_AST.Attributes es ->
            let uu____5296 =
              let uu____5297 = str "attributes"  in
              let uu____5298 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5297 uu____5298  in
            FStar_Pprint.group uu____5296
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5302 =
                let uu____5303 =
                  let uu____5304 = str "if"  in
                  let uu____5305 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5304 uu____5305  in
                let uu____5306 =
                  let uu____5307 = str "then"  in
                  let uu____5308 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5307 uu____5308  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5303 uu____5306  in
              FStar_Pprint.group uu____5302
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5311,uu____5312,e31) when
                     is_unit e31 ->
                     let uu____5314 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5314
                 | uu____5315 -> p_noSeqTerm false false e2  in
               let uu____5316 =
                 let uu____5317 =
                   let uu____5318 = str "if"  in
                   let uu____5319 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5318 uu____5319  in
                 let uu____5320 =
                   let uu____5321 =
                     let uu____5322 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5322 e2_doc  in
                   let uu____5323 =
                     let uu____5324 = str "else"  in
                     let uu____5325 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5324 uu____5325  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5321 uu____5323  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5317 uu____5320  in
               FStar_Pprint.group uu____5316)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5348 =
              let uu____5349 =
                let uu____5350 =
                  let uu____5351 = str "try"  in
                  let uu____5352 = p_noSeqTerm false false e1  in
                  prefix2 uu____5351 uu____5352  in
                let uu____5353 =
                  let uu____5354 = str "with"  in
                  let uu____5355 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5354 uu____5355  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5350 uu____5353  in
              FStar_Pprint.group uu____5349  in
            let uu____5364 = paren_if (ps || pb)  in uu____5364 uu____5348
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5390 =
              let uu____5391 =
                let uu____5392 =
                  let uu____5393 = str "match"  in
                  let uu____5394 = p_noSeqTerm false false e1  in
                  let uu____5395 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5393 uu____5394 uu____5395
                   in
                let uu____5396 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5392 uu____5396  in
              FStar_Pprint.group uu____5391  in
            let uu____5405 = paren_if (ps || pb)  in uu____5405 uu____5390
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5411 =
              let uu____5412 =
                let uu____5413 =
                  let uu____5414 = str "let open"  in
                  let uu____5415 = p_quident uid  in
                  let uu____5416 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5414 uu____5415 uu____5416
                   in
                let uu____5417 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5413 uu____5417  in
              FStar_Pprint.group uu____5412  in
            let uu____5418 = paren_if ps  in uu____5418 uu____5411
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5478 is_last =
              match uu____5478 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5511 =
                          let uu____5512 = str "let"  in
                          let uu____5513 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5512 uu____5513
                           in
                        FStar_Pprint.group uu____5511
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5514 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5519 =
                    if is_last
                    then
                      let uu____5520 =
                        let uu____5521 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____5522 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____5521 doc_expr
                          uu____5522
                         in
                      FStar_Pprint.group uu____5520
                    else
                      (let uu____5524 =
                         let uu____5525 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____5525 doc_expr
                          in
                       FStar_Pprint.group uu____5524)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5519
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5571 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5571
                     else
                       (let uu____5579 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5579)) lbs
               in
            let lbs_doc =
              let uu____5587 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5587  in
            let uu____5588 =
              let uu____5589 =
                let uu____5590 =
                  let uu____5591 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5591
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5590  in
              FStar_Pprint.group uu____5589  in
            let uu____5592 = paren_if ps  in uu____5592 uu____5588
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5598;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5601;
                                                             FStar_Parser_AST.level
                                                               = uu____5602;_})
            when matches_var maybe_x x ->
            let uu____5629 =
              let uu____5630 =
                let uu____5631 = str "function"  in
                let uu____5632 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5631 uu____5632  in
              FStar_Pprint.group uu____5630  in
            let uu____5641 = paren_if (ps || pb)  in uu____5641 uu____5629
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5646 =
              let uu____5647 = str "quote"  in
              let uu____5648 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5647 uu____5648  in
            FStar_Pprint.group uu____5646
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5650 =
              let uu____5651 = str "`"  in
              let uu____5652 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5651 uu____5652  in
            FStar_Pprint.group uu____5650
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5654 =
              let uu____5655 = str "%`"  in
              let uu____5656 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5655 uu____5656  in
            FStar_Pprint.group uu____5654
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5658 =
              let uu____5659 = str "`#"  in
              let uu____5660 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5659 uu____5660  in
            FStar_Pprint.group uu____5658
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5662 =
              let uu____5663 = str "`@"  in
              let uu____5664 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5663 uu____5664  in
            FStar_Pprint.group uu____5662
        | uu____5665 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___64_5666  ->
    match uu___64_5666 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5678 =
          let uu____5679 =
            let uu____5680 = str "[@"  in
            let uu____5681 =
              let uu____5682 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5683 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5682 uu____5683  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5680 uu____5681  in
          FStar_Pprint.group uu____5679  in
        FStar_Pprint.op_Hat_Hat uu____5678 break1

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
            let uu____5705 =
              let uu____5706 =
                let uu____5707 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5707 FStar_Pprint.space  in
              let uu____5708 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5706 uu____5708 FStar_Pprint.dot
               in
            let uu____5709 =
              let uu____5710 = p_trigger trigger  in
              let uu____5711 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5710 uu____5711  in
            prefix2 uu____5705 uu____5709
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5727 =
              let uu____5728 =
                let uu____5729 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5729 FStar_Pprint.space  in
              let uu____5730 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5728 uu____5730 FStar_Pprint.dot
               in
            let uu____5731 =
              let uu____5732 = p_trigger trigger  in
              let uu____5733 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5732 uu____5733  in
            prefix2 uu____5727 uu____5731
        | uu____5734 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5736 -> str "forall"
    | FStar_Parser_AST.QExists uu____5749 -> str "exists"
    | uu____5762 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___65_5763  ->
    match uu___65_5763 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5775 =
          let uu____5776 =
            let uu____5777 = str "pattern"  in
            let uu____5778 =
              let uu____5779 =
                let uu____5780 = p_disjunctivePats pats  in jump2 uu____5780
                 in
              let uu____5781 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5779 uu____5781  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5777 uu____5778  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5776  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5775

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5787 = str "\\/"  in
    FStar_Pprint.separate_map uu____5787 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5793 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5793

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5803 =
              let uu____5804 =
                let uu____5805 = str "fun"  in
                let uu____5806 =
                  let uu____5807 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5807
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5805 uu____5806  in
              let uu____5808 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5804 uu____5808  in
            let uu____5809 = paren_if ps  in uu____5809 uu____5803
        | uu____5813 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5817  ->
      match uu____5817 with
      | (pat,when_opt,e) ->
          let uu____5833 =
            let uu____5834 =
              let uu____5835 =
                let uu____5836 =
                  let uu____5837 =
                    let uu____5838 = p_disjunctivePattern pat  in
                    let uu____5839 =
                      let uu____5840 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5840 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5838 uu____5839  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5837  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5836  in
              FStar_Pprint.group uu____5835  in
            let uu____5841 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5834 uu____5841  in
          FStar_Pprint.group uu____5833

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___66_5842  ->
    match uu___66_5842 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5846 = str "when"  in
        let uu____5847 =
          let uu____5848 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5848 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5846 uu____5847

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5850;_},e1::e2::[])
        ->
        let uu____5855 = str "<==>"  in
        let uu____5856 = p_tmImplies e1  in
        let uu____5857 = p_tmIff e2  in
        infix0 uu____5855 uu____5856 uu____5857
    | uu____5858 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5860;_},e1::e2::[])
        ->
        let uu____5865 = str "==>"  in
        let uu____5866 = p_tmArrow p_tmFormula e1  in
        let uu____5867 = p_tmImplies e2  in
        infix0 uu____5865 uu____5866 uu____5867
    | uu____5868 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5879 =
            let uu____5880 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5885 = p_binder false b  in
                   let uu____5886 =
                     let uu____5887 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5887
                      in
                   FStar_Pprint.op_Hat_Hat uu____5885 uu____5886) bs
               in
            let uu____5888 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5880 uu____5888  in
          FStar_Pprint.group uu____5879
      | uu____5889 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5891;_},e1::e2::[])
        ->
        let uu____5896 = str "\\/"  in
        let uu____5897 = p_tmFormula e1  in
        let uu____5898 = p_tmConjunction e2  in
        infix0 uu____5896 uu____5897 uu____5898
    | uu____5899 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5901;_},e1::e2::[])
        ->
        let uu____5906 = str "/\\"  in
        let uu____5907 = p_tmConjunction e1  in
        let uu____5908 = p_tmTuple e2  in
        infix0 uu____5906 uu____5907 uu____5908
    | uu____5909 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5926 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5926
          (fun uu____5934  ->
             match uu____5934 with | (e1,uu____5940) -> p_tmEq e1) args
    | uu____5941 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5946 =
             let uu____5947 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5947  in
           FStar_Pprint.group uu____5946)

and (p_tmEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 =
        max_level
          (FStar_List.append [colon_equals (); pipe_right ()]
             (operatorInfix0ad12 ()))
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
               (let uu____6010 = FStar_Ident.text_of_id op  in
                uu____6010 = "="))
              ||
              (let uu____6012 = FStar_Ident.text_of_id op  in
               uu____6012 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6014 = levels op1  in
            (match uu____6014 with
             | (left1,mine,right1) ->
                 let uu____6024 =
                   let uu____6025 = FStar_All.pipe_left str op1  in
                   let uu____6026 = p_tmEqWith' p_X left1 e1  in
                   let uu____6027 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____6025 uu____6026 uu____6027  in
                 paren_if_gt curr mine uu____6024)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____6028;_},e1::e2::[])
            ->
            let uu____6033 =
              let uu____6034 = p_tmEqWith p_X e1  in
              let uu____6035 =
                let uu____6036 =
                  let uu____6037 =
                    let uu____6038 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____6038  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____6037  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6036  in
              FStar_Pprint.op_Hat_Hat uu____6034 uu____6035  in
            FStar_Pprint.group uu____6033
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____6039;_},e1::[])
            ->
            let uu____6043 = levels "-"  in
            (match uu____6043 with
             | (left1,mine,right1) ->
                 let uu____6053 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____6053)
        | uu____6054 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]
         in
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
            (lid,(e1,uu____6125)::(e2,uu____6127)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____6147 = is_list e  in Prims.op_Negation uu____6147)
            ->
            let op = "::"  in
            let uu____6149 = levels op  in
            (match uu____6149 with
             | (left1,mine,right1) ->
                 let uu____6159 =
                   let uu____6160 = str op  in
                   let uu____6161 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6162 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6160 uu____6161 uu____6162  in
                 paren_if_gt curr mine uu____6159)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____6170 = levels op  in
            (match uu____6170 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____6185 = p_binder false b  in
                   let uu____6186 =
                     let uu____6187 =
                       let uu____6188 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____6188 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6187
                      in
                   FStar_Pprint.op_Hat_Hat uu____6185 uu____6186  in
                 let uu____6189 =
                   let uu____6190 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____6191 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____6190 uu____6191  in
                 paren_if_gt curr mine uu____6189)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6198 = levels op1  in
            (match uu____6198 with
             | (left1,mine,right1) ->
                 let uu____6208 =
                   let uu____6209 = str op1  in
                   let uu____6210 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6211 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6209 uu____6210 uu____6211  in
                 paren_if_gt curr mine uu____6208)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____6230 =
              let uu____6231 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____6232 =
                let uu____6233 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____6233 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____6231 uu____6232  in
            braces_with_nesting uu____6230
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6238;_},e1::[])
            ->
            let uu____6242 =
              let uu____6243 = str "~"  in
              let uu____6244 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____6243 uu____6244  in
            FStar_Pprint.group uu____6242
        | uu____6245 -> p_X e

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
        let uu____6252 =
          let uu____6253 = p_lidentOrUnderscore lid  in
          let uu____6254 =
            let uu____6255 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6255  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6253 uu____6254  in
        FStar_Pprint.group uu____6252
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6258 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6260 = p_appTerm e  in
    let uu____6261 =
      let uu____6262 =
        let uu____6263 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6263 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6262  in
    FStar_Pprint.op_Hat_Hat uu____6260 uu____6261

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6268 =
            let uu____6269 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____6269 t phi  in
          soft_parens_with_nesting uu____6268
      | FStar_Parser_AST.TAnnotated uu____6270 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6275 ->
          let uu____6276 =
            let uu____6277 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6277
             in
          failwith uu____6276
      | FStar_Parser_AST.TVariable uu____6278 ->
          let uu____6279 =
            let uu____6280 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6280
             in
          failwith uu____6279
      | FStar_Parser_AST.NoName uu____6281 ->
          let uu____6282 =
            let uu____6283 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6283
             in
          failwith uu____6282

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6285  ->
      match uu____6285 with
      | (lid,e) ->
          let uu____6292 =
            let uu____6293 = p_qlident lid  in
            let uu____6294 =
              let uu____6295 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6295
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6293 uu____6294  in
          FStar_Pprint.group uu____6292

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6297 when is_general_application e ->
        let uu____6304 = head_and_args e  in
        (match uu____6304 with
         | (head1,args) ->
             let uu____6329 =
               let uu____6340 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6340
               then
                 let uu____6374 =
                   FStar_Util.take
                     (fun uu____6398  ->
                        match uu____6398 with
                        | (uu____6403,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6374 with
                 | (fs_typ_args,args1) ->
                     let uu____6441 =
                       let uu____6442 = p_indexingTerm head1  in
                       let uu____6443 =
                         let uu____6444 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6444 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6442 uu____6443  in
                     (uu____6441, args1)
               else
                 (let uu____6456 = p_indexingTerm head1  in
                  (uu____6456, args))
                in
             (match uu____6329 with
              | (head_doc,args1) ->
                  let uu____6477 =
                    let uu____6478 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6478 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6477))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6498 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6498)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6516 =
               let uu____6517 = p_quident lid  in
               let uu____6518 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6517 uu____6518  in
             FStar_Pprint.group uu____6516
         | hd1::tl1 ->
             let uu____6535 =
               let uu____6536 =
                 let uu____6537 =
                   let uu____6538 = p_quident lid  in
                   let uu____6539 = p_argTerm hd1  in
                   prefix2 uu____6538 uu____6539  in
                 FStar_Pprint.group uu____6537  in
               let uu____6540 =
                 let uu____6541 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6541  in
               FStar_Pprint.op_Hat_Hat uu____6536 uu____6540  in
             FStar_Pprint.group uu____6535)
    | uu____6546 -> p_indexingTerm e

and (p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        let uu____6554 =
          FStar_Errors.log_issue e.FStar_Parser_AST.range
            (FStar_Errors.Warning_UnexpectedFsTypApp,
              "Unexpected FsTypApp, output might not be formatted correctly.")
           in
        let uu____6555 = p_indexingTerm e  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          FStar_Pprint.langle uu____6555 FStar_Pprint.rangle
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6557 = str "#"  in
        let uu____6558 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6557 uu____6558
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6560  ->
    match uu____6560 with | (e,uu____6566) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6571;_},e1::e2::[])
          ->
          let uu____6576 =
            let uu____6577 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6578 =
              let uu____6579 =
                let uu____6580 = p_term false false e2  in
                soft_parens_with_nesting uu____6580  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6579  in
            FStar_Pprint.op_Hat_Hat uu____6577 uu____6578  in
          FStar_Pprint.group uu____6576
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6581;_},e1::e2::[])
          ->
          let uu____6586 =
            let uu____6587 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6588 =
              let uu____6589 =
                let uu____6590 = p_term false false e2  in
                soft_brackets_with_nesting uu____6590  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6589  in
            FStar_Pprint.op_Hat_Hat uu____6587 uu____6588  in
          FStar_Pprint.group uu____6586
      | uu____6591 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6596 = p_quident lid  in
        let uu____6597 =
          let uu____6598 =
            let uu____6599 = p_term false false e1  in
            soft_parens_with_nesting uu____6599  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6598  in
        FStar_Pprint.op_Hat_Hat uu____6596 uu____6597
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6605 =
          let uu____6606 = FStar_Ident.text_of_id op  in str uu____6606  in
        let uu____6607 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6605 uu____6607
    | uu____6608 -> p_atomicTermNotQUident e

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
         | uu____6615 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6622 =
          let uu____6623 = FStar_Ident.text_of_id op  in str uu____6623  in
        let uu____6624 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6622 uu____6624
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6628 =
          let uu____6629 =
            let uu____6630 =
              let uu____6631 = FStar_Ident.text_of_id op  in str uu____6631
               in
            let uu____6632 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6630 uu____6632  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6629  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6628
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6647 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6648 =
          let uu____6649 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6650 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6649 p_tmEq uu____6650  in
        let uu____6657 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6647 uu____6648 uu____6657
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6660 =
          let uu____6661 = p_atomicTermNotQUident e1  in
          let uu____6662 =
            let uu____6663 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6663  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6661 uu____6662
           in
        FStar_Pprint.group uu____6660
    | uu____6664 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6669 = p_quident constr_lid  in
        let uu____6670 =
          let uu____6671 =
            let uu____6672 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6672  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6671  in
        FStar_Pprint.op_Hat_Hat uu____6669 uu____6670
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6674 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6674 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6676 = p_term false false e1  in
        soft_parens_with_nesting uu____6676
    | uu____6677 when is_array e ->
        let es = extract_from_list e  in
        let uu____6681 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6682 =
          let uu____6683 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6683
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6686 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6681 uu____6682 uu____6686
    | uu____6687 when is_list e ->
        let uu____6688 =
          let uu____6689 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6690 = extract_from_list e  in
          separate_map_or_flow_last uu____6689
            (fun ps  -> p_noSeqTerm ps false) uu____6690
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6688 FStar_Pprint.rbracket
    | uu____6695 when is_lex_list e ->
        let uu____6696 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6697 =
          let uu____6698 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6699 = extract_from_list e  in
          separate_map_or_flow_last uu____6698
            (fun ps  -> p_noSeqTerm ps false) uu____6699
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6696 uu____6697 FStar_Pprint.rbracket
    | uu____6704 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6708 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6709 =
          let uu____6710 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6710 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6708 uu____6709 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6714 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6715 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6714 uu____6715
    | FStar_Parser_AST.Op (op,args) when
        let uu____6722 = handleable_op op args  in
        Prims.op_Negation uu____6722 ->
        let uu____6723 =
          let uu____6724 =
            let uu____6725 = FStar_Ident.text_of_id op  in
            let uu____6726 =
              let uu____6727 =
                let uu____6728 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6728
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6727  in
            Prims.strcat uu____6725 uu____6726  in
          Prims.strcat "Operation " uu____6724  in
        failwith uu____6723
    | FStar_Parser_AST.Uvar uu____6729 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6730 = p_term false false e  in
        soft_parens_with_nesting uu____6730
    | FStar_Parser_AST.Const uu____6731 ->
        let uu____6732 = p_term false false e  in
        soft_parens_with_nesting uu____6732
    | FStar_Parser_AST.Op uu____6733 ->
        let uu____6740 = p_term false false e  in
        soft_parens_with_nesting uu____6740
    | FStar_Parser_AST.Tvar uu____6741 ->
        let uu____6742 = p_term false false e  in
        soft_parens_with_nesting uu____6742
    | FStar_Parser_AST.Var uu____6743 ->
        let uu____6744 = p_term false false e  in
        soft_parens_with_nesting uu____6744
    | FStar_Parser_AST.Name uu____6745 ->
        let uu____6746 = p_term false false e  in
        soft_parens_with_nesting uu____6746
    | FStar_Parser_AST.Construct uu____6747 ->
        let uu____6758 = p_term false false e  in
        soft_parens_with_nesting uu____6758
    | FStar_Parser_AST.Abs uu____6759 ->
        let uu____6766 = p_term false false e  in
        soft_parens_with_nesting uu____6766
    | FStar_Parser_AST.App uu____6767 ->
        let uu____6774 = p_term false false e  in
        soft_parens_with_nesting uu____6774
    | FStar_Parser_AST.Let uu____6775 ->
        let uu____6796 = p_term false false e  in
        soft_parens_with_nesting uu____6796
    | FStar_Parser_AST.LetOpen uu____6797 ->
        let uu____6802 = p_term false false e  in
        soft_parens_with_nesting uu____6802
    | FStar_Parser_AST.Seq uu____6803 ->
        let uu____6808 = p_term false false e  in
        soft_parens_with_nesting uu____6808
    | FStar_Parser_AST.Bind uu____6809 ->
        let uu____6816 = p_term false false e  in
        soft_parens_with_nesting uu____6816
    | FStar_Parser_AST.If uu____6817 ->
        let uu____6824 = p_term false false e  in
        soft_parens_with_nesting uu____6824
    | FStar_Parser_AST.Match uu____6825 ->
        let uu____6840 = p_term false false e  in
        soft_parens_with_nesting uu____6840
    | FStar_Parser_AST.TryWith uu____6841 ->
        let uu____6856 = p_term false false e  in
        soft_parens_with_nesting uu____6856
    | FStar_Parser_AST.Ascribed uu____6857 ->
        let uu____6866 = p_term false false e  in
        soft_parens_with_nesting uu____6866
    | FStar_Parser_AST.Record uu____6867 ->
        let uu____6880 = p_term false false e  in
        soft_parens_with_nesting uu____6880
    | FStar_Parser_AST.Project uu____6881 ->
        let uu____6886 = p_term false false e  in
        soft_parens_with_nesting uu____6886
    | FStar_Parser_AST.Product uu____6887 ->
        let uu____6894 = p_term false false e  in
        soft_parens_with_nesting uu____6894
    | FStar_Parser_AST.Sum uu____6895 ->
        let uu____6902 = p_term false false e  in
        soft_parens_with_nesting uu____6902
    | FStar_Parser_AST.QForall uu____6903 ->
        let uu____6916 = p_term false false e  in
        soft_parens_with_nesting uu____6916
    | FStar_Parser_AST.QExists uu____6917 ->
        let uu____6930 = p_term false false e  in
        soft_parens_with_nesting uu____6930
    | FStar_Parser_AST.Refine uu____6931 ->
        let uu____6936 = p_term false false e  in
        soft_parens_with_nesting uu____6936
    | FStar_Parser_AST.NamedTyp uu____6937 ->
        let uu____6942 = p_term false false e  in
        soft_parens_with_nesting uu____6942
    | FStar_Parser_AST.Requires uu____6943 ->
        let uu____6950 = p_term false false e  in
        soft_parens_with_nesting uu____6950
    | FStar_Parser_AST.Ensures uu____6951 ->
        let uu____6958 = p_term false false e  in
        soft_parens_with_nesting uu____6958
    | FStar_Parser_AST.Attributes uu____6959 ->
        let uu____6962 = p_term false false e  in
        soft_parens_with_nesting uu____6962
    | FStar_Parser_AST.Quote uu____6963 ->
        let uu____6968 = p_term false false e  in
        soft_parens_with_nesting uu____6968
    | FStar_Parser_AST.VQuote uu____6969 ->
        let uu____6970 = p_term false false e  in
        soft_parens_with_nesting uu____6970
    | FStar_Parser_AST.Antiquote uu____6971 ->
        let uu____6976 = p_term false false e  in
        soft_parens_with_nesting uu____6976

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___69_6977  ->
    match uu___69_6977 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6981 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6981
    | FStar_Const.Const_string (s,uu____6983) ->
        let uu____6984 = str s  in FStar_Pprint.dquotes uu____6984
    | FStar_Const.Const_bytearray (bytes,uu____6986) ->
        let uu____6991 =
          let uu____6992 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6992  in
        let uu____6993 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6991 uu____6993
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___67_7012 =
          match uu___67_7012 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___68_7017 =
          match uu___68_7017 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____7028  ->
               match uu____7028 with
               | (s,w) ->
                   let uu____7035 = signedness s  in
                   let uu____7036 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____7035 uu____7036)
            sign_width_opt
           in
        let uu____7037 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____7037 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____7039 = FStar_Range.string_of_range r  in str uu____7039
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____7041 = p_quident lid  in
        let uu____7042 =
          let uu____7043 =
            let uu____7044 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____7044  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____7043  in
        FStar_Pprint.op_Hat_Hat uu____7041 uu____7042

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____7046 = str "u#"  in
    let uu____7047 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____7046 uu____7047

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7049;_},u1::u2::[])
        ->
        let uu____7054 =
          let uu____7055 = p_universeFrom u1  in
          let uu____7056 =
            let uu____7057 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____7057  in
          FStar_Pprint.op_Hat_Slash_Hat uu____7055 uu____7056  in
        FStar_Pprint.group uu____7054
    | FStar_Parser_AST.App uu____7058 ->
        let uu____7065 = head_and_args u  in
        (match uu____7065 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____7091 =
                    let uu____7092 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____7093 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____7101  ->
                           match uu____7101 with
                           | (u1,uu____7107) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____7092 uu____7093  in
                  FStar_Pprint.group uu____7091
              | uu____7108 ->
                  let uu____7109 =
                    let uu____7110 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____7110
                     in
                  failwith uu____7109))
    | uu____7111 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____7134 = FStar_Ident.text_of_id id1  in str uu____7134
    | FStar_Parser_AST.Paren u1 ->
        let uu____7136 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7136
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7137;_},uu____7138::uu____7139::[])
        ->
        let uu____7142 = p_universeFrom u  in
        soft_parens_with_nesting uu____7142
    | FStar_Parser_AST.App uu____7143 ->
        let uu____7150 = p_universeFrom u  in
        soft_parens_with_nesting uu____7150
    | uu____7151 ->
        let uu____7152 =
          let uu____7153 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7153
           in
        failwith uu____7152

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
    let uu____7184 = FStar_ST.op_Colon_Equals should_print_fs_typ_app false
       in
    let res =
      match m with
      | FStar_Parser_AST.Module (uu____7209,decls) ->
          let uu____7215 =
            FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
          FStar_All.pipe_right uu____7215
            (FStar_Pprint.separate FStar_Pprint.hardline)
      | FStar_Parser_AST.Interface (uu____7224,decls,uu____7226) ->
          let uu____7231 =
            FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
          FStar_All.pipe_right uu____7231
            (FStar_Pprint.separate FStar_Pprint.hardline)
       in
    let uu____7240 = FStar_ST.op_Colon_Equals should_print_fs_typ_app false
       in
    res
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7288  ->
         match uu____7288 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7332,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7338,decls,uu____7340) -> decls
         in
      let uu____7345 = FStar_ST.op_Colon_Equals should_print_fs_typ_app false
         in
      match decls with
      | [] -> (FStar_Pprint.empty, comments)
      | d::ds ->
          let uu____7389 =
            match ds with
            | {
                FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                  (FStar_Parser_AST.LightOff );
                FStar_Parser_AST.drange = uu____7402;
                FStar_Parser_AST.doc = uu____7403;
                FStar_Parser_AST.quals = uu____7404;
                FStar_Parser_AST.attrs = uu____7405;_}::uu____7406 ->
                let d0 = FStar_List.hd ds  in
                let uu____7412 =
                  let uu____7415 =
                    let uu____7418 = FStar_List.tl ds  in d :: uu____7418  in
                  d0 :: uu____7415  in
                (uu____7412, (d0.FStar_Parser_AST.drange))
            | uu____7423 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
          (match uu____7389 with
           | (decls1,first_range) ->
               let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
               let uu____7449 =
                 FStar_ST.op_Colon_Equals comment_stack comments  in
               let initial_comment =
                 let uu____7486 = FStar_Range.start_of_range first_range  in
                 place_comments_until_pos (Prims.parse_int "0")
                   (Prims.parse_int "1") uu____7486 FStar_Pprint.empty
                  in
               let doc1 =
                 separate_map_with_comments FStar_Pprint.empty
                   FStar_Pprint.empty decl_to_document decls1
                   extract_decl_range
                  in
               let comments1 = FStar_ST.op_Bang comment_stack  in
               let uu____7530 = FStar_ST.op_Colon_Equals comment_stack []  in
               let uu____7570 =
                 FStar_ST.op_Colon_Equals should_print_fs_typ_app false  in
               let uu____7594 = FStar_Pprint.op_Hat_Hat initial_comment doc1
                  in
               (uu____7594, comments1))
  