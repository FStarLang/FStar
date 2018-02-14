open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____19 'Auu____20 .
    Prims.bool -> ('Auu____20 -> 'Auu____19) -> 'Auu____20 -> 'Auu____19
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
  'Auu____107 'Auu____108 .
    'Auu____108 ->
      ('Auu____107 -> 'Auu____108) ->
        'Auu____107 FStar_Pervasives_Native.option -> 'Auu____108
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
  'Auu____162 .
    FStar_Pprint.document ->
      ('Auu____162 -> FStar_Pprint.document) ->
        'Auu____162 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____184 =
          let uu____185 =
            let uu____186 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____186  in
          FStar_Pprint.separate_map uu____185 f l  in
        FStar_Pprint.group uu____184
  
let precede_break_separate_map :
  'Auu____192 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____192 -> FStar_Pprint.document) ->
          'Auu____192 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____218 =
            let uu____219 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____220 =
              let uu____221 = FStar_List.hd l  in
              FStar_All.pipe_right uu____221 f  in
            FStar_Pprint.precede uu____219 uu____220  in
          let uu____222 =
            let uu____223 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____229 =
                   let uu____230 =
                     let uu____231 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____231  in
                   FStar_Pprint.op_Hat_Hat sep uu____230  in
                 FStar_Pprint.op_Hat_Hat break1 uu____229) uu____223
             in
          FStar_Pprint.op_Hat_Hat uu____218 uu____222
  
let concat_break_map :
  'Auu____235 .
    ('Auu____235 -> FStar_Pprint.document) ->
      'Auu____235 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____253 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____257 = f x  in FStar_Pprint.op_Hat_Hat uu____257 break1)
          l
         in
      FStar_Pprint.group uu____253
  
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
    let uu____279 = str "begin"  in
    let uu____280 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____279 contents uu____280
  
let separate_map_or_flow :
  'Auu____285 .
    FStar_Pprint.document ->
      ('Auu____285 -> FStar_Pprint.document) ->
        'Auu____285 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____317 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____317 -> FStar_Pprint.document) ->
                  'Auu____317 Prims.list -> FStar_Pprint.document
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
                    (let uu____362 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____362
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____372 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____372 -> FStar_Pprint.document) ->
                  'Auu____372 Prims.list -> FStar_Pprint.document
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
                    (let uu____417 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____417
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____430  ->
    match uu____430 with
    | (comment,keywords) ->
        let uu____455 =
          let uu____456 =
            let uu____459 = str comment  in
            let uu____460 =
              let uu____463 =
                let uu____466 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____475  ->
                       match uu____475 with
                       | (k,v1) ->
                           let uu____482 =
                             let uu____485 = str k  in
                             let uu____486 =
                               let uu____489 =
                                 let uu____492 = str v1  in [uu____492]  in
                               FStar_Pprint.rarrow :: uu____489  in
                             uu____485 :: uu____486  in
                           FStar_Pprint.concat uu____482) keywords
                   in
                [uu____466]  in
              FStar_Pprint.space :: uu____463  in
            uu____459 :: uu____460  in
          FStar_Pprint.concat uu____456  in
        FStar_Pprint.group uu____455
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____496 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____504 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____533::(e2,uu____535)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____558 -> false  in
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
    | FStar_Parser_AST.Construct (uu____570,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____581,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____602 = extract_from_list e2  in e1 :: uu____602
    | uu____605 ->
        let uu____606 =
          let uu____607 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____607  in
        failwith uu____606
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____614;
           FStar_Parser_AST.level = uu____615;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____617 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____623;
           FStar_Parser_AST.level = uu____624;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____626;
                                                        FStar_Parser_AST.level
                                                          = uu____627;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____629;
                                                   FStar_Parser_AST.level =
                                                     uu____630;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____632;
                FStar_Parser_AST.level = uu____633;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____635;
           FStar_Parser_AST.level = uu____636;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____638 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____646 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____647;
           FStar_Parser_AST.range = uu____648;
           FStar_Parser_AST.level = uu____649;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____650;
                                                        FStar_Parser_AST.range
                                                          = uu____651;
                                                        FStar_Parser_AST.level
                                                          = uu____652;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____654;
                                                   FStar_Parser_AST.level =
                                                     uu____655;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____656;
                FStar_Parser_AST.range = uu____657;
                FStar_Parser_AST.level = uu____658;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____660;
           FStar_Parser_AST.level = uu____661;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____663 = extract_from_ref_set e1  in
        let uu____666 = extract_from_ref_set e2  in
        FStar_List.append uu____663 uu____666
    | uu____669 ->
        let uu____670 =
          let uu____671 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____671  in
        failwith uu____670
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____677 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____677
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____681 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____681
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0")
       in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) && ((FStar_Ident.text_of_id op) <> "~"))
  
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
      | uu____748 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____762 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____766 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____770 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___51_788  ->
    match uu___51_788 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___52_805  ->
      match uu___52_805 with
      | FStar_Util.Inl c ->
          let uu____814 = FStar_String.get s (Prims.parse_int "0")  in
          uu____814 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____822 .
    Prims.string ->
      ('Auu____822,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____841  ->
      match uu____841 with
      | (assoc_levels,tokens) ->
          let uu____869 = FStar_List.tryFind (matches_token s) tokens  in
          uu____869 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____895 .
    Prims.unit ->
      (associativity,('Auu____895,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____906  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____922 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____922) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____934  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____969 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____969) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____981  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1009 .
    Prims.unit ->
      (associativity,('Auu____1009,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1020  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1036 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1036) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1048  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1076 .
    Prims.unit ->
      (associativity,('Auu____1076,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1087  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1103 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1103) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1115  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1136 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1136) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1148  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1183 .
    Prims.unit ->
      (associativity,('Auu____1183,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1194  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1210 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1210) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1222  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1243 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1243) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1255  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1276 .
    Prims.unit ->
      (associativity,('Auu____1276,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1287  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1303 .
    Prims.unit ->
      (associativity,('Auu____1303,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1314  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1330 .
    Prims.unit ->
      (associativity,('Auu____1330,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1341  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___53_1548 =
    match uu___53_1548 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1588  ->
         match uu____1588 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1668 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1668 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1718) ->
          assoc_levels
      | uu____1762 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1797 .
    ('Auu____1797,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1857 =
        FStar_List.tryFind
          (fun uu____1897  ->
             match uu____1897 with
             | (uu____1915,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1857 with
      | FStar_Pervasives_Native.Some ((uu____1957,l1,uu____1959),uu____1960)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2015 =
            let uu____2016 =
              let uu____2017 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2017  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2016
             in
          failwith uu____2015
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____2051 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2051) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2065  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2146 =
      let uu____2160 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2160 (operatorInfix0ad12 ())  in
    uu____2146 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2273 =
      let uu____2287 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2287 opinfix34  in
    uu____2273 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2353 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2353
    then (Prims.parse_int "1")
    else
      (let uu____2355 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2355
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2361 . FStar_Ident.ident -> 'Auu____2361 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_27 when _0_27 = (Prims.parse_int "0") -> true
      | _0_28 when _0_28 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
      | _0_29 when _0_29 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (FStar_List.mem (FStar_Ident.text_of_id op)
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_30 when _0_30 = (Prims.parse_int "3") ->
          FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
      | uu____2374 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2408 .
    ('Auu____2408 -> FStar_Pprint.document) ->
      'Auu____2408 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2440 = FStar_ST.op_Bang comment_stack  in
          match uu____2440 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2499 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2499
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2536 =
                    let uu____2537 =
                      let uu____2538 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2538
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2537  in
                  comments_before_pos uu____2536 print_pos lookahead_pos))
              else
                (let uu____2540 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2540))
           in
        let uu____2541 =
          let uu____2546 =
            let uu____2547 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2547  in
          let uu____2548 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2546 uu____2548  in
        match uu____2541 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2554 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2554
              else comments  in
            let uu____2560 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2560
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2573 = FStar_ST.op_Bang comment_stack  in
          match uu____2573 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2657 =
                    let uu____2658 =
                      let uu____2659 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2659  in
                    uu____2658 - lbegin  in
                  max k uu____2657  in
                let doc2 =
                  let uu____2661 =
                    let uu____2662 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2663 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2662 uu____2663  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2661  in
                let uu____2664 =
                  let uu____2665 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2665  in
                place_comments_until_pos (Prims.parse_int "1") uu____2664
                  pos_end doc2))
          | uu____2666 ->
              let lnum =
                let uu____2674 =
                  let uu____2675 = FStar_Range.line_of_pos pos_end  in
                  uu____2675 - lbegin  in
                max (Prims.parse_int "1") uu____2674  in
              let uu____2676 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2676
  
let separate_map_with_comments :
  'Auu____2683 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2683 -> FStar_Pprint.document) ->
          'Auu____2683 Prims.list ->
            ('Auu____2683 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2731 x =
              match uu____2731 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2745 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2745 doc1
                     in
                  let uu____2746 =
                    let uu____2747 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2747  in
                  let uu____2748 =
                    let uu____2749 =
                      let uu____2750 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2750  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2749  in
                  (uu____2746, uu____2748)
               in
            let uu____2751 =
              let uu____2758 = FStar_List.hd xs  in
              let uu____2759 = FStar_List.tl xs  in (uu____2758, uu____2759)
               in
            match uu____2751 with
            | (x,xs1) ->
                let init1 =
                  let uu____2775 =
                    let uu____2776 =
                      let uu____2777 = extract_range x  in
                      FStar_Range.end_of_range uu____2777  in
                    FStar_Range.line_of_pos uu____2776  in
                  let uu____2778 =
                    let uu____2779 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2779  in
                  (uu____2775, uu____2778)  in
                let uu____2780 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2780
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3095 =
      let uu____3096 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3097 =
        let uu____3098 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3099 =
          let uu____3100 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3101 =
            let uu____3102 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3102
             in
          FStar_Pprint.op_Hat_Hat uu____3100 uu____3101  in
        FStar_Pprint.op_Hat_Hat uu____3098 uu____3099  in
      FStar_Pprint.op_Hat_Hat uu____3096 uu____3097  in
    FStar_Pprint.group uu____3095

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3105 =
      let uu____3106 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3106  in
    let uu____3107 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3105 FStar_Pprint.space uu____3107
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3108  ->
    match uu____3108 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3142 =
                match uu____3142 with
                | (kwd,arg) ->
                    let uu____3149 = str "@"  in
                    let uu____3150 =
                      let uu____3151 = str kwd  in
                      let uu____3152 =
                        let uu____3153 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3153
                         in
                      FStar_Pprint.op_Hat_Hat uu____3151 uu____3152  in
                    FStar_Pprint.op_Hat_Hat uu____3149 uu____3150
                 in
              let uu____3154 =
                let uu____3155 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3155 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3154
           in
        let uu____3160 =
          let uu____3161 =
            let uu____3162 =
              let uu____3163 =
                let uu____3164 = str doc1  in
                let uu____3165 =
                  let uu____3166 =
                    let uu____3167 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3167  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3166  in
                FStar_Pprint.op_Hat_Hat uu____3164 uu____3165  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3163  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3162  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3161  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3160

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3171 =
          let uu____3172 = str "val"  in
          let uu____3173 =
            let uu____3174 =
              let uu____3175 = p_lident lid  in
              let uu____3176 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3175 uu____3176  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3174  in
          FStar_Pprint.op_Hat_Hat uu____3172 uu____3173  in
        let uu____3177 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3171 uu____3177
    | FStar_Parser_AST.TopLevelLet (uu____3178,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3203 =
               let uu____3204 = str "let"  in
               let uu____3205 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3204 uu____3205  in
             FStar_Pprint.group uu____3203) lbs
    | uu____3206 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3209 =
          let uu____3210 = str "open"  in
          let uu____3211 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3210 uu____3211  in
        FStar_Pprint.group uu____3209
    | FStar_Parser_AST.Include uid ->
        let uu____3213 =
          let uu____3214 = str "include"  in
          let uu____3215 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3214 uu____3215  in
        FStar_Pprint.group uu____3213
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3218 =
          let uu____3219 = str "module"  in
          let uu____3220 =
            let uu____3221 =
              let uu____3222 = p_uident uid1  in
              let uu____3223 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3222 uu____3223  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3221  in
          FStar_Pprint.op_Hat_Hat uu____3219 uu____3220  in
        let uu____3224 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3218 uu____3224
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3226 =
          let uu____3227 = str "module"  in
          let uu____3228 =
            let uu____3229 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3229  in
          FStar_Pprint.op_Hat_Hat uu____3227 uu____3228  in
        FStar_Pprint.group uu____3226
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3262 = str "effect"  in
          let uu____3263 =
            let uu____3264 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3264  in
          FStar_Pprint.op_Hat_Hat uu____3262 uu____3263  in
        let uu____3265 =
          let uu____3266 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3266 FStar_Pprint.equals
           in
        let uu____3267 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3265 uu____3267
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3285 = str "type"  in
        let uu____3286 = str "and"  in
        precede_break_separate_map uu____3285 uu____3286 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3308 = str "let"  in
          let uu____3309 =
            let uu____3310 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3310 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3308 uu____3309  in
        let uu____3311 =
          let uu____3312 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3312 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3311 p_letbinding lbs
          (fun uu____3320  ->
             match uu____3320 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3329 =
          let uu____3330 = str "val"  in
          let uu____3331 =
            let uu____3332 =
              let uu____3333 = p_lident lid  in
              let uu____3334 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3333 uu____3334  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3332  in
          FStar_Pprint.op_Hat_Hat uu____3330 uu____3331  in
        let uu____3335 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3329 uu____3335
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3339 =
            let uu____3340 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3340 FStar_Util.is_upper  in
          if uu____3339
          then FStar_Pprint.empty
          else
            (let uu____3342 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3342 FStar_Pprint.space)
           in
        let uu____3343 =
          let uu____3344 =
            let uu____3345 = p_ident id1  in
            let uu____3346 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3345 uu____3346  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3344  in
        let uu____3347 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3343 uu____3347
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3354 = str "exception"  in
        let uu____3355 =
          let uu____3356 =
            let uu____3357 = p_uident uid  in
            let uu____3358 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3363 = str "of"  in
                   let uu____3364 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3363 uu____3364) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3357 uu____3358  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3356  in
        FStar_Pprint.op_Hat_Hat uu____3354 uu____3355
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3366 = str "new_effect"  in
        let uu____3367 =
          let uu____3368 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3368  in
        FStar_Pprint.op_Hat_Hat uu____3366 uu____3367
    | FStar_Parser_AST.SubEffect se ->
        let uu____3370 = str "sub_effect"  in
        let uu____3371 =
          let uu____3372 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3372  in
        FStar_Pprint.op_Hat_Hat uu____3370 uu____3371
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3375 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3375 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3376 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3377) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3394  ->
    match uu___54_3394 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3396 = str "#set-options"  in
        let uu____3397 =
          let uu____3398 =
            let uu____3399 = str s  in FStar_Pprint.dquotes uu____3399  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3398  in
        FStar_Pprint.op_Hat_Hat uu____3396 uu____3397
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3403 = str "#reset-options"  in
        let uu____3404 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3408 =
                 let uu____3409 = str s  in FStar_Pprint.dquotes uu____3409
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3408) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3403 uu____3404
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
  fun uu____3433  ->
    match uu____3433 with
    | (typedecl,fsdoc_opt) ->
        let uu____3446 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3447 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3446 uu____3447

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3448  ->
    match uu___55_3448 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3463 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3479 =
          let uu____3480 = p_typ t  in prefix2 FStar_Pprint.equals uu____3480
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3524 =
          match uu____3524 with
          | (lid1,t,doc_opt) ->
              let uu____3540 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3540
           in
        let p_fields uu____3554 =
          let uu____3555 =
            let uu____3556 =
              let uu____3557 =
                let uu____3558 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3558 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3557  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3556  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3555  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3622 =
          match uu____3622 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3648 =
                  let uu____3649 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3649  in
                FStar_Range.extend_to_end_of_line uu____3648  in
              let p_constructorBranch decl =
                let uu____3682 =
                  let uu____3683 =
                    let uu____3684 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3684  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3683  in
                FStar_Pprint.group uu____3682  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3704 =
          let uu____3705 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3705  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3720  ->
             let uu____3721 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3721)

and (p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document)
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____3736 = p_ident lid  in
            let uu____3737 =
              let uu____3738 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3738  in
            FStar_Pprint.op_Hat_Hat uu____3736 uu____3737
          else
            (let binders_doc =
               let uu____3741 = p_typars bs  in
               let uu____3742 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3746 =
                        let uu____3747 =
                          let uu____3748 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3748
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3747
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3746) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3741 uu____3742  in
             let uu____3749 = p_ident lid  in
             let uu____3750 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3749 binders_doc uu____3750)

and (p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun uu____3751  ->
    match uu____3751 with
    | (lid,t,doc_opt) ->
        let uu____3767 =
          let uu____3768 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____3769 =
            let uu____3770 = p_lident lid  in
            let uu____3771 =
              let uu____3772 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3772  in
            FStar_Pprint.op_Hat_Hat uu____3770 uu____3771  in
          FStar_Pprint.op_Hat_Hat uu____3768 uu____3769  in
        FStar_Pprint.group uu____3767

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____3773  ->
    match uu____3773 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3801 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3802 =
          let uu____3803 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3804 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3809 =
                   let uu____3810 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3810  in
                 let uu____3811 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____3809 uu____3811) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3803 uu____3804  in
        FStar_Pprint.op_Hat_Hat uu____3801 uu____3802

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3812  ->
    match uu____3812 with
    | (pat,uu____3818) ->
        let uu____3819 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3830 =
                let uu____3831 =
                  let uu____3832 =
                    let uu____3833 =
                      let uu____3834 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3834
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3833  in
                  FStar_Pprint.group uu____3832  in
                FStar_Pprint.op_Hat_Hat break1 uu____3831  in
              (pat1, uu____3830)
          | uu____3835 -> (pat, FStar_Pprint.empty)  in
        (match uu____3819 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3839);
                     FStar_Parser_AST.prange = uu____3840;_},pats)
                  ->
                  let uu____3850 =
                    let uu____3851 = p_lident x  in
                    let uu____3852 =
                      let uu____3853 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____3853 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3851 uu____3852  in
                  FStar_Pprint.group uu____3850
              | uu____3854 ->
                  let uu____3855 =
                    let uu____3856 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____3856 ascr_doc  in
                  FStar_Pprint.group uu____3855))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3857  ->
    match uu____3857 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____3865 =
          let uu____3866 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____3866  in
        let uu____3867 = p_term e  in prefix2 uu____3865 uu____3867

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_3868  ->
    match uu___56_3868 with
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
        let uu____3893 = p_uident uid  in
        let uu____3894 = p_binders true bs  in
        let uu____3895 =
          let uu____3896 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____3896  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3893 uu____3894 uu____3895

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
          let uu____3905 =
            let uu____3906 =
              let uu____3907 =
                let uu____3908 = p_uident uid  in
                let uu____3909 = p_binders true bs  in
                let uu____3910 =
                  let uu____3911 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____3911  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3908 uu____3909 uu____3910
                 in
              FStar_Pprint.group uu____3907  in
            let uu____3912 =
              let uu____3913 = str "with"  in
              let uu____3914 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____3913 uu____3914  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3906 uu____3912  in
          braces_with_nesting uu____3905

and (p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3944 =
          let uu____3945 = p_lident lid  in
          let uu____3946 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____3945 uu____3946  in
        let uu____3947 = p_simpleTerm e  in prefix2 uu____3944 uu____3947
    | uu____3948 ->
        let uu____3949 =
          let uu____3950 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3950
           in
        failwith uu____3949

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____4005 =
        match uu____4005 with
        | (kwd,t) ->
            let uu____4012 =
              let uu____4013 = str kwd  in
              let uu____4014 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4013 uu____4014  in
            let uu____4015 = p_simpleTerm t  in prefix2 uu____4012 uu____4015
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____4020 =
      let uu____4021 =
        let uu____4022 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4023 =
          let uu____4024 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4024  in
        FStar_Pprint.op_Hat_Hat uu____4022 uu____4023  in
      let uu____4025 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4021 uu____4025  in
    let uu____4026 =
      let uu____4027 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4027  in
    FStar_Pprint.op_Hat_Hat uu____4020 uu____4026

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4028  ->
    match uu___57_4028 with
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
    let uu____4030 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4030

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4031  ->
    match uu___58_4031 with
    | FStar_Parser_AST.Rec  ->
        let uu____4032 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4032
    | FStar_Parser_AST.Mutable  ->
        let uu____4033 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4033
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4034  ->
    match uu___59_4034 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4039 =
          let uu____4040 =
            let uu____4041 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4041  in
          FStar_Pprint.separate_map uu____4040 p_tuplePattern pats  in
        FStar_Pprint.group uu____4039
    | uu____4042 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4049 =
          let uu____4050 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4050 p_constructorPattern pats  in
        FStar_Pprint.group uu____4049
    | uu____4051 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4054;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4059 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4060 = p_constructorPattern hd1  in
        let uu____4061 = p_constructorPattern tl1  in
        infix0 uu____4059 uu____4060 uu____4061
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4063;_},pats)
        ->
        let uu____4069 = p_quident uid  in
        let uu____4070 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4069 uu____4070
    | uu____4071 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4079;
               FStar_Parser_AST.blevel = uu____4080;
               FStar_Parser_AST.aqual = uu____4081;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4087 =
               let uu____4088 = p_ident lid  in
               p_refinement aqual uu____4088 t1 phi  in
             soft_parens_with_nesting uu____4087
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4090;
               FStar_Parser_AST.blevel = uu____4091;
               FStar_Parser_AST.aqual = uu____4092;_},phi))
             ->
             let uu____4094 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4094
         | uu____4095 ->
             let uu____4100 =
               let uu____4101 = p_tuplePattern pat  in
               let uu____4102 =
                 let uu____4103 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4104 =
                   let uu____4105 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4105  in
                 FStar_Pprint.op_Hat_Hat uu____4103 uu____4104  in
               FStar_Pprint.op_Hat_Hat uu____4101 uu____4102  in
             soft_parens_with_nesting uu____4100)
    | FStar_Parser_AST.PatList pats ->
        let uu____4109 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4109 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4124 =
          match uu____4124 with
          | (lid,pat) ->
              let uu____4131 = p_qlident lid  in
              let uu____4132 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4131 uu____4132
           in
        let uu____4133 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4133
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4143 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4144 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4145 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4143 uu____4144 uu____4145
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4156 =
          let uu____4157 =
            let uu____4158 = str (FStar_Ident.text_of_id op)  in
            let uu____4159 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4158 uu____4159  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4157  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4156
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4167 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4168 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4167 uu____4168
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4170 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4173;
           FStar_Parser_AST.prange = uu____4174;_},uu____4175)
        ->
        let uu____4180 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4180
    | FStar_Parser_AST.PatTuple (uu____4181,false ) ->
        let uu____4186 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4186
    | uu____4187 ->
        let uu____4188 =
          let uu____4189 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4189  in
        failwith uu____4188

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4193 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4194 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4193 uu____4194
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4201;
                   FStar_Parser_AST.blevel = uu____4202;
                   FStar_Parser_AST.aqual = uu____4203;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4205 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4205 t1 phi
            | uu____4206 ->
                let uu____4207 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4208 =
                  let uu____4209 = p_lident lid  in
                  let uu____4210 =
                    let uu____4211 =
                      let uu____4212 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4213 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4212 uu____4213  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4211  in
                  FStar_Pprint.op_Hat_Hat uu____4209 uu____4210  in
                FStar_Pprint.op_Hat_Hat uu____4207 uu____4208
             in
          if is_atomic
          then
            let uu____4214 =
              let uu____4215 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4215  in
            FStar_Pprint.group uu____4214
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4217 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4224;
                  FStar_Parser_AST.blevel = uu____4225;
                  FStar_Parser_AST.aqual = uu____4226;_},phi)
               ->
               if is_atomic
               then
                 let uu____4228 =
                   let uu____4229 =
                     let uu____4230 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4230 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4229  in
                 FStar_Pprint.group uu____4228
               else
                 (let uu____4232 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4232)
           | uu____4233 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4241 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4242 =
            let uu____4243 =
              let uu____4244 =
                let uu____4245 = p_appTerm t  in
                let uu____4246 =
                  let uu____4247 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____4247  in
                FStar_Pprint.op_Hat_Hat uu____4245 uu____4246  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4244  in
            FStar_Pprint.op_Hat_Hat binder uu____4243  in
          FStar_Pprint.op_Hat_Hat uu____4241 uu____4242

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and (p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1

and (p_term : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4263 =
          let uu____4264 =
            let uu____4265 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4265 FStar_Pprint.semi  in
          FStar_Pprint.group uu____4264  in
        let uu____4266 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4263 uu____4266
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4270 =
          let uu____4271 =
            let uu____4272 =
              let uu____4273 = p_lident x  in
              let uu____4274 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____4273 uu____4274  in
            let uu____4275 =
              let uu____4276 = p_noSeqTerm e1  in
              let uu____4277 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____4276 uu____4277  in
            op_Hat_Slash_Plus_Hat uu____4272 uu____4275  in
          FStar_Pprint.group uu____4271  in
        let uu____4278 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4270 uu____4278
    | uu____4279 ->
        let uu____4280 = p_noSeqTerm e  in FStar_Pprint.group uu____4280

and (p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and (p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4287 =
          let uu____4288 = p_tmIff e1  in
          let uu____4289 =
            let uu____4290 =
              let uu____4291 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4291  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4290  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4288 uu____4289  in
        FStar_Pprint.group uu____4287
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4297 =
          let uu____4298 = p_tmIff e1  in
          let uu____4299 =
            let uu____4300 =
              let uu____4301 =
                let uu____4302 = p_typ t  in
                let uu____4303 =
                  let uu____4304 = str "by"  in
                  let uu____4305 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4304 uu____4305  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4302 uu____4303  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4301  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4300  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4298 uu____4299  in
        FStar_Pprint.group uu____4297
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4306;_},e1::e2::e3::[])
        ->
        let uu____4312 =
          let uu____4313 =
            let uu____4314 =
              let uu____4315 = p_atomicTermNotQUident e1  in
              let uu____4316 =
                let uu____4317 =
                  let uu____4318 =
                    let uu____4319 = p_term e2  in
                    soft_parens_with_nesting uu____4319  in
                  let uu____4320 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4318 uu____4320  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4317  in
              FStar_Pprint.op_Hat_Hat uu____4315 uu____4316  in
            FStar_Pprint.group uu____4314  in
          let uu____4321 =
            let uu____4322 = p_noSeqTerm e3  in jump2 uu____4322  in
          FStar_Pprint.op_Hat_Hat uu____4313 uu____4321  in
        FStar_Pprint.group uu____4312
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4323;_},e1::e2::e3::[])
        ->
        let uu____4329 =
          let uu____4330 =
            let uu____4331 =
              let uu____4332 = p_atomicTermNotQUident e1  in
              let uu____4333 =
                let uu____4334 =
                  let uu____4335 =
                    let uu____4336 = p_term e2  in
                    soft_brackets_with_nesting uu____4336  in
                  let uu____4337 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4335 uu____4337  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4334  in
              FStar_Pprint.op_Hat_Hat uu____4332 uu____4333  in
            FStar_Pprint.group uu____4331  in
          let uu____4338 =
            let uu____4339 = p_noSeqTerm e3  in jump2 uu____4339  in
          FStar_Pprint.op_Hat_Hat uu____4330 uu____4338  in
        FStar_Pprint.group uu____4329
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4349 =
          let uu____4350 = str "requires"  in
          let uu____4351 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4350 uu____4351  in
        FStar_Pprint.group uu____4349
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4361 =
          let uu____4362 = str "ensures"  in
          let uu____4363 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4362 uu____4363  in
        FStar_Pprint.group uu____4361
    | FStar_Parser_AST.Attributes es ->
        let uu____4367 =
          let uu____4368 = str "attributes"  in
          let uu____4369 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4368 uu____4369  in
        FStar_Pprint.group uu____4367
    | FStar_Parser_AST.If (e1,e2,e3) ->
        if is_unit e3
        then
          let uu____4373 =
            let uu____4374 =
              let uu____4375 = str "if"  in
              let uu____4376 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4375 uu____4376  in
            let uu____4377 =
              let uu____4378 = str "then"  in
              let uu____4379 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4378 uu____4379  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4374 uu____4377  in
          FStar_Pprint.group uu____4373
        else
          (let e2_doc =
             match e2.FStar_Parser_AST.tm with
             | FStar_Parser_AST.If (uu____4382,uu____4383,e31) when
                 is_unit e31 ->
                 let uu____4385 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4385
             | uu____4386 -> p_noSeqTerm e2  in
           let uu____4387 =
             let uu____4388 =
               let uu____4389 = str "if"  in
               let uu____4390 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4389 uu____4390  in
             let uu____4391 =
               let uu____4392 =
                 let uu____4393 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4393 e2_doc  in
               let uu____4394 =
                 let uu____4395 = str "else"  in
                 let uu____4396 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4395 uu____4396  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4392 uu____4394  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4388 uu____4391  in
           FStar_Pprint.group uu____4387)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4419 =
          let uu____4420 =
            let uu____4421 = str "try"  in
            let uu____4422 = p_noSeqTerm e1  in prefix2 uu____4421 uu____4422
             in
          let uu____4423 =
            let uu____4424 = str "with"  in
            let uu____4425 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4424 uu____4425  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4420 uu____4423  in
        FStar_Pprint.group uu____4419
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4456 =
          let uu____4457 =
            let uu____4458 = str "match"  in
            let uu____4459 = p_noSeqTerm e1  in
            let uu____4460 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4458 uu____4459 uu____4460
             in
          let uu____4461 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4457 uu____4461  in
        FStar_Pprint.group uu____4456
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4472 =
          let uu____4473 =
            let uu____4474 = str "let open"  in
            let uu____4475 = p_quident uid  in
            let uu____4476 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4474 uu____4475 uu____4476
             in
          let uu____4477 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4473 uu____4477  in
        FStar_Pprint.group uu____4472
    | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
        let let_first =
          let uu____4540 = p_attrs_opt a0  in
          let uu____4541 =
            let uu____4542 =
              let uu____4543 = str "let"  in
              let uu____4544 =
                let uu____4545 = p_letqualifier q  in
                let uu____4546 = p_letbinding lb0  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4545 uu____4546  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4543 uu____4544  in
            FStar_Pprint.group uu____4542  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4540 uu____4541  in
        let let_rest =
          match attr_letbindings with
          | [] -> FStar_Pprint.empty
          | uu____4560 ->
              let uu____4575 =
                precede_break_separate_map FStar_Pprint.empty
                  FStar_Pprint.empty p_attr_letbinding attr_letbindings
                 in
              FStar_Pprint.group uu____4575
           in
        let uu____4588 =
          let uu____4589 =
            let uu____4590 = str "in"  in
            let uu____4591 = p_term e1  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4590 uu____4591  in
          FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4589  in
        FStar_Pprint.op_Hat_Slash_Hat let_first uu____4588
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4594;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4597;
                                                         FStar_Parser_AST.level
                                                           = uu____4598;_})
        when matches_var maybe_x x ->
        let uu____4625 =
          let uu____4626 = str "function"  in
          let uu____4627 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4626 uu____4627  in
        FStar_Pprint.group uu____4625
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4638 =
          let uu____4639 = p_lident id1  in
          let uu____4640 =
            let uu____4641 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4641  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4639 uu____4640  in
        FStar_Pprint.group uu____4638
    | uu____4642 -> p_typ e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_4643  ->
    match uu___60_4643 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4655 =
          let uu____4656 = str "[@"  in
          let uu____4657 =
            let uu____4658 =
              FStar_Pprint.separate_map FStar_Pprint.semi p_term terms  in
            let uu____4659 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4658 uu____4659  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4656 uu____4657  in
        FStar_Pprint.group uu____4655

and (p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4660  ->
    match uu____4660 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4689 =
          let uu____4690 = p_attrs_opt a  in
          let uu____4691 =
            let uu____4692 =
              let uu____4693 = str "and "  in
              let uu____4694 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4693 uu____4694  in
            FStar_Pprint.group uu____4692  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4690 uu____4691  in
        let uu____4695 = p_term e  in prefix2 uu____4689 uu____4695

and (p_typ : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and (p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4713 =
          let uu____4714 =
            let uu____4715 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4715 FStar_Pprint.space  in
          let uu____4716 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4714 uu____4716 FStar_Pprint.dot
           in
        let uu____4717 =
          let uu____4718 = p_trigger trigger  in
          let uu____4719 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4718 uu____4719  in
        prefix2 uu____4713 uu____4717
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4735 =
          let uu____4736 =
            let uu____4737 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4737 FStar_Pprint.space  in
          let uu____4738 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4736 uu____4738 FStar_Pprint.dot
           in
        let uu____4739 =
          let uu____4740 = p_trigger trigger  in
          let uu____4741 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4740 uu____4741  in
        prefix2 uu____4735 uu____4739
    | uu____4742 -> p_simpleTerm e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____4744 -> str "forall"
    | FStar_Parser_AST.QExists uu____4757 -> str "exists"
    | uu____4770 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_4771  ->
    match uu___61_4771 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4783 =
          let uu____4784 =
            let uu____4785 = str "pattern"  in
            let uu____4786 =
              let uu____4787 =
                let uu____4788 = p_disjunctivePats pats  in jump2 uu____4788
                 in
              let uu____4789 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4787 uu____4789  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4785 uu____4786  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4784  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4783

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____4795 = str "\\/"  in
    FStar_Pprint.separate_map uu____4795 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____4801 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4801

and (p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4809 =
          let uu____4810 = str "fun"  in
          let uu____4811 =
            let uu____4812 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4812 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4810 uu____4811  in
        let uu____4813 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4809 uu____4813
    | uu____4814 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun uu____4817  ->
    match uu____4817 with
    | (pat,when_opt,e) ->
        let uu____4833 =
          let uu____4834 =
            let uu____4835 =
              let uu____4836 =
                let uu____4837 =
                  let uu____4838 = p_disjunctivePattern pat  in
                  let uu____4839 =
                    let uu____4840 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____4840 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____4838 uu____4839  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4837  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4836  in
            FStar_Pprint.group uu____4835  in
          let uu____4841 = p_term e  in
          op_Hat_Slash_Plus_Hat uu____4834 uu____4841  in
        FStar_Pprint.group uu____4833

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_4842  ->
    match uu___62_4842 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4846 = str "when"  in
        let uu____4847 =
          let uu____4848 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____4848 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____4846 uu____4847

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4850;_},e1::e2::[])
        ->
        let uu____4855 = str "<==>"  in
        let uu____4856 = p_tmImplies e1  in
        let uu____4857 = p_tmIff e2  in
        infix0 uu____4855 uu____4856 uu____4857
    | uu____4858 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4860;_},e1::e2::[])
        ->
        let uu____4865 = str "==>"  in
        let uu____4866 = p_tmArrow p_tmFormula e1  in
        let uu____4867 = p_tmImplies e2  in
        infix0 uu____4865 uu____4866 uu____4867
    | uu____4868 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4879 =
            let uu____4880 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4885 = p_binder false b  in
                   let uu____4886 =
                     let uu____4887 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4887
                      in
                   FStar_Pprint.op_Hat_Hat uu____4885 uu____4886) bs
               in
            let uu____4888 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____4880 uu____4888  in
          FStar_Pprint.group uu____4879
      | uu____4889 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4891;_},e1::e2::[])
        ->
        let uu____4896 = str "\\/"  in
        let uu____4897 = p_tmFormula e1  in
        let uu____4898 = p_tmConjunction e2  in
        infix0 uu____4896 uu____4897 uu____4898
    | uu____4899 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4901;_},e1::e2::[])
        ->
        let uu____4906 = str "/\\"  in
        let uu____4907 = p_tmConjunction e1  in
        let uu____4908 = p_tmTuple e2  in
        infix0 uu____4906 uu____4907 uu____4908
    | uu____4909 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4926 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____4926
          (fun uu____4934  ->
             match uu____4934 with | (e1,uu____4940) -> p_tmEq e1) args
    | uu____4941 -> p_tmEq e

and (paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4946 =
             let uu____4947 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4947  in
           FStar_Pprint.group uu____4946)

and (p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ()))
       in
    p_tmEq' n1 e

and (p_tmEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun curr  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5004 = levels op1  in
          (match uu____5004 with
           | (left1,mine,right1) ->
               let uu____5014 =
                 let uu____5015 = FStar_All.pipe_left str op1  in
                 let uu____5016 = p_tmEq' left1 e1  in
                 let uu____5017 = p_tmEq' right1 e2  in
                 infix0 uu____5015 uu____5016 uu____5017  in
               paren_if curr mine uu____5014)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5018;_},e1::e2::[])
          ->
          let uu____5023 =
            let uu____5024 = p_tmEq e1  in
            let uu____5025 =
              let uu____5026 =
                let uu____5027 =
                  let uu____5028 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5028  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5027  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5026  in
            FStar_Pprint.op_Hat_Hat uu____5024 uu____5025  in
          FStar_Pprint.group uu____5023
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5029;_},e1::[])
          ->
          let uu____5033 = levels "-"  in
          (match uu____5033 with
           | (left1,mine,right1) ->
               let uu____5043 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5043)
      | uu____5044 -> p_tmNoEq e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and (p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun curr  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5109)::(e2,uu____5111)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5131 = is_list e  in Prims.op_Negation uu____5131)
          ->
          let op = "::"  in
          let uu____5133 = levels op  in
          (match uu____5133 with
           | (left1,mine,right1) ->
               let uu____5143 =
                 let uu____5144 = str op  in
                 let uu____5145 = p_tmNoEq' left1 e1  in
                 let uu____5146 = p_tmNoEq' right1 e2  in
                 infix0 uu____5144 uu____5145 uu____5146  in
               paren_if curr mine uu____5143)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5154 = levels op  in
          (match uu____5154 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5168 = p_binder false b  in
                 let uu____5169 =
                   let uu____5170 =
                     let uu____5171 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5171 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5170  in
                 FStar_Pprint.op_Hat_Hat uu____5168 uu____5169  in
               let uu____5172 =
                 let uu____5173 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5174 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5173 uu____5174  in
               paren_if curr mine uu____5172)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5181 = levels op1  in
          (match uu____5181 with
           | (left1,mine,right1) ->
               let uu____5191 =
                 let uu____5192 = str op1  in
                 let uu____5193 = p_tmNoEq' left1 e1  in
                 let uu____5194 = p_tmNoEq' right1 e2  in
                 infix0 uu____5192 uu____5193 uu____5194  in
               paren_if curr mine uu____5191)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5197 =
            let uu____5198 = p_lidentOrUnderscore lid  in
            let uu____5199 =
              let uu____5200 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5200  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5198 uu____5199  in
          FStar_Pprint.group uu____5197
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5221 =
            let uu____5222 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5223 =
              let uu____5224 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____5224 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____5222 uu____5223  in
          braces_with_nesting uu____5221
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5229;_},e1::[])
          ->
          let uu____5233 =
            let uu____5234 = str "~"  in
            let uu____5235 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5234 uu____5235  in
          FStar_Pprint.group uu____5233
      | uu____5236 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5238 = p_appTerm e  in
    let uu____5239 =
      let uu____5240 =
        let uu____5241 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5241 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5240  in
    FStar_Pprint.op_Hat_Hat uu____5238 uu____5239

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5246 =
            let uu____5247 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5247 t phi  in
          soft_parens_with_nesting uu____5246
      | FStar_Parser_AST.TAnnotated uu____5248 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5253 ->
          let uu____5254 =
            let uu____5255 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5255
             in
          failwith uu____5254
      | FStar_Parser_AST.TVariable uu____5256 ->
          let uu____5257 =
            let uu____5258 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5258
             in
          failwith uu____5257
      | FStar_Parser_AST.NoName uu____5259 ->
          let uu____5260 =
            let uu____5261 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5261
             in
          failwith uu____5260

and (p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document)
  =
  fun uu____5262  ->
    match uu____5262 with
    | (lid,e) ->
        let uu____5269 =
          let uu____5270 = p_qlident lid  in
          let uu____5271 =
            let uu____5272 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5272  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5270 uu____5271  in
        FStar_Pprint.group uu____5269

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5274 when is_general_application e ->
        let uu____5281 = head_and_args e  in
        (match uu____5281 with
         | (head1,args) ->
             let uu____5306 =
               let uu____5317 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5317
               then
                 let uu____5347 =
                   FStar_Util.take
                     (fun uu____5371  ->
                        match uu____5371 with
                        | (uu____5376,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5347 with
                 | (fs_typ_args,args1) ->
                     let uu____5414 =
                       let uu____5415 = p_indexingTerm head1  in
                       let uu____5416 =
                         let uu____5417 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5417 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5415 uu____5416  in
                     (uu____5414, args1)
               else
                 (let uu____5429 = p_indexingTerm head1  in
                  (uu____5429, args))
                in
             (match uu____5306 with
              | (head_doc,args1) ->
                  let uu____5450 =
                    let uu____5451 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5451 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5450))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5471 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5471)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5489 =
               let uu____5490 = p_quident lid  in
               let uu____5491 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5490 uu____5491  in
             FStar_Pprint.group uu____5489
         | hd1::tl1 ->
             let uu____5508 =
               let uu____5509 =
                 let uu____5510 =
                   let uu____5511 = p_quident lid  in
                   let uu____5512 = p_argTerm hd1  in
                   prefix2 uu____5511 uu____5512  in
                 FStar_Pprint.group uu____5510  in
               let uu____5513 =
                 let uu____5514 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5514  in
               FStar_Pprint.op_Hat_Hat uu____5509 uu____5513  in
             FStar_Pprint.group uu____5508)
    | uu____5519 -> p_indexingTerm e

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
         (let uu____5528 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5528 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5530 = str "#"  in
        let uu____5531 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5530 uu____5531
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5533  ->
    match uu____5533 with | (e,uu____5539) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5544;_},e1::e2::[])
          ->
          let uu____5549 =
            let uu____5550 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5551 =
              let uu____5552 =
                let uu____5553 = p_term e2  in
                soft_parens_with_nesting uu____5553  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5552  in
            FStar_Pprint.op_Hat_Hat uu____5550 uu____5551  in
          FStar_Pprint.group uu____5549
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5554;_},e1::e2::[])
          ->
          let uu____5559 =
            let uu____5560 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5561 =
              let uu____5562 =
                let uu____5563 = p_term e2  in
                soft_brackets_with_nesting uu____5563  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5562  in
            FStar_Pprint.op_Hat_Hat uu____5560 uu____5561  in
          FStar_Pprint.group uu____5559
      | uu____5564 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5569 = p_quident lid  in
        let uu____5570 =
          let uu____5571 =
            let uu____5572 = p_term e1  in
            soft_parens_with_nesting uu____5572  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5571  in
        FStar_Pprint.op_Hat_Hat uu____5569 uu____5570
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5578 = str (FStar_Ident.text_of_id op)  in
        let uu____5579 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5578 uu____5579
    | uu____5580 -> p_atomicTermNotQUident e

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
         | uu____5587 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5594 = str (FStar_Ident.text_of_id op)  in
        let uu____5595 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5594 uu____5595
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5599 =
          let uu____5600 =
            let uu____5601 = str (FStar_Ident.text_of_id op)  in
            let uu____5602 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5601 uu____5602  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5600  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5599
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5617 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5618 =
          let uu____5619 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5620 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5619 p_tmEq uu____5620  in
        let uu____5627 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5617 uu____5618 uu____5627
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5630 =
          let uu____5631 = p_atomicTermNotQUident e1  in
          let uu____5632 =
            let uu____5633 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5633  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5631 uu____5632
           in
        FStar_Pprint.group uu____5630
    | uu____5634 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5639 = p_quident constr_lid  in
        let uu____5640 =
          let uu____5641 =
            let uu____5642 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5642  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5641  in
        FStar_Pprint.op_Hat_Hat uu____5639 uu____5640
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5644 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5644 FStar_Pprint.qmark
    | uu____5645 when is_array e ->
        let es = extract_from_list e  in
        let uu____5649 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5650 =
          let uu____5651 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5651 p_noSeqTerm es  in
        let uu____5652 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5649 uu____5650 uu____5652
    | uu____5653 when is_list e ->
        let uu____5654 =
          let uu____5655 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5656 = extract_from_list e  in
          separate_map_or_flow uu____5655 p_noSeqTerm uu____5656  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5654 FStar_Pprint.rbracket
    | uu____5659 when is_lex_list e ->
        let uu____5660 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5661 =
          let uu____5662 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5663 = extract_from_list e  in
          separate_map_or_flow uu____5662 p_noSeqTerm uu____5663  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5660 uu____5661 FStar_Pprint.rbracket
    | uu____5666 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5670 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5671 =
          let uu____5672 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5672 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5670 uu____5671 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5676 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5677 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5676 uu____5677
    | FStar_Parser_AST.Op (op,args) when
        let uu____5684 = handleable_op op args  in
        Prims.op_Negation uu____5684 ->
        let uu____5685 =
          let uu____5686 =
            let uu____5687 =
              let uu____5688 =
                let uu____5689 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5689
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5688  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5687  in
          Prims.strcat "Operation " uu____5686  in
        failwith uu____5685
    | FStar_Parser_AST.Uvar uu____5690 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5691 = p_term e  in soft_parens_with_nesting uu____5691
    | FStar_Parser_AST.Const uu____5692 ->
        let uu____5693 = p_term e  in soft_parens_with_nesting uu____5693
    | FStar_Parser_AST.Op uu____5694 ->
        let uu____5701 = p_term e  in soft_parens_with_nesting uu____5701
    | FStar_Parser_AST.Tvar uu____5702 ->
        let uu____5703 = p_term e  in soft_parens_with_nesting uu____5703
    | FStar_Parser_AST.Var uu____5704 ->
        let uu____5705 = p_term e  in soft_parens_with_nesting uu____5705
    | FStar_Parser_AST.Name uu____5706 ->
        let uu____5707 = p_term e  in soft_parens_with_nesting uu____5707
    | FStar_Parser_AST.Construct uu____5708 ->
        let uu____5719 = p_term e  in soft_parens_with_nesting uu____5719
    | FStar_Parser_AST.Abs uu____5720 ->
        let uu____5727 = p_term e  in soft_parens_with_nesting uu____5727
    | FStar_Parser_AST.App uu____5728 ->
        let uu____5735 = p_term e  in soft_parens_with_nesting uu____5735
    | FStar_Parser_AST.Let uu____5736 ->
        let uu____5757 = p_term e  in soft_parens_with_nesting uu____5757
    | FStar_Parser_AST.LetOpen uu____5758 ->
        let uu____5763 = p_term e  in soft_parens_with_nesting uu____5763
    | FStar_Parser_AST.Seq uu____5764 ->
        let uu____5769 = p_term e  in soft_parens_with_nesting uu____5769
    | FStar_Parser_AST.Bind uu____5770 ->
        let uu____5777 = p_term e  in soft_parens_with_nesting uu____5777
    | FStar_Parser_AST.If uu____5778 ->
        let uu____5785 = p_term e  in soft_parens_with_nesting uu____5785
    | FStar_Parser_AST.Match uu____5786 ->
        let uu____5801 = p_term e  in soft_parens_with_nesting uu____5801
    | FStar_Parser_AST.TryWith uu____5802 ->
        let uu____5817 = p_term e  in soft_parens_with_nesting uu____5817
    | FStar_Parser_AST.Ascribed uu____5818 ->
        let uu____5827 = p_term e  in soft_parens_with_nesting uu____5827
    | FStar_Parser_AST.Record uu____5828 ->
        let uu____5841 = p_term e  in soft_parens_with_nesting uu____5841
    | FStar_Parser_AST.Project uu____5842 ->
        let uu____5847 = p_term e  in soft_parens_with_nesting uu____5847
    | FStar_Parser_AST.Product uu____5848 ->
        let uu____5855 = p_term e  in soft_parens_with_nesting uu____5855
    | FStar_Parser_AST.Sum uu____5856 ->
        let uu____5863 = p_term e  in soft_parens_with_nesting uu____5863
    | FStar_Parser_AST.QForall uu____5864 ->
        let uu____5877 = p_term e  in soft_parens_with_nesting uu____5877
    | FStar_Parser_AST.QExists uu____5878 ->
        let uu____5891 = p_term e  in soft_parens_with_nesting uu____5891
    | FStar_Parser_AST.Refine uu____5892 ->
        let uu____5897 = p_term e  in soft_parens_with_nesting uu____5897
    | FStar_Parser_AST.NamedTyp uu____5898 ->
        let uu____5903 = p_term e  in soft_parens_with_nesting uu____5903
    | FStar_Parser_AST.Requires uu____5904 ->
        let uu____5911 = p_term e  in soft_parens_with_nesting uu____5911
    | FStar_Parser_AST.Ensures uu____5912 ->
        let uu____5919 = p_term e  in soft_parens_with_nesting uu____5919
    | FStar_Parser_AST.Assign uu____5920 ->
        let uu____5925 = p_term e  in soft_parens_with_nesting uu____5925
    | FStar_Parser_AST.Attributes uu____5926 ->
        let uu____5929 = p_term e  in soft_parens_with_nesting uu____5929

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_5930  ->
    match uu___65_5930 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5934 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____5934
    | FStar_Const.Const_string (s,uu____5936) ->
        let uu____5937 = str s  in FStar_Pprint.dquotes uu____5937
    | FStar_Const.Const_bytearray (bytes,uu____5939) ->
        let uu____5944 =
          let uu____5945 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____5945  in
        let uu____5946 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____5944 uu____5946
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_5964 =
          match uu___63_5964 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_5968 =
          match uu___64_5968 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5979  ->
               match uu____5979 with
               | (s,w) ->
                   let uu____5986 = signedness s  in
                   let uu____5987 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____5986 uu____5987)
            sign_width_opt
           in
        let uu____5988 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____5988 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____5990 = FStar_Range.string_of_range r  in str uu____5990
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5992 = p_quident lid  in
        let uu____5993 =
          let uu____5994 =
            let uu____5995 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5995  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5994  in
        FStar_Pprint.op_Hat_Hat uu____5992 uu____5993

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____5997 = str "u#"  in
    let uu____5998 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____5997 uu____5998

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6000;_},u1::u2::[])
        ->
        let uu____6005 =
          let uu____6006 = p_universeFrom u1  in
          let uu____6007 =
            let uu____6008 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6008  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6006 uu____6007  in
        FStar_Pprint.group uu____6005
    | FStar_Parser_AST.App uu____6009 ->
        let uu____6016 = head_and_args u  in
        (match uu____6016 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6042 =
                    let uu____6043 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6044 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6052  ->
                           match uu____6052 with
                           | (u1,uu____6058) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6043 uu____6044  in
                  FStar_Pprint.group uu____6042
              | uu____6059 ->
                  let uu____6060 =
                    let uu____6061 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6061
                     in
                  failwith uu____6060))
    | uu____6062 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6085;_},uu____6086::uu____6087::[])
        ->
        let uu____6090 = p_universeFrom u  in
        soft_parens_with_nesting uu____6090
    | FStar_Parser_AST.App uu____6091 ->
        let uu____6098 = p_universeFrom u  in
        soft_parens_with_nesting uu____6098
    | uu____6099 ->
        let uu____6100 =
          let uu____6101 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6101
           in
        failwith uu____6100

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_term e 
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
       | FStar_Parser_AST.Module (uu____6141,decls) ->
           let uu____6147 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6147
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6156,decls,uu____6158) ->
           let uu____6163 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6163
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6214  ->
         match uu____6214 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6254,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6260,decls,uu____6262) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6307 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6320;
                 FStar_Parser_AST.doc = uu____6321;
                 FStar_Parser_AST.quals = uu____6322;
                 FStar_Parser_AST.attrs = uu____6323;_}::uu____6324 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6330 =
                   let uu____6333 =
                     let uu____6336 = FStar_List.tl ds  in d :: uu____6336
                      in
                   d0 :: uu____6333  in
                 (uu____6330, (d0.FStar_Parser_AST.drange))
             | uu____6341 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6307 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6399 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6399 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6495 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6495, comments1))))))
  