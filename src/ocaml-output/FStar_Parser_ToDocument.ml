open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____19 'Auu____20 .
    Prims.bool -> ('Auu____19 -> 'Auu____20) -> 'Auu____19 -> 'Auu____20
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
    'Auu____107 ->
      ('Auu____108 -> 'Auu____107) ->
        'Auu____108 FStar_Pervasives_Native.option -> 'Auu____107
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
  
let separate_map_last :
  'Auu____285 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____285 -> FStar_Pprint.document) ->
        'Auu____285 Prims.list -> FStar_Pprint.document
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
  'Auu____330 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____330 -> FStar_Pprint.document) ->
        'Auu____330 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____357 =
          let uu____358 =
            let uu____359 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____359  in
          separate_map_last uu____358 f l  in
        FStar_Pprint.group uu____357
  
let separate_map_or_flow :
  'Auu____364 .
    FStar_Pprint.document ->
      ('Auu____364 -> FStar_Pprint.document) ->
        'Auu____364 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____391 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____391 -> FStar_Pprint.document) ->
        'Auu____391 Prims.list -> FStar_Pprint.document
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
  'Auu____436 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____436 -> FStar_Pprint.document) ->
        'Auu____436 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let soft_surround_separate_map :
  'Auu____473 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____473 -> FStar_Pprint.document) ->
                  'Auu____473 Prims.list -> FStar_Pprint.document
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
                    (let uu____518 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____518
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____528 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____528 -> FStar_Pprint.document) ->
                  'Auu____528 Prims.list -> FStar_Pprint.document
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
                    (let uu____573 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____573
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____586  ->
    match uu____586 with
    | (comment,keywords) ->
        let uu____611 =
          let uu____612 =
            let uu____615 = str comment  in
            let uu____616 =
              let uu____619 =
                let uu____622 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____631  ->
                       match uu____631 with
                       | (k,v1) ->
                           let uu____638 =
                             let uu____641 = str k  in
                             let uu____642 =
                               let uu____645 =
                                 let uu____648 = str v1  in [uu____648]  in
                               FStar_Pprint.rarrow :: uu____645  in
                             uu____641 :: uu____642  in
                           FStar_Pprint.concat uu____638) keywords
                   in
                [uu____622]  in
              FStar_Pprint.space :: uu____619  in
            uu____615 :: uu____616  in
          FStar_Pprint.concat uu____612  in
        FStar_Pprint.group uu____611
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____652 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          let uu____660 = FStar_Ident.text_of_lid y  in
          x.FStar_Ident.idText = uu____660
      | uu____661 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____690::(e2,uu____692)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____715 -> false  in
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
    | FStar_Parser_AST.Construct (uu____727,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____738,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____759 = extract_from_list e2  in e1 :: uu____759
    | uu____762 ->
        let uu____763 =
          let uu____764 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____764  in
        failwith uu____763
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____771;
           FStar_Parser_AST.level = uu____772;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____774 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____780;
           FStar_Parser_AST.level = uu____781;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____783;
                                                        FStar_Parser_AST.level
                                                          = uu____784;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____786;
                                                   FStar_Parser_AST.level =
                                                     uu____787;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____789;
                FStar_Parser_AST.level = uu____790;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____792;
           FStar_Parser_AST.level = uu____793;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____795 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____803 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____804;
           FStar_Parser_AST.range = uu____805;
           FStar_Parser_AST.level = uu____806;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____807;
                                                        FStar_Parser_AST.range
                                                          = uu____808;
                                                        FStar_Parser_AST.level
                                                          = uu____809;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____811;
                                                   FStar_Parser_AST.level =
                                                     uu____812;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____813;
                FStar_Parser_AST.range = uu____814;
                FStar_Parser_AST.level = uu____815;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____817;
           FStar_Parser_AST.level = uu____818;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____820 = extract_from_ref_set e1  in
        let uu____823 = extract_from_ref_set e2  in
        FStar_List.append uu____820 uu____823
    | uu____826 ->
        let uu____827 =
          let uu____828 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____828  in
        failwith uu____827
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____834 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____834
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____838 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____838
  
let (is_general_prefix_op : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let op_starting_char =
      let uu____843 = FStar_Ident.text_of_id op  in
      FStar_Util.char_at uu____843 (Prims.parse_int "0")  in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) &&
         (let uu____848 = FStar_Ident.text_of_id op  in uu____848 <> "~"))
  
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
      | uu____908 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____922 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____926 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____930 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___54_948  ->
    match uu___54_948 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___55_965  ->
      match uu___55_965 with
      | FStar_Util.Inl c ->
          let uu____974 = FStar_String.get s (Prims.parse_int "0")  in
          uu____974 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____982 .
    Prims.string ->
      ('Auu____982,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1001  ->
      match uu____1001 with
      | (assoc_levels,tokens) ->
          let uu____1029 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1029 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1055 .
    Prims.unit ->
      (associativity,('Auu____1055,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1066  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1082 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1082) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1094  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1129 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1129) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1141  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1169 .
    Prims.unit ->
      (associativity,('Auu____1169,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1180  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1196 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1196) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1208  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1236 .
    Prims.unit ->
      (associativity,('Auu____1236,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1247  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1263 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1263) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1275  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1296 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1296) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1308  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1343 .
    Prims.unit ->
      (associativity,('Auu____1343,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1354  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1370 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1370) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1382  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1403 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1403) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1415  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1436 .
    Prims.unit ->
      (associativity,('Auu____1436,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1447  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1463 .
    Prims.unit ->
      (associativity,('Auu____1463,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1474  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1490 .
    Prims.unit ->
      (associativity,('Auu____1490,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1501  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___56_1708 =
    match uu___56_1708 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1748  ->
         match uu____1748 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1828 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1828 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1878) ->
          assoc_levels
      | uu____1922 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1957 .
    ('Auu____1957,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2017 =
        FStar_List.tryFind
          (fun uu____2057  ->
             match uu____2057 with
             | (uu____2075,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2017 with
      | FStar_Pervasives_Native.Some ((uu____2117,l1,uu____2119),uu____2120)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2175 =
            let uu____2176 =
              let uu____2177 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2177  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2176
             in
          failwith uu____2175
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2211 = assign_levels level_associativity_spec op  in
    match uu____2211 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2235 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2235) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2249  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2330 =
      let uu____2344 =
        let uu____2358 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2358  in
      FStar_List.tryFind uu____2344 (operatorInfix0ad12 ())  in
    uu____2330 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2458 =
      let uu____2472 =
        let uu____2486 = FStar_Ident.text_of_id op  in
        FStar_All.pipe_left matches_level uu____2486  in
      FStar_List.tryFind uu____2472 opinfix34  in
    uu____2458 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2539 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2539
    then (Prims.parse_int "1")
    else
      (let uu____2541 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2541
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2547 . FStar_Ident.ident -> 'Auu____2547 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_27 when _0_27 = (Prims.parse_int "0") -> true
      | _0_28 when _0_28 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (let uu____2561 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2561 ["-"; "~"])
      | _0_29 when _0_29 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (let uu____2563 = FStar_Ident.text_of_id op  in
             FStar_List.mem uu____2563
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_30 when _0_30 = (Prims.parse_int "3") ->
          let uu____2564 = FStar_Ident.text_of_id op  in
          FStar_List.mem uu____2564 [".()<-"; ".[]<-"]
      | uu____2565 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2599 .
    ('Auu____2599 -> FStar_Pprint.document) ->
      'Auu____2599 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2631 = FStar_ST.op_Bang comment_stack  in
          match uu____2631 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2690 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2690
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2727 =
                    let uu____2728 =
                      let uu____2729 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2729
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2728  in
                  comments_before_pos uu____2727 print_pos lookahead_pos))
              else
                (let uu____2731 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2731))
           in
        let uu____2732 =
          let uu____2737 =
            let uu____2738 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2738  in
          let uu____2739 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2737 uu____2739  in
        match uu____2732 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2745 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2745
              else comments  in
            let uu____2751 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2751
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2764 = FStar_ST.op_Bang comment_stack  in
          match uu____2764 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2848 =
                    let uu____2849 =
                      let uu____2850 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2850  in
                    uu____2849 - lbegin  in
                  max k uu____2848  in
                let doc2 =
                  let uu____2852 =
                    let uu____2853 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2854 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2853 uu____2854  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2852  in
                let uu____2855 =
                  let uu____2856 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2856  in
                place_comments_until_pos (Prims.parse_int "1") uu____2855
                  pos_end doc2))
          | uu____2857 ->
              let lnum =
                let uu____2865 =
                  let uu____2866 = FStar_Range.line_of_pos pos_end  in
                  uu____2866 - lbegin  in
                max (Prims.parse_int "1") uu____2865  in
              let uu____2867 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2867
  
let separate_map_with_comments :
  'Auu____2874 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2874 -> FStar_Pprint.document) ->
          'Auu____2874 Prims.list ->
            ('Auu____2874 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2922 x =
              match uu____2922 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2936 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2936 doc1
                     in
                  let uu____2937 =
                    let uu____2938 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2938  in
                  let uu____2939 =
                    let uu____2940 =
                      let uu____2941 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2941  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2940  in
                  (uu____2937, uu____2939)
               in
            let uu____2942 =
              let uu____2949 = FStar_List.hd xs  in
              let uu____2950 = FStar_List.tl xs  in (uu____2949, uu____2950)
               in
            match uu____2942 with
            | (x,xs1) ->
                let init1 =
                  let uu____2966 =
                    let uu____2967 =
                      let uu____2968 = extract_range x  in
                      FStar_Range.end_of_range uu____2968  in
                    FStar_Range.line_of_pos uu____2967  in
                  let uu____2969 =
                    let uu____2970 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2970  in
                  (uu____2966, uu____2969)  in
                let uu____2971 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2971
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3347 =
      let uu____3348 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3349 =
        let uu____3350 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3351 =
          let uu____3352 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3353 =
            let uu____3354 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3354
             in
          FStar_Pprint.op_Hat_Hat uu____3352 uu____3353  in
        FStar_Pprint.op_Hat_Hat uu____3350 uu____3351  in
      FStar_Pprint.op_Hat_Hat uu____3348 uu____3349  in
    FStar_Pprint.group uu____3347

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3357 =
      let uu____3358 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3358  in
    let uu____3359 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3357 FStar_Pprint.space uu____3359
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3360  ->
    match uu____3360 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3394 =
                match uu____3394 with
                | (kwd,arg) ->
                    let uu____3401 = str "@"  in
                    let uu____3402 =
                      let uu____3403 = str kwd  in
                      let uu____3404 =
                        let uu____3405 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3405
                         in
                      FStar_Pprint.op_Hat_Hat uu____3403 uu____3404  in
                    FStar_Pprint.op_Hat_Hat uu____3401 uu____3402
                 in
              let uu____3406 =
                let uu____3407 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3407 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3406
           in
        let uu____3412 =
          let uu____3413 =
            let uu____3414 =
              let uu____3415 =
                let uu____3416 = str doc1  in
                let uu____3417 =
                  let uu____3418 =
                    let uu____3419 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3419  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3418  in
                FStar_Pprint.op_Hat_Hat uu____3416 uu____3417  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3415  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3414  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3413  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3412

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3423 =
          let uu____3424 = str "val"  in
          let uu____3425 =
            let uu____3426 =
              let uu____3427 = p_lident lid  in
              let uu____3428 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3427 uu____3428  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3426  in
          FStar_Pprint.op_Hat_Hat uu____3424 uu____3425  in
        let uu____3429 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3423 uu____3429
    | FStar_Parser_AST.TopLevelLet (uu____3430,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3455 =
               let uu____3456 = str "let"  in
               let uu____3457 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3456 uu____3457  in
             FStar_Pprint.group uu____3455) lbs
    | uu____3458 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___57_3471 =
          match uu___57_3471 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3479 = f x  in
              let uu____3480 =
                let uu____3481 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3481  in
              FStar_Pprint.op_Hat_Hat uu____3479 uu____3480
           in
        let uu____3482 = str "["  in
        let uu____3483 =
          let uu____3484 = p_list' l  in
          let uu____3485 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3484 uu____3485  in
        FStar_Pprint.op_Hat_Hat uu____3482 uu____3483

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3488 =
          let uu____3489 = str "open"  in
          let uu____3490 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3489 uu____3490  in
        FStar_Pprint.group uu____3488
    | FStar_Parser_AST.Include uid ->
        let uu____3492 =
          let uu____3493 = str "include"  in
          let uu____3494 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3493 uu____3494  in
        FStar_Pprint.group uu____3492
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3497 =
          let uu____3498 = str "module"  in
          let uu____3499 =
            let uu____3500 =
              let uu____3501 = p_uident uid1  in
              let uu____3502 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3501 uu____3502  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3500  in
          FStar_Pprint.op_Hat_Hat uu____3498 uu____3499  in
        let uu____3503 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3497 uu____3503
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3505 =
          let uu____3506 = str "module"  in
          let uu____3507 =
            let uu____3508 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3508  in
          FStar_Pprint.op_Hat_Hat uu____3506 uu____3507  in
        FStar_Pprint.group uu____3505
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3541 = str "effect"  in
          let uu____3542 =
            let uu____3543 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3543  in
          FStar_Pprint.op_Hat_Hat uu____3541 uu____3542  in
        let uu____3544 =
          let uu____3545 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3545 FStar_Pprint.equals
           in
        let uu____3546 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3544 uu____3546
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3564 = str "type"  in
        let uu____3565 = str "and"  in
        precede_break_separate_map uu____3564 uu____3565 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3587 = str "let"  in
          let uu____3588 =
            let uu____3589 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3589 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3587 uu____3588  in
        let uu____3590 =
          let uu____3591 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3591 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3590 p_letbinding lbs
          (fun uu____3599  ->
             match uu____3599 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3608 =
          let uu____3609 = str "val"  in
          let uu____3610 =
            let uu____3611 =
              let uu____3612 = p_lident lid  in
              let uu____3613 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3612 uu____3613  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3611  in
          FStar_Pprint.op_Hat_Hat uu____3609 uu____3610  in
        let uu____3614 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3608 uu____3614
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3618 =
            let uu____3619 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3619 FStar_Util.is_upper  in
          if uu____3618
          then FStar_Pprint.empty
          else
            (let uu____3621 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3621 FStar_Pprint.space)
           in
        let uu____3622 =
          let uu____3623 =
            let uu____3624 = p_ident id1  in
            let uu____3625 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3624 uu____3625  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3623  in
        let uu____3626 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3622 uu____3626
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3633 = str "exception"  in
        let uu____3634 =
          let uu____3635 =
            let uu____3636 = p_uident uid  in
            let uu____3637 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3641 =
                     let uu____3642 = str "of"  in
                     let uu____3643 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3642 uu____3643  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3641) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3636 uu____3637  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3635  in
        FStar_Pprint.op_Hat_Hat uu____3633 uu____3634
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3645 = str "new_effect"  in
        let uu____3646 =
          let uu____3647 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3647  in
        FStar_Pprint.op_Hat_Hat uu____3645 uu____3646
    | FStar_Parser_AST.SubEffect se ->
        let uu____3649 = str "sub_effect"  in
        let uu____3650 =
          let uu____3651 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3651  in
        FStar_Pprint.op_Hat_Hat uu____3649 uu____3650
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3654 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3654 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3655 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3656) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3679 = str "%splice"  in
        let uu____3680 =
          let uu____3681 =
            let uu____3682 = str ";"  in p_list p_uident uu____3682 ids  in
          let uu____3683 =
            let uu____3684 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3684  in
          FStar_Pprint.op_Hat_Hat uu____3681 uu____3683  in
        FStar_Pprint.op_Hat_Hat uu____3679 uu____3680

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___58_3685  ->
    match uu___58_3685 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3687 = str "#set-options"  in
        let uu____3688 =
          let uu____3689 =
            let uu____3690 = str s  in FStar_Pprint.dquotes uu____3690  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3689  in
        FStar_Pprint.op_Hat_Hat uu____3687 uu____3688
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3694 = str "#reset-options"  in
        let uu____3695 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3699 =
                 let uu____3700 = str s  in FStar_Pprint.dquotes uu____3700
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3699) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3694 uu____3695
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
  fun uu____3724  ->
    match uu____3724 with
    | (typedecl,fsdoc_opt) ->
        let uu____3737 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3738 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3737 uu____3738

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___59_3739  ->
    match uu___59_3739 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3754 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3770 =
          let uu____3771 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3771  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3818 =
          match uu____3818 with
          | (lid1,t,doc_opt) ->
              let uu____3834 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3834
           in
        let p_fields uu____3848 =
          let uu____3849 =
            let uu____3850 =
              let uu____3851 =
                let uu____3852 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3852 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3851  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3850  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3849  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3916 =
          match uu____3916 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3942 =
                  let uu____3943 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3943  in
                FStar_Range.extend_to_end_of_line uu____3942  in
              let p_constructorBranch decl =
                let uu____3976 =
                  let uu____3977 =
                    let uu____3978 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3978  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3977  in
                FStar_Pprint.group uu____3976  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3998 =
          let uu____3999 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3999  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4014  ->
             let uu____4015 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____4015)

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
            let uu____4030 = p_ident lid  in
            let uu____4031 =
              let uu____4032 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4032  in
            FStar_Pprint.op_Hat_Hat uu____4030 uu____4031
          else
            (let binders_doc =
               let uu____4035 = p_typars bs  in
               let uu____4036 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4040 =
                        let uu____4041 =
                          let uu____4042 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4042
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4041
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____4040) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____4035 uu____4036  in
             let uu____4043 = p_ident lid  in
             let uu____4044 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4043 binders_doc uu____4044)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4046  ->
      match uu____4046 with
      | (lid,t,doc_opt) ->
          let uu____4062 =
            let uu____4063 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4064 =
              let uu____4065 = p_lident lid  in
              let uu____4066 =
                let uu____4067 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4067  in
              FStar_Pprint.op_Hat_Hat uu____4065 uu____4066  in
            FStar_Pprint.op_Hat_Hat uu____4063 uu____4064  in
          FStar_Pprint.group uu____4062

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4068  ->
    match uu____4068 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4096 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4097 =
          let uu____4098 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4099 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4104 =
                   let uu____4105 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4105  in
                 let uu____4106 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4104 uu____4106) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4098 uu____4099  in
        FStar_Pprint.op_Hat_Hat uu____4096 uu____4097

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4107  ->
    match uu____4107 with
    | (pat,uu____4113) ->
        let uu____4114 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4133 =
                let uu____4134 =
                  let uu____4135 =
                    let uu____4136 =
                      let uu____4137 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4137
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4136  in
                  FStar_Pprint.group uu____4135  in
                FStar_Pprint.op_Hat_Hat break1 uu____4134  in
              (pat1, uu____4133)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4149 =
                let uu____4150 =
                  let uu____4151 =
                    let uu____4152 =
                      let uu____4153 =
                        let uu____4154 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4154
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4153
                       in
                    FStar_Pprint.group uu____4152  in
                  let uu____4155 =
                    let uu____4156 =
                      let uu____4157 = str "by"  in
                      let uu____4158 =
                        let uu____4159 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4159
                         in
                      FStar_Pprint.op_Hat_Hat uu____4157 uu____4158  in
                    FStar_Pprint.group uu____4156  in
                  FStar_Pprint.op_Hat_Hat uu____4151 uu____4155  in
                FStar_Pprint.op_Hat_Hat break1 uu____4150  in
              (pat1, uu____4149)
          | uu____4160 -> (pat, FStar_Pprint.empty)  in
        (match uu____4114 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4164);
                     FStar_Parser_AST.prange = uu____4165;_},pats)
                  ->
                  let uu____4175 =
                    let uu____4176 = p_lident x  in
                    let uu____4177 =
                      let uu____4178 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4178 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4176 uu____4177  in
                  FStar_Pprint.group uu____4175
              | uu____4179 ->
                  let uu____4180 =
                    let uu____4181 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4181 ascr_doc  in
                  FStar_Pprint.group uu____4180))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4182  ->
    match uu____4182 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4190 =
          let uu____4191 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4191  in
        let uu____4192 = p_term false false e  in
        prefix2 uu____4190 uu____4192

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___60_4193  ->
    match uu___60_4193 with
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
        let uu____4218 = p_uident uid  in
        let uu____4219 = p_binders true bs  in
        let uu____4220 =
          let uu____4221 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4221  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4218 uu____4219 uu____4220

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
          let uu____4230 =
            let uu____4231 =
              let uu____4232 =
                let uu____4233 = p_uident uid  in
                let uu____4234 = p_binders true bs  in
                let uu____4235 =
                  let uu____4236 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4236  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4233 uu____4234 uu____4235
                 in
              FStar_Pprint.group uu____4232  in
            let uu____4237 =
              let uu____4238 = str "with"  in
              let uu____4239 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4238 uu____4239  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4231 uu____4237  in
          braces_with_nesting uu____4230

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
          let uu____4270 =
            let uu____4271 = p_lident lid  in
            let uu____4272 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4271 uu____4272  in
          let uu____4273 = p_simpleTerm ps false e  in
          prefix2 uu____4270 uu____4273
      | uu____4274 ->
          let uu____4275 =
            let uu____4276 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4276
             in
          failwith uu____4275

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4334 =
        match uu____4334 with
        | (kwd,t) ->
            let uu____4341 =
              let uu____4342 = str kwd  in
              let uu____4343 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4342 uu____4343  in
            let uu____4344 = p_simpleTerm ps false t  in
            prefix2 uu____4341 uu____4344
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4349 =
      let uu____4350 =
        let uu____4351 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4352 =
          let uu____4353 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4353  in
        FStar_Pprint.op_Hat_Hat uu____4351 uu____4352  in
      let uu____4354 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4350 uu____4354  in
    let uu____4355 =
      let uu____4356 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4356  in
    FStar_Pprint.op_Hat_Hat uu____4349 uu____4355

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___61_4357  ->
    match uu___61_4357 with
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
    let uu____4359 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4359

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___62_4360  ->
    match uu___62_4360 with
    | FStar_Parser_AST.Rec  ->
        let uu____4361 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4361
    | FStar_Parser_AST.Mutable  ->
        let uu____4362 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4362
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___63_4363  ->
    match uu___63_4363 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4368 =
          let uu____4369 =
            let uu____4370 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4370  in
          FStar_Pprint.separate_map uu____4369 p_tuplePattern pats  in
        FStar_Pprint.group uu____4368
    | uu____4371 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4378 =
          let uu____4379 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4379 p_constructorPattern pats  in
        FStar_Pprint.group uu____4378
    | uu____4380 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4383;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4388 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4389 = p_constructorPattern hd1  in
        let uu____4390 = p_constructorPattern tl1  in
        infix0 uu____4388 uu____4389 uu____4390
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4392;_},pats)
        ->
        let uu____4398 = p_quident uid  in
        let uu____4399 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4398 uu____4399
    | uu____4400 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4416;
               FStar_Parser_AST.blevel = uu____4417;
               FStar_Parser_AST.aqual = uu____4418;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4424 =
               let uu____4425 = p_ident lid  in
               p_refinement aqual uu____4425 t1 phi  in
             soft_parens_with_nesting uu____4424
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4427;
               FStar_Parser_AST.blevel = uu____4428;
               FStar_Parser_AST.aqual = uu____4429;_},phi))
             ->
             let uu____4431 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4431
         | uu____4432 ->
             let uu____4437 =
               let uu____4438 = p_tuplePattern pat  in
               let uu____4439 =
                 let uu____4440 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4441 =
                   let uu____4442 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4442  in
                 FStar_Pprint.op_Hat_Hat uu____4440 uu____4441  in
               FStar_Pprint.op_Hat_Hat uu____4438 uu____4439  in
             soft_parens_with_nesting uu____4437)
    | FStar_Parser_AST.PatList pats ->
        let uu____4446 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4446 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4461 =
          match uu____4461 with
          | (lid,pat) ->
              let uu____4468 = p_qlident lid  in
              let uu____4469 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4468 uu____4469
           in
        let uu____4470 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4470
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4480 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4481 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4482 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4480 uu____4481 uu____4482
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4493 =
          let uu____4494 =
            let uu____4495 =
              let uu____4496 = FStar_Ident.text_of_id op  in str uu____4496
               in
            let uu____4497 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4495 uu____4497  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4494  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4493
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4505 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4506 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4505 uu____4506
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4508 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4511;
           FStar_Parser_AST.prange = uu____4512;_},uu____4513)
        ->
        let uu____4518 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4518
    | FStar_Parser_AST.PatTuple (uu____4519,false ) ->
        let uu____4524 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4524
    | uu____4525 ->
        let uu____4526 =
          let uu____4527 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4527  in
        failwith uu____4526

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4531 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4532 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4531 uu____4532
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4539;
                   FStar_Parser_AST.blevel = uu____4540;
                   FStar_Parser_AST.aqual = uu____4541;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4543 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4543 t1 phi
            | uu____4544 ->
                let uu____4545 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4546 =
                  let uu____4547 = p_lident lid  in
                  let uu____4548 =
                    let uu____4549 =
                      let uu____4550 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4551 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4550 uu____4551  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4549  in
                  FStar_Pprint.op_Hat_Hat uu____4547 uu____4548  in
                FStar_Pprint.op_Hat_Hat uu____4545 uu____4546
             in
          if is_atomic
          then
            let uu____4552 =
              let uu____4553 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4553  in
            FStar_Pprint.group uu____4552
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4555 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4562;
                  FStar_Parser_AST.blevel = uu____4563;
                  FStar_Parser_AST.aqual = uu____4564;_},phi)
               ->
               if is_atomic
               then
                 let uu____4566 =
                   let uu____4567 =
                     let uu____4568 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4568 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4567  in
                 FStar_Pprint.group uu____4566
               else
                 (let uu____4570 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4570)
           | uu____4571 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4579 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4580 =
            let uu____4581 =
              let uu____4582 =
                let uu____4583 = p_appTerm t  in
                let uu____4584 =
                  let uu____4585 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4585  in
                FStar_Pprint.op_Hat_Hat uu____4583 uu____4584  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4582  in
            FStar_Pprint.op_Hat_Hat binder uu____4581  in
          FStar_Pprint.op_Hat_Hat uu____4579 uu____4580

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____4591 = FStar_Ident.text_of_lid lid  in str uu____4591

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> let uu____4593 = FStar_Ident.text_of_lid lid  in str uu____4593

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4595 = FStar_Ident.text_of_id lid  in str uu____4595

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4597 = FStar_Ident.text_of_id lid  in str uu____4597

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4599 = FStar_Ident.text_of_id lid  in str uu____4599

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> let uu____4601 = FStar_Ident.text_of_id lid  in str uu____4601

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
            let uu____4614 =
              let uu____4615 =
                let uu____4616 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4616 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4615  in
            let uu____4617 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4614 uu____4617
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4621 =
              let uu____4622 =
                let uu____4623 =
                  let uu____4624 = p_lident x  in
                  let uu____4625 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4624 uu____4625  in
                let uu____4626 =
                  let uu____4627 = p_noSeqTerm true false e1  in
                  let uu____4628 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4627 uu____4628  in
                op_Hat_Slash_Plus_Hat uu____4623 uu____4626  in
              FStar_Pprint.group uu____4622  in
            let uu____4629 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4621 uu____4629
        | uu____4630 ->
            let uu____4631 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4631

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
            let uu____4642 =
              let uu____4643 = p_tmIff e1  in
              let uu____4644 =
                let uu____4645 =
                  let uu____4646 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4646
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4645  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4643 uu____4644  in
            FStar_Pprint.group uu____4642
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4652 =
              let uu____4653 = p_tmIff e1  in
              let uu____4654 =
                let uu____4655 =
                  let uu____4656 =
                    let uu____4657 = p_typ false false t  in
                    let uu____4658 =
                      let uu____4659 = str "by"  in
                      let uu____4660 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4659 uu____4660  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4657 uu____4658  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4656
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4655  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4653 uu____4654  in
            FStar_Pprint.group uu____4652
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4661;_},e1::e2::e3::[])
            ->
            let uu____4667 =
              let uu____4668 =
                let uu____4669 =
                  let uu____4670 = p_atomicTermNotQUident e1  in
                  let uu____4671 =
                    let uu____4672 =
                      let uu____4673 =
                        let uu____4674 = p_term false false e2  in
                        soft_parens_with_nesting uu____4674  in
                      let uu____4675 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4673 uu____4675  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4672  in
                  FStar_Pprint.op_Hat_Hat uu____4670 uu____4671  in
                FStar_Pprint.group uu____4669  in
              let uu____4676 =
                let uu____4677 = p_noSeqTerm ps pb e3  in jump2 uu____4677
                 in
              FStar_Pprint.op_Hat_Hat uu____4668 uu____4676  in
            FStar_Pprint.group uu____4667
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4678;_},e1::e2::e3::[])
            ->
            let uu____4684 =
              let uu____4685 =
                let uu____4686 =
                  let uu____4687 = p_atomicTermNotQUident e1  in
                  let uu____4688 =
                    let uu____4689 =
                      let uu____4690 =
                        let uu____4691 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4691  in
                      let uu____4692 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4690 uu____4692  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4689  in
                  FStar_Pprint.op_Hat_Hat uu____4687 uu____4688  in
                FStar_Pprint.group uu____4686  in
              let uu____4693 =
                let uu____4694 = p_noSeqTerm ps pb e3  in jump2 uu____4694
                 in
              FStar_Pprint.op_Hat_Hat uu____4685 uu____4693  in
            FStar_Pprint.group uu____4684
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4704 =
              let uu____4705 = str "requires"  in
              let uu____4706 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4705 uu____4706  in
            FStar_Pprint.group uu____4704
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4716 =
              let uu____4717 = str "ensures"  in
              let uu____4718 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4717 uu____4718  in
            FStar_Pprint.group uu____4716
        | FStar_Parser_AST.Attributes es ->
            let uu____4722 =
              let uu____4723 = str "attributes"  in
              let uu____4724 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4723 uu____4724  in
            FStar_Pprint.group uu____4722
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4728 =
                let uu____4729 =
                  let uu____4730 = str "if"  in
                  let uu____4731 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4730 uu____4731  in
                let uu____4732 =
                  let uu____4733 = str "then"  in
                  let uu____4734 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4733 uu____4734  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4729 uu____4732  in
              FStar_Pprint.group uu____4728
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4737,uu____4738,e31) when
                     is_unit e31 ->
                     let uu____4740 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4740
                 | uu____4741 -> p_noSeqTerm false false e2  in
               let uu____4742 =
                 let uu____4743 =
                   let uu____4744 = str "if"  in
                   let uu____4745 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4744 uu____4745  in
                 let uu____4746 =
                   let uu____4747 =
                     let uu____4748 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4748 e2_doc  in
                   let uu____4749 =
                     let uu____4750 = str "else"  in
                     let uu____4751 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4750 uu____4751  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4747 uu____4749  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4743 uu____4746  in
               FStar_Pprint.group uu____4742)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4774 =
              let uu____4775 =
                let uu____4776 =
                  let uu____4777 = str "try"  in
                  let uu____4778 = p_noSeqTerm false false e1  in
                  prefix2 uu____4777 uu____4778  in
                let uu____4779 =
                  let uu____4780 = str "with"  in
                  let uu____4781 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4780 uu____4781  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4776 uu____4779  in
              FStar_Pprint.group uu____4775  in
            let uu____4790 = paren_if (ps || pb)  in uu____4790 uu____4774
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4815 =
              let uu____4816 =
                let uu____4817 =
                  let uu____4818 = str "match"  in
                  let uu____4819 = p_noSeqTerm false false e1  in
                  let uu____4820 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4818 uu____4819 uu____4820
                   in
                let uu____4821 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4817 uu____4821  in
              FStar_Pprint.group uu____4816  in
            let uu____4830 = paren_if (ps || pb)  in uu____4830 uu____4815
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4835 =
              let uu____4836 =
                let uu____4837 =
                  let uu____4838 = str "let open"  in
                  let uu____4839 = p_quident uid  in
                  let uu____4840 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4838 uu____4839 uu____4840
                   in
                let uu____4841 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4837 uu____4841  in
              FStar_Pprint.group uu____4836  in
            let uu____4842 = paren_if ps  in uu____4842 uu____4835
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____4898 is_last =
              match uu____4898 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____4931 =
                          let uu____4932 = str "let"  in
                          let uu____4933 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4932 uu____4933
                           in
                        FStar_Pprint.group uu____4931
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____4934 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____4939 =
                    if is_last
                    then
                      let uu____4940 =
                        let uu____4941 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____4942 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____4941 doc_expr
                          uu____4942
                         in
                      FStar_Pprint.group uu____4940
                    else
                      (let uu____4944 =
                         let uu____4945 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____4945 doc_expr
                          in
                       FStar_Pprint.group uu____4944)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____4939
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____4991 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____4991
                     else
                       (let uu____4999 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____4999)) lbs
               in
            let lbs_doc =
              let uu____5007 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5007  in
            let uu____5008 =
              let uu____5009 =
                let uu____5010 =
                  let uu____5011 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5011
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5010  in
              FStar_Pprint.group uu____5009  in
            let uu____5012 = paren_if ps  in uu____5012 uu____5008
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5017;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5020;
                                                             FStar_Parser_AST.level
                                                               = uu____5021;_})
            when matches_var maybe_x x ->
            let uu____5048 =
              let uu____5049 =
                let uu____5050 = str "function"  in
                let uu____5051 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5050 uu____5051  in
              FStar_Pprint.group uu____5049  in
            let uu____5060 = paren_if (ps || pb)  in uu____5060 uu____5048
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5064 =
              let uu____5065 = str "quote"  in
              let uu____5066 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5065 uu____5066  in
            FStar_Pprint.group uu____5064
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5068 =
              let uu____5069 = str "`"  in
              let uu____5070 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5069 uu____5070  in
            FStar_Pprint.group uu____5068
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5072 =
              let uu____5073 = str "%`"  in
              let uu____5074 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5073 uu____5074  in
            FStar_Pprint.group uu____5072
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5076 =
              let uu____5077 = str "`#"  in
              let uu____5078 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5077 uu____5078  in
            FStar_Pprint.group uu____5076
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5080 =
              let uu____5081 = str "`@"  in
              let uu____5082 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5081 uu____5082  in
            FStar_Pprint.group uu____5080
        | uu____5083 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___64_5084  ->
    match uu___64_5084 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5096 =
          let uu____5097 =
            let uu____5098 = str "[@"  in
            let uu____5099 =
              let uu____5100 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5101 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5100 uu____5101  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5098 uu____5099  in
          FStar_Pprint.group uu____5097  in
        FStar_Pprint.op_Hat_Hat uu____5096 break1

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
            let uu____5123 =
              let uu____5124 =
                let uu____5125 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5125 FStar_Pprint.space  in
              let uu____5126 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5124 uu____5126 FStar_Pprint.dot
               in
            let uu____5127 =
              let uu____5128 = p_trigger trigger  in
              let uu____5129 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5128 uu____5129  in
            prefix2 uu____5123 uu____5127
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5145 =
              let uu____5146 =
                let uu____5147 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5147 FStar_Pprint.space  in
              let uu____5148 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5146 uu____5148 FStar_Pprint.dot
               in
            let uu____5149 =
              let uu____5150 = p_trigger trigger  in
              let uu____5151 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5150 uu____5151  in
            prefix2 uu____5145 uu____5149
        | uu____5152 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5154 -> str "forall"
    | FStar_Parser_AST.QExists uu____5167 -> str "exists"
    | uu____5180 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___65_5181  ->
    match uu___65_5181 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5193 =
          let uu____5194 =
            let uu____5195 = str "pattern"  in
            let uu____5196 =
              let uu____5197 =
                let uu____5198 = p_disjunctivePats pats  in jump2 uu____5198
                 in
              let uu____5199 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5197 uu____5199  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5195 uu____5196  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5194  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5193

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5205 = str "\\/"  in
    FStar_Pprint.separate_map uu____5205 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5211 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5211

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5221 =
              let uu____5222 =
                let uu____5223 = str "fun"  in
                let uu____5224 =
                  let uu____5225 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5225
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5223 uu____5224  in
              let uu____5226 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5222 uu____5226  in
            let uu____5227 = paren_if ps  in uu____5227 uu____5221
        | uu____5230 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5234  ->
      match uu____5234 with
      | (pat,when_opt,e) ->
          let uu____5250 =
            let uu____5251 =
              let uu____5252 =
                let uu____5253 =
                  let uu____5254 =
                    let uu____5255 = p_disjunctivePattern pat  in
                    let uu____5256 =
                      let uu____5257 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5257 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5255 uu____5256  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5254  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5253  in
              FStar_Pprint.group uu____5252  in
            let uu____5258 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5251 uu____5258  in
          FStar_Pprint.group uu____5250

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___66_5259  ->
    match uu___66_5259 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5263 = str "when"  in
        let uu____5264 =
          let uu____5265 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5265 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5263 uu____5264

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5267;_},e1::e2::[])
        ->
        let uu____5272 = str "<==>"  in
        let uu____5273 = p_tmImplies e1  in
        let uu____5274 = p_tmIff e2  in
        infix0 uu____5272 uu____5273 uu____5274
    | uu____5275 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5277;_},e1::e2::[])
        ->
        let uu____5282 = str "==>"  in
        let uu____5283 = p_tmArrow p_tmFormula e1  in
        let uu____5284 = p_tmImplies e2  in
        infix0 uu____5282 uu____5283 uu____5284
    | uu____5285 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5296 =
            let uu____5297 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5302 = p_binder false b  in
                   let uu____5303 =
                     let uu____5304 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5304
                      in
                   FStar_Pprint.op_Hat_Hat uu____5302 uu____5303) bs
               in
            let uu____5305 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5297 uu____5305  in
          FStar_Pprint.group uu____5296
      | uu____5306 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5308;_},e1::e2::[])
        ->
        let uu____5313 = str "\\/"  in
        let uu____5314 = p_tmFormula e1  in
        let uu____5315 = p_tmConjunction e2  in
        infix0 uu____5313 uu____5314 uu____5315
    | uu____5316 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5318;_},e1::e2::[])
        ->
        let uu____5323 = str "/\\"  in
        let uu____5324 = p_tmConjunction e1  in
        let uu____5325 = p_tmTuple e2  in
        infix0 uu____5323 uu____5324 uu____5325
    | uu____5326 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5343 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5343
          (fun uu____5351  ->
             match uu____5351 with | (e1,uu____5357) -> p_tmEq e1) args
    | uu____5358 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5363 =
             let uu____5364 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5364  in
           FStar_Pprint.group uu____5363)

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
               (let uu____5427 = FStar_Ident.text_of_id op  in
                uu____5427 = "="))
              ||
              (let uu____5429 = FStar_Ident.text_of_id op  in
               uu____5429 = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5431 = levels op1  in
            (match uu____5431 with
             | (left1,mine,right1) ->
                 let uu____5441 =
                   let uu____5442 = FStar_All.pipe_left str op1  in
                   let uu____5443 = p_tmEqWith' p_X left1 e1  in
                   let uu____5444 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5442 uu____5443 uu____5444  in
                 paren_if_gt curr mine uu____5441)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5445;_},e1::e2::[])
            ->
            let uu____5450 =
              let uu____5451 = p_tmEqWith p_X e1  in
              let uu____5452 =
                let uu____5453 =
                  let uu____5454 =
                    let uu____5455 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5455  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5454  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5453  in
              FStar_Pprint.op_Hat_Hat uu____5451 uu____5452  in
            FStar_Pprint.group uu____5450
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5456;_},e1::[])
            ->
            let uu____5460 = levels "-"  in
            (match uu____5460 with
             | (left1,mine,right1) ->
                 let uu____5470 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5470)
        | uu____5471 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5542)::(e2,uu____5544)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5564 = is_list e  in Prims.op_Negation uu____5564)
            ->
            let op = "::"  in
            let uu____5566 = levels op  in
            (match uu____5566 with
             | (left1,mine,right1) ->
                 let uu____5576 =
                   let uu____5577 = str op  in
                   let uu____5578 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5579 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5577 uu____5578 uu____5579  in
                 paren_if_gt curr mine uu____5576)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5587 = levels op  in
            (match uu____5587 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5601 = p_binder false b  in
                   let uu____5602 =
                     let uu____5603 =
                       let uu____5604 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5604 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5603
                      in
                   FStar_Pprint.op_Hat_Hat uu____5601 uu____5602  in
                 let uu____5605 =
                   let uu____5606 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5607 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5606 uu____5607  in
                 paren_if_gt curr mine uu____5605)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5614 = levels op1  in
            (match uu____5614 with
             | (left1,mine,right1) ->
                 let uu____5624 =
                   let uu____5625 = str op1  in
                   let uu____5626 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5627 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5625 uu____5626 uu____5627  in
                 paren_if_gt curr mine uu____5624)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5646 =
              let uu____5647 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5648 =
                let uu____5649 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5649 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5647 uu____5648  in
            braces_with_nesting uu____5646
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5654;_},e1::[])
            ->
            let uu____5658 =
              let uu____5659 = str "~"  in
              let uu____5660 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5659 uu____5660  in
            FStar_Pprint.group uu____5658
        | uu____5661 -> p_X e

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
        let uu____5668 =
          let uu____5669 = p_lidentOrUnderscore lid  in
          let uu____5670 =
            let uu____5671 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5671  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5669 uu____5670  in
        FStar_Pprint.group uu____5668
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5674 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5676 = p_appTerm e  in
    let uu____5677 =
      let uu____5678 =
        let uu____5679 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5679 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5678  in
    FStar_Pprint.op_Hat_Hat uu____5676 uu____5677

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5684 =
            let uu____5685 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5685 t phi  in
          soft_parens_with_nesting uu____5684
      | FStar_Parser_AST.TAnnotated uu____5686 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5691 ->
          let uu____5692 =
            let uu____5693 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5693
             in
          failwith uu____5692
      | FStar_Parser_AST.TVariable uu____5694 ->
          let uu____5695 =
            let uu____5696 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5696
             in
          failwith uu____5695
      | FStar_Parser_AST.NoName uu____5697 ->
          let uu____5698 =
            let uu____5699 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5699
             in
          failwith uu____5698

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5701  ->
      match uu____5701 with
      | (lid,e) ->
          let uu____5708 =
            let uu____5709 = p_qlident lid  in
            let uu____5710 =
              let uu____5711 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5711
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5709 uu____5710  in
          FStar_Pprint.group uu____5708

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5713 when is_general_application e ->
        let uu____5720 = head_and_args e  in
        (match uu____5720 with
         | (head1,args) ->
             let uu____5745 =
               let uu____5756 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5756
               then
                 let uu____5786 =
                   FStar_Util.take
                     (fun uu____5810  ->
                        match uu____5810 with
                        | (uu____5815,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5786 with
                 | (fs_typ_args,args1) ->
                     let uu____5853 =
                       let uu____5854 = p_indexingTerm head1  in
                       let uu____5855 =
                         let uu____5856 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5856 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5854 uu____5855  in
                     (uu____5853, args1)
               else
                 (let uu____5868 = p_indexingTerm head1  in
                  (uu____5868, args))
                in
             (match uu____5745 with
              | (head_doc,args1) ->
                  let uu____5889 =
                    let uu____5890 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5890 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5889))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5910 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5910)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5928 =
               let uu____5929 = p_quident lid  in
               let uu____5930 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5929 uu____5930  in
             FStar_Pprint.group uu____5928
         | hd1::tl1 ->
             let uu____5947 =
               let uu____5948 =
                 let uu____5949 =
                   let uu____5950 = p_quident lid  in
                   let uu____5951 = p_argTerm hd1  in
                   prefix2 uu____5950 uu____5951  in
                 FStar_Pprint.group uu____5949  in
               let uu____5952 =
                 let uu____5953 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5953  in
               FStar_Pprint.op_Hat_Hat uu____5948 uu____5952  in
             FStar_Pprint.group uu____5947)
    | uu____5958 -> p_indexingTerm e

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
         (let uu____5967 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5967 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5969 = str "#"  in
        let uu____5970 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5969 uu____5970
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5972  ->
    match uu____5972 with | (e,uu____5978) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5983;_},e1::e2::[])
          ->
          let uu____5988 =
            let uu____5989 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5990 =
              let uu____5991 =
                let uu____5992 = p_term false false e2  in
                soft_parens_with_nesting uu____5992  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5991  in
            FStar_Pprint.op_Hat_Hat uu____5989 uu____5990  in
          FStar_Pprint.group uu____5988
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5993;_},e1::e2::[])
          ->
          let uu____5998 =
            let uu____5999 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6000 =
              let uu____6001 =
                let uu____6002 = p_term false false e2  in
                soft_brackets_with_nesting uu____6002  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6001  in
            FStar_Pprint.op_Hat_Hat uu____5999 uu____6000  in
          FStar_Pprint.group uu____5998
      | uu____6003 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6008 = p_quident lid  in
        let uu____6009 =
          let uu____6010 =
            let uu____6011 = p_term false false e1  in
            soft_parens_with_nesting uu____6011  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6010  in
        FStar_Pprint.op_Hat_Hat uu____6008 uu____6009
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6017 =
          let uu____6018 = FStar_Ident.text_of_id op  in str uu____6018  in
        let uu____6019 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6017 uu____6019
    | uu____6020 -> p_atomicTermNotQUident e

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
         | uu____6027 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6034 =
          let uu____6035 = FStar_Ident.text_of_id op  in str uu____6035  in
        let uu____6036 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6034 uu____6036
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6040 =
          let uu____6041 =
            let uu____6042 =
              let uu____6043 = FStar_Ident.text_of_id op  in str uu____6043
               in
            let uu____6044 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6042 uu____6044  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6041  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6040
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6059 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6060 =
          let uu____6061 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6062 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6061 p_tmEq uu____6062  in
        let uu____6069 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6059 uu____6060 uu____6069
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6072 =
          let uu____6073 = p_atomicTermNotQUident e1  in
          let uu____6074 =
            let uu____6075 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6075  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6073 uu____6074
           in
        FStar_Pprint.group uu____6072
    | uu____6076 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6081 = p_quident constr_lid  in
        let uu____6082 =
          let uu____6083 =
            let uu____6084 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6084  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6083  in
        FStar_Pprint.op_Hat_Hat uu____6081 uu____6082
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6086 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6086 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6088 = p_term false false e1  in
        soft_parens_with_nesting uu____6088
    | uu____6089 when is_array e ->
        let es = extract_from_list e  in
        let uu____6093 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6094 =
          let uu____6095 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6095
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6098 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6093 uu____6094 uu____6098
    | uu____6099 when is_list e ->
        let uu____6100 =
          let uu____6101 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6102 = extract_from_list e  in
          separate_map_or_flow_last uu____6101
            (fun ps  -> p_noSeqTerm ps false) uu____6102
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6100 FStar_Pprint.rbracket
    | uu____6107 when is_lex_list e ->
        let uu____6108 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6109 =
          let uu____6110 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6111 = extract_from_list e  in
          separate_map_or_flow_last uu____6110
            (fun ps  -> p_noSeqTerm ps false) uu____6111
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6108 uu____6109 FStar_Pprint.rbracket
    | uu____6116 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6120 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6121 =
          let uu____6122 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6122 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6120 uu____6121 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6126 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6127 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6126 uu____6127
    | FStar_Parser_AST.Op (op,args) when
        let uu____6134 = handleable_op op args  in
        Prims.op_Negation uu____6134 ->
        let uu____6135 =
          let uu____6136 =
            let uu____6137 = FStar_Ident.text_of_id op  in
            let uu____6138 =
              let uu____6139 =
                let uu____6140 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6140
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6139  in
            Prims.strcat uu____6137 uu____6138  in
          Prims.strcat "Operation " uu____6136  in
        failwith uu____6135
    | FStar_Parser_AST.Uvar uu____6141 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6142 = p_term false false e  in
        soft_parens_with_nesting uu____6142
    | FStar_Parser_AST.Const uu____6143 ->
        let uu____6144 = p_term false false e  in
        soft_parens_with_nesting uu____6144
    | FStar_Parser_AST.Op uu____6145 ->
        let uu____6152 = p_term false false e  in
        soft_parens_with_nesting uu____6152
    | FStar_Parser_AST.Tvar uu____6153 ->
        let uu____6154 = p_term false false e  in
        soft_parens_with_nesting uu____6154
    | FStar_Parser_AST.Var uu____6155 ->
        let uu____6156 = p_term false false e  in
        soft_parens_with_nesting uu____6156
    | FStar_Parser_AST.Name uu____6157 ->
        let uu____6158 = p_term false false e  in
        soft_parens_with_nesting uu____6158
    | FStar_Parser_AST.Construct uu____6159 ->
        let uu____6170 = p_term false false e  in
        soft_parens_with_nesting uu____6170
    | FStar_Parser_AST.Abs uu____6171 ->
        let uu____6178 = p_term false false e  in
        soft_parens_with_nesting uu____6178
    | FStar_Parser_AST.App uu____6179 ->
        let uu____6186 = p_term false false e  in
        soft_parens_with_nesting uu____6186
    | FStar_Parser_AST.Let uu____6187 ->
        let uu____6208 = p_term false false e  in
        soft_parens_with_nesting uu____6208
    | FStar_Parser_AST.LetOpen uu____6209 ->
        let uu____6214 = p_term false false e  in
        soft_parens_with_nesting uu____6214
    | FStar_Parser_AST.Seq uu____6215 ->
        let uu____6220 = p_term false false e  in
        soft_parens_with_nesting uu____6220
    | FStar_Parser_AST.Bind uu____6221 ->
        let uu____6228 = p_term false false e  in
        soft_parens_with_nesting uu____6228
    | FStar_Parser_AST.If uu____6229 ->
        let uu____6236 = p_term false false e  in
        soft_parens_with_nesting uu____6236
    | FStar_Parser_AST.Match uu____6237 ->
        let uu____6252 = p_term false false e  in
        soft_parens_with_nesting uu____6252
    | FStar_Parser_AST.TryWith uu____6253 ->
        let uu____6268 = p_term false false e  in
        soft_parens_with_nesting uu____6268
    | FStar_Parser_AST.Ascribed uu____6269 ->
        let uu____6278 = p_term false false e  in
        soft_parens_with_nesting uu____6278
    | FStar_Parser_AST.Record uu____6279 ->
        let uu____6292 = p_term false false e  in
        soft_parens_with_nesting uu____6292
    | FStar_Parser_AST.Project uu____6293 ->
        let uu____6298 = p_term false false e  in
        soft_parens_with_nesting uu____6298
    | FStar_Parser_AST.Product uu____6299 ->
        let uu____6306 = p_term false false e  in
        soft_parens_with_nesting uu____6306
    | FStar_Parser_AST.Sum uu____6307 ->
        let uu____6314 = p_term false false e  in
        soft_parens_with_nesting uu____6314
    | FStar_Parser_AST.QForall uu____6315 ->
        let uu____6328 = p_term false false e  in
        soft_parens_with_nesting uu____6328
    | FStar_Parser_AST.QExists uu____6329 ->
        let uu____6342 = p_term false false e  in
        soft_parens_with_nesting uu____6342
    | FStar_Parser_AST.Refine uu____6343 ->
        let uu____6348 = p_term false false e  in
        soft_parens_with_nesting uu____6348
    | FStar_Parser_AST.NamedTyp uu____6349 ->
        let uu____6354 = p_term false false e  in
        soft_parens_with_nesting uu____6354
    | FStar_Parser_AST.Requires uu____6355 ->
        let uu____6362 = p_term false false e  in
        soft_parens_with_nesting uu____6362
    | FStar_Parser_AST.Ensures uu____6363 ->
        let uu____6370 = p_term false false e  in
        soft_parens_with_nesting uu____6370
    | FStar_Parser_AST.Attributes uu____6371 ->
        let uu____6374 = p_term false false e  in
        soft_parens_with_nesting uu____6374
    | FStar_Parser_AST.Quote uu____6375 ->
        let uu____6380 = p_term false false e  in
        soft_parens_with_nesting uu____6380
    | FStar_Parser_AST.VQuote uu____6381 ->
        let uu____6382 = p_term false false e  in
        soft_parens_with_nesting uu____6382
    | FStar_Parser_AST.Antiquote uu____6383 ->
        let uu____6388 = p_term false false e  in
        soft_parens_with_nesting uu____6388

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___69_6389  ->
    match uu___69_6389 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6393 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6393
    | FStar_Const.Const_string (s,uu____6395) ->
        let uu____6396 = str s  in FStar_Pprint.dquotes uu____6396
    | FStar_Const.Const_bytearray (bytes,uu____6398) ->
        let uu____6403 =
          let uu____6404 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6404  in
        let uu____6405 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6403 uu____6405
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___67_6423 =
          match uu___67_6423 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___68_6427 =
          match uu___68_6427 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6438  ->
               match uu____6438 with
               | (s,w) ->
                   let uu____6445 = signedness s  in
                   let uu____6446 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6445 uu____6446)
            sign_width_opt
           in
        let uu____6447 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6447 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6449 = FStar_Range.string_of_range r  in str uu____6449
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6451 = p_quident lid  in
        let uu____6452 =
          let uu____6453 =
            let uu____6454 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6454  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6453  in
        FStar_Pprint.op_Hat_Hat uu____6451 uu____6452

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6456 = str "u#"  in
    let uu____6457 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6456 uu____6457

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6459;_},u1::u2::[])
        ->
        let uu____6464 =
          let uu____6465 = p_universeFrom u1  in
          let uu____6466 =
            let uu____6467 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6467  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6465 uu____6466  in
        FStar_Pprint.group uu____6464
    | FStar_Parser_AST.App uu____6468 ->
        let uu____6475 = head_and_args u  in
        (match uu____6475 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6501 =
                    let uu____6502 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6503 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6511  ->
                           match uu____6511 with
                           | (u1,uu____6517) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6502 uu____6503  in
                  FStar_Pprint.group uu____6501
              | uu____6518 ->
                  let uu____6519 =
                    let uu____6520 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6520
                     in
                  failwith uu____6519))
    | uu____6521 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 ->
        let uu____6544 = FStar_Ident.text_of_id id1  in str uu____6544
    | FStar_Parser_AST.Paren u1 ->
        let uu____6546 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6546
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6547;_},uu____6548::uu____6549::[])
        ->
        let uu____6552 = p_universeFrom u  in
        soft_parens_with_nesting uu____6552
    | FStar_Parser_AST.App uu____6553 ->
        let uu____6560 = p_universeFrom u  in
        soft_parens_with_nesting uu____6560
    | uu____6561 ->
        let uu____6562 =
          let uu____6563 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6563
           in
        failwith uu____6562

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
       | FStar_Parser_AST.Module (uu____6603,decls) ->
           let uu____6609 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6609
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6618,decls,uu____6620) ->
           let uu____6625 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6625
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6676  ->
         match uu____6676 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6716,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6722,decls,uu____6724) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6769 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6782;
                 FStar_Parser_AST.doc = uu____6783;
                 FStar_Parser_AST.quals = uu____6784;
                 FStar_Parser_AST.attrs = uu____6785;_}::uu____6786 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6792 =
                   let uu____6795 =
                     let uu____6798 = FStar_List.tl ds  in d :: uu____6798
                      in
                   d0 :: uu____6795  in
                 (uu____6792, (d0.FStar_Parser_AST.drange))
             | uu____6803 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6769 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6861 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6861 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6957 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6957, comments1))))))
  