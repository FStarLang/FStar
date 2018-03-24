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
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____660 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____689::(e2,uu____691)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____714 -> false  in
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
    | FStar_Parser_AST.Construct (uu____726,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____737,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____758 = extract_from_list e2  in e1 :: uu____758
    | uu____761 ->
        let uu____762 =
          let uu____763 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____763  in
        failwith uu____762
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____770;
           FStar_Parser_AST.level = uu____771;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____773 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____779;
           FStar_Parser_AST.level = uu____780;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____782;
                                                        FStar_Parser_AST.level
                                                          = uu____783;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____785;
                                                   FStar_Parser_AST.level =
                                                     uu____786;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____788;
                FStar_Parser_AST.level = uu____789;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____791;
           FStar_Parser_AST.level = uu____792;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____794 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____802 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____803;
           FStar_Parser_AST.range = uu____804;
           FStar_Parser_AST.level = uu____805;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____806;
                                                        FStar_Parser_AST.range
                                                          = uu____807;
                                                        FStar_Parser_AST.level
                                                          = uu____808;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____810;
                                                   FStar_Parser_AST.level =
                                                     uu____811;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____812;
                FStar_Parser_AST.range = uu____813;
                FStar_Parser_AST.level = uu____814;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____816;
           FStar_Parser_AST.level = uu____817;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____819 = extract_from_ref_set e1  in
        let uu____822 = extract_from_ref_set e2  in
        FStar_List.append uu____819 uu____822
    | uu____825 ->
        let uu____826 =
          let uu____827 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____827  in
        failwith uu____826
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____833 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____833
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____837 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____837
  
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
      | uu____904 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____918 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____922 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____926 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___54_944  ->
    match uu___54_944 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___55_961  ->
      match uu___55_961 with
      | FStar_Util.Inl c ->
          let uu____970 = FStar_String.get s (Prims.parse_int "0")  in
          uu____970 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____978 .
    Prims.string ->
      ('Auu____978,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____997  ->
      match uu____997 with
      | (assoc_levels,tokens) ->
          let uu____1025 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1025 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1051 .
    Prims.unit ->
      (associativity,('Auu____1051,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1062  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1078 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1078) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1090  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1125 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1125) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1137  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1165 .
    Prims.unit ->
      (associativity,('Auu____1165,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1176  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1192 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1192) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1204  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1232 .
    Prims.unit ->
      (associativity,('Auu____1232,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1243  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1259 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1259) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1271  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1292 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1292) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1304  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1339 .
    Prims.unit ->
      (associativity,('Auu____1339,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1350  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1366 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1366) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1378  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1399 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1399) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1411  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1432 .
    Prims.unit ->
      (associativity,('Auu____1432,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1443  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1459 .
    Prims.unit ->
      (associativity,('Auu____1459,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1470  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1486 .
    Prims.unit ->
      (associativity,('Auu____1486,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1497  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___56_1704 =
    match uu___56_1704 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1744  ->
         match uu____1744 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1824 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1824 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1874) ->
          assoc_levels
      | uu____1918 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1953 .
    ('Auu____1953,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2013 =
        FStar_List.tryFind
          (fun uu____2053  ->
             match uu____2053 with
             | (uu____2071,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2013 with
      | FStar_Pervasives_Native.Some ((uu____2113,l1,uu____2115),uu____2116)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2171 =
            let uu____2172 =
              let uu____2173 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2173  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2172
             in
          failwith uu____2171
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2207 = assign_levels level_associativity_spec op  in
    match uu____2207 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2231 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2231) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2245  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2326 =
      let uu____2340 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2340 (operatorInfix0ad12 ())  in
    uu____2326 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2453 =
      let uu____2467 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2467 opinfix34  in
    uu____2453 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2533 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2533
    then (Prims.parse_int "1")
    else
      (let uu____2535 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2535
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2541 . FStar_Ident.ident -> 'Auu____2541 Prims.list -> Prims.bool =
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
      | uu____2554 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2588 .
    ('Auu____2588 -> FStar_Pprint.document) ->
      'Auu____2588 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2620 = FStar_ST.op_Bang comment_stack  in
          match uu____2620 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2679 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2679
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2716 =
                    let uu____2717 =
                      let uu____2718 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2718
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2717  in
                  comments_before_pos uu____2716 print_pos lookahead_pos))
              else
                (let uu____2720 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2720))
           in
        let uu____2721 =
          let uu____2726 =
            let uu____2727 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2727  in
          let uu____2728 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2726 uu____2728  in
        match uu____2721 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2734 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2734
              else comments  in
            let uu____2740 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2740
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2753 = FStar_ST.op_Bang comment_stack  in
          match uu____2753 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2837 =
                    let uu____2838 =
                      let uu____2839 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2839  in
                    uu____2838 - lbegin  in
                  max k uu____2837  in
                let doc2 =
                  let uu____2841 =
                    let uu____2842 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2843 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2842 uu____2843  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2841  in
                let uu____2844 =
                  let uu____2845 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2845  in
                place_comments_until_pos (Prims.parse_int "1") uu____2844
                  pos_end doc2))
          | uu____2846 ->
              let lnum =
                let uu____2854 =
                  let uu____2855 = FStar_Range.line_of_pos pos_end  in
                  uu____2855 - lbegin  in
                max (Prims.parse_int "1") uu____2854  in
              let uu____2856 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2856
  
let separate_map_with_comments :
  'Auu____2863 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2863 -> FStar_Pprint.document) ->
          'Auu____2863 Prims.list ->
            ('Auu____2863 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2911 x =
              match uu____2911 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2925 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2925 doc1
                     in
                  let uu____2926 =
                    let uu____2927 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2927  in
                  let uu____2928 =
                    let uu____2929 =
                      let uu____2930 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2930  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2929  in
                  (uu____2926, uu____2928)
               in
            let uu____2931 =
              let uu____2938 = FStar_List.hd xs  in
              let uu____2939 = FStar_List.tl xs  in (uu____2938, uu____2939)
               in
            match uu____2931 with
            | (x,xs1) ->
                let init1 =
                  let uu____2955 =
                    let uu____2956 =
                      let uu____2957 = extract_range x  in
                      FStar_Range.end_of_range uu____2957  in
                    FStar_Range.line_of_pos uu____2956  in
                  let uu____2958 =
                    let uu____2959 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2959  in
                  (uu____2955, uu____2958)  in
                let uu____2960 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2960
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3336 =
      let uu____3337 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3338 =
        let uu____3339 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3340 =
          let uu____3341 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3342 =
            let uu____3343 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3343
             in
          FStar_Pprint.op_Hat_Hat uu____3341 uu____3342  in
        FStar_Pprint.op_Hat_Hat uu____3339 uu____3340  in
      FStar_Pprint.op_Hat_Hat uu____3337 uu____3338  in
    FStar_Pprint.group uu____3336

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3346 =
      let uu____3347 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3347  in
    let uu____3348 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3346 FStar_Pprint.space uu____3348
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3349  ->
    match uu____3349 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3383 =
                match uu____3383 with
                | (kwd,arg) ->
                    let uu____3390 = str "@"  in
                    let uu____3391 =
                      let uu____3392 = str kwd  in
                      let uu____3393 =
                        let uu____3394 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3394
                         in
                      FStar_Pprint.op_Hat_Hat uu____3392 uu____3393  in
                    FStar_Pprint.op_Hat_Hat uu____3390 uu____3391
                 in
              let uu____3395 =
                let uu____3396 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3396 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3395
           in
        let uu____3401 =
          let uu____3402 =
            let uu____3403 =
              let uu____3404 =
                let uu____3405 = str doc1  in
                let uu____3406 =
                  let uu____3407 =
                    let uu____3408 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3408  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3407  in
                FStar_Pprint.op_Hat_Hat uu____3405 uu____3406  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3404  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3403  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3402  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3401

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3412 =
          let uu____3413 = str "val"  in
          let uu____3414 =
            let uu____3415 =
              let uu____3416 = p_lident lid  in
              let uu____3417 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3416 uu____3417  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3415  in
          FStar_Pprint.op_Hat_Hat uu____3413 uu____3414  in
        let uu____3418 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3412 uu____3418
    | FStar_Parser_AST.TopLevelLet (uu____3419,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3444 =
               let uu____3445 = str "let"  in
               let uu____3446 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3445 uu____3446  in
             FStar_Pprint.group uu____3444) lbs
    | uu____3447 -> FStar_Pprint.empty

and (p_list :
  (FStar_Ident.ident -> FStar_Pprint.document) ->
    FStar_Pprint.document ->
      FStar_Ident.ident Prims.list -> FStar_Pprint.document)
  =
  fun f  ->
    fun sep  ->
      fun l  ->
        let rec p_list' uu___57_3460 =
          match uu___57_3460 with
          | [] -> FStar_Pprint.empty
          | x::[] -> f x
          | x::xs ->
              let uu____3468 = f x  in
              let uu____3469 =
                let uu____3470 = p_list' xs  in
                FStar_Pprint.op_Hat_Hat sep uu____3470  in
              FStar_Pprint.op_Hat_Hat uu____3468 uu____3469
           in
        let uu____3471 = str "["  in
        let uu____3472 =
          let uu____3473 = p_list' l  in
          let uu____3474 = str "]"  in
          FStar_Pprint.op_Hat_Hat uu____3473 uu____3474  in
        FStar_Pprint.op_Hat_Hat uu____3471 uu____3472

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3477 =
          let uu____3478 = str "open"  in
          let uu____3479 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3478 uu____3479  in
        FStar_Pprint.group uu____3477
    | FStar_Parser_AST.Include uid ->
        let uu____3481 =
          let uu____3482 = str "include"  in
          let uu____3483 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3482 uu____3483  in
        FStar_Pprint.group uu____3481
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3486 =
          let uu____3487 = str "module"  in
          let uu____3488 =
            let uu____3489 =
              let uu____3490 = p_uident uid1  in
              let uu____3491 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3490 uu____3491  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3489  in
          FStar_Pprint.op_Hat_Hat uu____3487 uu____3488  in
        let uu____3492 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3486 uu____3492
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3494 =
          let uu____3495 = str "module"  in
          let uu____3496 =
            let uu____3497 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3497  in
          FStar_Pprint.op_Hat_Hat uu____3495 uu____3496  in
        FStar_Pprint.group uu____3494
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3530 = str "effect"  in
          let uu____3531 =
            let uu____3532 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3532  in
          FStar_Pprint.op_Hat_Hat uu____3530 uu____3531  in
        let uu____3533 =
          let uu____3534 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3534 FStar_Pprint.equals
           in
        let uu____3535 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3533 uu____3535
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3553 = str "type"  in
        let uu____3554 = str "and"  in
        precede_break_separate_map uu____3553 uu____3554 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3576 = str "let"  in
          let uu____3577 =
            let uu____3578 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3578 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3576 uu____3577  in
        let uu____3579 =
          let uu____3580 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3580 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3579 p_letbinding lbs
          (fun uu____3588  ->
             match uu____3588 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3597 =
          let uu____3598 = str "val"  in
          let uu____3599 =
            let uu____3600 =
              let uu____3601 = p_lident lid  in
              let uu____3602 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3601 uu____3602  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3600  in
          FStar_Pprint.op_Hat_Hat uu____3598 uu____3599  in
        let uu____3603 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3597 uu____3603
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3607 =
            let uu____3608 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3608 FStar_Util.is_upper  in
          if uu____3607
          then FStar_Pprint.empty
          else
            (let uu____3610 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3610 FStar_Pprint.space)
           in
        let uu____3611 =
          let uu____3612 =
            let uu____3613 = p_ident id1  in
            let uu____3614 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3613 uu____3614  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3612  in
        let uu____3615 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3611 uu____3615
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3622 = str "exception"  in
        let uu____3623 =
          let uu____3624 =
            let uu____3625 = p_uident uid  in
            let uu____3626 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3630 =
                     let uu____3631 = str "of"  in
                     let uu____3632 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3631 uu____3632  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3630) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3625 uu____3626  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3624  in
        FStar_Pprint.op_Hat_Hat uu____3622 uu____3623
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3634 = str "new_effect"  in
        let uu____3635 =
          let uu____3636 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3636  in
        FStar_Pprint.op_Hat_Hat uu____3634 uu____3635
    | FStar_Parser_AST.SubEffect se ->
        let uu____3638 = str "sub_effect"  in
        let uu____3639 =
          let uu____3640 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3640  in
        FStar_Pprint.op_Hat_Hat uu____3638 uu____3639
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3643 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3643 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3644 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3645) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice (ids,t) ->
        let uu____3668 = str "%splice"  in
        let uu____3669 =
          let uu____3670 =
            let uu____3671 = str ";"  in p_list p_uident uu____3671 ids  in
          let uu____3672 =
            let uu____3673 = p_term false false t  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3673  in
          FStar_Pprint.op_Hat_Hat uu____3670 uu____3672  in
        FStar_Pprint.op_Hat_Hat uu____3668 uu____3669

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___58_3674  ->
    match uu___58_3674 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3676 = str "#set-options"  in
        let uu____3677 =
          let uu____3678 =
            let uu____3679 = str s  in FStar_Pprint.dquotes uu____3679  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3678  in
        FStar_Pprint.op_Hat_Hat uu____3676 uu____3677
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3683 = str "#reset-options"  in
        let uu____3684 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3688 =
                 let uu____3689 = str s  in FStar_Pprint.dquotes uu____3689
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3688) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3683 uu____3684
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
  fun uu____3713  ->
    match uu____3713 with
    | (typedecl,fsdoc_opt) ->
        let uu____3726 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3727 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3726 uu____3727

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___59_3728  ->
    match uu___59_3728 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3743 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3759 =
          let uu____3760 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3760  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3807 =
          match uu____3807 with
          | (lid1,t,doc_opt) ->
              let uu____3823 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3823
           in
        let p_fields uu____3837 =
          let uu____3838 =
            let uu____3839 =
              let uu____3840 =
                let uu____3841 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3841 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3840  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3839  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3838  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3905 =
          match uu____3905 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3931 =
                  let uu____3932 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3932  in
                FStar_Range.extend_to_end_of_line uu____3931  in
              let p_constructorBranch decl =
                let uu____3965 =
                  let uu____3966 =
                    let uu____3967 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3967  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3966  in
                FStar_Pprint.group uu____3965  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3987 =
          let uu____3988 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3988  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4003  ->
             let uu____4004 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____4004)

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
            let uu____4019 = p_ident lid  in
            let uu____4020 =
              let uu____4021 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4021  in
            FStar_Pprint.op_Hat_Hat uu____4019 uu____4020
          else
            (let binders_doc =
               let uu____4024 = p_typars bs  in
               let uu____4025 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4029 =
                        let uu____4030 =
                          let uu____4031 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4031
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4030
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____4029) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____4024 uu____4025  in
             let uu____4032 = p_ident lid  in
             let uu____4033 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4032 binders_doc uu____4033)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4035  ->
      match uu____4035 with
      | (lid,t,doc_opt) ->
          let uu____4051 =
            let uu____4052 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4053 =
              let uu____4054 = p_lident lid  in
              let uu____4055 =
                let uu____4056 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4056  in
              FStar_Pprint.op_Hat_Hat uu____4054 uu____4055  in
            FStar_Pprint.op_Hat_Hat uu____4052 uu____4053  in
          FStar_Pprint.group uu____4051

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4057  ->
    match uu____4057 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4085 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4086 =
          let uu____4087 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4088 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4093 =
                   let uu____4094 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4094  in
                 let uu____4095 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4093 uu____4095) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4087 uu____4088  in
        FStar_Pprint.op_Hat_Hat uu____4085 uu____4086

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4096  ->
    match uu____4096 with
    | (pat,uu____4102) ->
        let uu____4103 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4122 =
                let uu____4123 =
                  let uu____4124 =
                    let uu____4125 =
                      let uu____4126 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4126
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4125  in
                  FStar_Pprint.group uu____4124  in
                FStar_Pprint.op_Hat_Hat break1 uu____4123  in
              (pat1, uu____4122)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4138 =
                let uu____4139 =
                  let uu____4140 =
                    let uu____4141 =
                      let uu____4142 =
                        let uu____4143 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4143
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4142
                       in
                    FStar_Pprint.group uu____4141  in
                  let uu____4144 =
                    let uu____4145 =
                      let uu____4146 = str "by"  in
                      let uu____4147 =
                        let uu____4148 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4148
                         in
                      FStar_Pprint.op_Hat_Hat uu____4146 uu____4147  in
                    FStar_Pprint.group uu____4145  in
                  FStar_Pprint.op_Hat_Hat uu____4140 uu____4144  in
                FStar_Pprint.op_Hat_Hat break1 uu____4139  in
              (pat1, uu____4138)
          | uu____4149 -> (pat, FStar_Pprint.empty)  in
        (match uu____4103 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4153);
                     FStar_Parser_AST.prange = uu____4154;_},pats)
                  ->
                  let uu____4164 =
                    let uu____4165 = p_lident x  in
                    let uu____4166 =
                      let uu____4167 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4167 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4165 uu____4166  in
                  FStar_Pprint.group uu____4164
              | uu____4168 ->
                  let uu____4169 =
                    let uu____4170 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4170 ascr_doc  in
                  FStar_Pprint.group uu____4169))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4171  ->
    match uu____4171 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4179 =
          let uu____4180 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4180  in
        let uu____4181 = p_term false false e  in
        prefix2 uu____4179 uu____4181

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___60_4182  ->
    match uu___60_4182 with
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
        let uu____4207 = p_uident uid  in
        let uu____4208 = p_binders true bs  in
        let uu____4209 =
          let uu____4210 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4210  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4207 uu____4208 uu____4209

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
          let uu____4219 =
            let uu____4220 =
              let uu____4221 =
                let uu____4222 = p_uident uid  in
                let uu____4223 = p_binders true bs  in
                let uu____4224 =
                  let uu____4225 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4225  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4222 uu____4223 uu____4224
                 in
              FStar_Pprint.group uu____4221  in
            let uu____4226 =
              let uu____4227 = str "with"  in
              let uu____4228 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4227 uu____4228  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4220 uu____4226  in
          braces_with_nesting uu____4219

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
          let uu____4259 =
            let uu____4260 = p_lident lid  in
            let uu____4261 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4260 uu____4261  in
          let uu____4262 = p_simpleTerm ps false e  in
          prefix2 uu____4259 uu____4262
      | uu____4263 ->
          let uu____4264 =
            let uu____4265 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4265
             in
          failwith uu____4264

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4323 =
        match uu____4323 with
        | (kwd,t) ->
            let uu____4330 =
              let uu____4331 = str kwd  in
              let uu____4332 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4331 uu____4332  in
            let uu____4333 = p_simpleTerm ps false t  in
            prefix2 uu____4330 uu____4333
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4338 =
      let uu____4339 =
        let uu____4340 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4341 =
          let uu____4342 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4342  in
        FStar_Pprint.op_Hat_Hat uu____4340 uu____4341  in
      let uu____4343 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4339 uu____4343  in
    let uu____4344 =
      let uu____4345 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4345  in
    FStar_Pprint.op_Hat_Hat uu____4338 uu____4344

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___61_4346  ->
    match uu___61_4346 with
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
    let uu____4348 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4348

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___62_4349  ->
    match uu___62_4349 with
    | FStar_Parser_AST.Rec  ->
        let uu____4350 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4350
    | FStar_Parser_AST.Mutable  ->
        let uu____4351 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4351
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___63_4352  ->
    match uu___63_4352 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4357 =
          let uu____4358 =
            let uu____4359 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4359  in
          FStar_Pprint.separate_map uu____4358 p_tuplePattern pats  in
        FStar_Pprint.group uu____4357
    | uu____4360 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4367 =
          let uu____4368 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4368 p_constructorPattern pats  in
        FStar_Pprint.group uu____4367
    | uu____4369 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4372;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4377 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4378 = p_constructorPattern hd1  in
        let uu____4379 = p_constructorPattern tl1  in
        infix0 uu____4377 uu____4378 uu____4379
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4381;_},pats)
        ->
        let uu____4387 = p_quident uid  in
        let uu____4388 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4387 uu____4388
    | uu____4389 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4405;
               FStar_Parser_AST.blevel = uu____4406;
               FStar_Parser_AST.aqual = uu____4407;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4413 =
               let uu____4414 = p_ident lid  in
               p_refinement aqual uu____4414 t1 phi  in
             soft_parens_with_nesting uu____4413
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4416;
               FStar_Parser_AST.blevel = uu____4417;
               FStar_Parser_AST.aqual = uu____4418;_},phi))
             ->
             let uu____4420 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4420
         | uu____4421 ->
             let uu____4426 =
               let uu____4427 = p_tuplePattern pat  in
               let uu____4428 =
                 let uu____4429 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4430 =
                   let uu____4431 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4431  in
                 FStar_Pprint.op_Hat_Hat uu____4429 uu____4430  in
               FStar_Pprint.op_Hat_Hat uu____4427 uu____4428  in
             soft_parens_with_nesting uu____4426)
    | FStar_Parser_AST.PatList pats ->
        let uu____4435 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4435 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4450 =
          match uu____4450 with
          | (lid,pat) ->
              let uu____4457 = p_qlident lid  in
              let uu____4458 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4457 uu____4458
           in
        let uu____4459 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4459
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4469 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4470 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4471 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4469 uu____4470 uu____4471
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4482 =
          let uu____4483 =
            let uu____4484 = str (FStar_Ident.text_of_id op)  in
            let uu____4485 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4484 uu____4485  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4483  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4482
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4493 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4494 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4493 uu____4494
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4496 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4499;
           FStar_Parser_AST.prange = uu____4500;_},uu____4501)
        ->
        let uu____4506 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4506
    | FStar_Parser_AST.PatTuple (uu____4507,false ) ->
        let uu____4512 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4512
    | uu____4513 ->
        let uu____4514 =
          let uu____4515 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4515  in
        failwith uu____4514

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4519 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4520 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4519 uu____4520
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4527;
                   FStar_Parser_AST.blevel = uu____4528;
                   FStar_Parser_AST.aqual = uu____4529;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4531 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4531 t1 phi
            | uu____4532 ->
                let uu____4533 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4534 =
                  let uu____4535 = p_lident lid  in
                  let uu____4536 =
                    let uu____4537 =
                      let uu____4538 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4539 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4538 uu____4539  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4537  in
                  FStar_Pprint.op_Hat_Hat uu____4535 uu____4536  in
                FStar_Pprint.op_Hat_Hat uu____4533 uu____4534
             in
          if is_atomic
          then
            let uu____4540 =
              let uu____4541 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4541  in
            FStar_Pprint.group uu____4540
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4543 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4550;
                  FStar_Parser_AST.blevel = uu____4551;
                  FStar_Parser_AST.aqual = uu____4552;_},phi)
               ->
               if is_atomic
               then
                 let uu____4554 =
                   let uu____4555 =
                     let uu____4556 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4556 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4555  in
                 FStar_Pprint.group uu____4554
               else
                 (let uu____4558 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4558)
           | uu____4559 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4567 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4568 =
            let uu____4569 =
              let uu____4570 =
                let uu____4571 = p_appTerm t  in
                let uu____4572 =
                  let uu____4573 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4573  in
                FStar_Pprint.op_Hat_Hat uu____4571 uu____4572  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4570  in
            FStar_Pprint.op_Hat_Hat binder uu____4569  in
          FStar_Pprint.op_Hat_Hat uu____4567 uu____4568

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
            let uu____4596 =
              let uu____4597 =
                let uu____4598 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4598 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4597  in
            let uu____4599 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4596 uu____4599
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4603 =
              let uu____4604 =
                let uu____4605 =
                  let uu____4606 = p_lident x  in
                  let uu____4607 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4606 uu____4607  in
                let uu____4608 =
                  let uu____4609 = p_noSeqTerm true false e1  in
                  let uu____4610 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4609 uu____4610  in
                op_Hat_Slash_Plus_Hat uu____4605 uu____4608  in
              FStar_Pprint.group uu____4604  in
            let uu____4611 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4603 uu____4611
        | uu____4612 ->
            let uu____4613 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4613

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
            let uu____4624 =
              let uu____4625 = p_tmIff e1  in
              let uu____4626 =
                let uu____4627 =
                  let uu____4628 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4628
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4627  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4625 uu____4626  in
            FStar_Pprint.group uu____4624
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4634 =
              let uu____4635 = p_tmIff e1  in
              let uu____4636 =
                let uu____4637 =
                  let uu____4638 =
                    let uu____4639 = p_typ false false t  in
                    let uu____4640 =
                      let uu____4641 = str "by"  in
                      let uu____4642 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4641 uu____4642  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4639 uu____4640  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4638
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4637  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4635 uu____4636  in
            FStar_Pprint.group uu____4634
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4643;_},e1::e2::e3::[])
            ->
            let uu____4649 =
              let uu____4650 =
                let uu____4651 =
                  let uu____4652 = p_atomicTermNotQUident e1  in
                  let uu____4653 =
                    let uu____4654 =
                      let uu____4655 =
                        let uu____4656 = p_term false false e2  in
                        soft_parens_with_nesting uu____4656  in
                      let uu____4657 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4655 uu____4657  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4654  in
                  FStar_Pprint.op_Hat_Hat uu____4652 uu____4653  in
                FStar_Pprint.group uu____4651  in
              let uu____4658 =
                let uu____4659 = p_noSeqTerm ps pb e3  in jump2 uu____4659
                 in
              FStar_Pprint.op_Hat_Hat uu____4650 uu____4658  in
            FStar_Pprint.group uu____4649
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4660;_},e1::e2::e3::[])
            ->
            let uu____4666 =
              let uu____4667 =
                let uu____4668 =
                  let uu____4669 = p_atomicTermNotQUident e1  in
                  let uu____4670 =
                    let uu____4671 =
                      let uu____4672 =
                        let uu____4673 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4673  in
                      let uu____4674 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4672 uu____4674  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4671  in
                  FStar_Pprint.op_Hat_Hat uu____4669 uu____4670  in
                FStar_Pprint.group uu____4668  in
              let uu____4675 =
                let uu____4676 = p_noSeqTerm ps pb e3  in jump2 uu____4676
                 in
              FStar_Pprint.op_Hat_Hat uu____4667 uu____4675  in
            FStar_Pprint.group uu____4666
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4686 =
              let uu____4687 = str "requires"  in
              let uu____4688 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4687 uu____4688  in
            FStar_Pprint.group uu____4686
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4698 =
              let uu____4699 = str "ensures"  in
              let uu____4700 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4699 uu____4700  in
            FStar_Pprint.group uu____4698
        | FStar_Parser_AST.Attributes es ->
            let uu____4704 =
              let uu____4705 = str "attributes"  in
              let uu____4706 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4705 uu____4706  in
            FStar_Pprint.group uu____4704
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4710 =
                let uu____4711 =
                  let uu____4712 = str "if"  in
                  let uu____4713 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4712 uu____4713  in
                let uu____4714 =
                  let uu____4715 = str "then"  in
                  let uu____4716 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4715 uu____4716  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4711 uu____4714  in
              FStar_Pprint.group uu____4710
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4719,uu____4720,e31) when
                     is_unit e31 ->
                     let uu____4722 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4722
                 | uu____4723 -> p_noSeqTerm false false e2  in
               let uu____4724 =
                 let uu____4725 =
                   let uu____4726 = str "if"  in
                   let uu____4727 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4726 uu____4727  in
                 let uu____4728 =
                   let uu____4729 =
                     let uu____4730 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4730 e2_doc  in
                   let uu____4731 =
                     let uu____4732 = str "else"  in
                     let uu____4733 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4732 uu____4733  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4729 uu____4731  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4725 uu____4728  in
               FStar_Pprint.group uu____4724)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4756 =
              let uu____4757 =
                let uu____4758 =
                  let uu____4759 = str "try"  in
                  let uu____4760 = p_noSeqTerm false false e1  in
                  prefix2 uu____4759 uu____4760  in
                let uu____4761 =
                  let uu____4762 = str "with"  in
                  let uu____4763 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4762 uu____4763  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4758 uu____4761  in
              FStar_Pprint.group uu____4757  in
            let uu____4772 = paren_if (ps || pb)  in uu____4772 uu____4756
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4797 =
              let uu____4798 =
                let uu____4799 =
                  let uu____4800 = str "match"  in
                  let uu____4801 = p_noSeqTerm false false e1  in
                  let uu____4802 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4800 uu____4801 uu____4802
                   in
                let uu____4803 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4799 uu____4803  in
              FStar_Pprint.group uu____4798  in
            let uu____4812 = paren_if (ps || pb)  in uu____4812 uu____4797
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4817 =
              let uu____4818 =
                let uu____4819 =
                  let uu____4820 = str "let open"  in
                  let uu____4821 = p_quident uid  in
                  let uu____4822 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4820 uu____4821 uu____4822
                   in
                let uu____4823 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4819 uu____4823  in
              FStar_Pprint.group uu____4818  in
            let uu____4824 = paren_if ps  in uu____4824 uu____4817
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____4880 is_last =
              match uu____4880 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____4913 =
                          let uu____4914 = str "let"  in
                          let uu____4915 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4914 uu____4915
                           in
                        FStar_Pprint.group uu____4913
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____4916 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____4921 =
                    if is_last
                    then
                      let uu____4922 =
                        let uu____4923 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____4924 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____4923 doc_expr
                          uu____4924
                         in
                      FStar_Pprint.group uu____4922
                    else
                      (let uu____4926 =
                         let uu____4927 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____4927 doc_expr
                          in
                       FStar_Pprint.group uu____4926)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____4921
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____4973 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____4973
                     else
                       (let uu____4981 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____4981)) lbs
               in
            let lbs_doc =
              let uu____4989 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____4989  in
            let uu____4990 =
              let uu____4991 =
                let uu____4992 =
                  let uu____4993 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4993
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____4992  in
              FStar_Pprint.group uu____4991  in
            let uu____4994 = paren_if ps  in uu____4994 uu____4990
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4999;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5002;
                                                             FStar_Parser_AST.level
                                                               = uu____5003;_})
            when matches_var maybe_x x ->
            let uu____5030 =
              let uu____5031 =
                let uu____5032 = str "function"  in
                let uu____5033 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5032 uu____5033  in
              FStar_Pprint.group uu____5031  in
            let uu____5042 = paren_if (ps || pb)  in uu____5042 uu____5030
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5046 =
              let uu____5047 = str "quote"  in
              let uu____5048 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5047 uu____5048  in
            FStar_Pprint.group uu____5046
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5050 =
              let uu____5051 = str "`"  in
              let uu____5052 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5051 uu____5052  in
            FStar_Pprint.group uu____5050
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5054 =
              let uu____5055 = str "%`"  in
              let uu____5056 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5055 uu____5056  in
            FStar_Pprint.group uu____5054
        | FStar_Parser_AST.Antiquote (false ,e1) ->
            let uu____5058 =
              let uu____5059 = str "`#"  in
              let uu____5060 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5059 uu____5060  in
            FStar_Pprint.group uu____5058
        | FStar_Parser_AST.Antiquote (true ,e1) ->
            let uu____5062 =
              let uu____5063 = str "`@"  in
              let uu____5064 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5063 uu____5064  in
            FStar_Pprint.group uu____5062
        | uu____5065 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___64_5066  ->
    match uu___64_5066 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5078 =
          let uu____5079 =
            let uu____5080 = str "[@"  in
            let uu____5081 =
              let uu____5082 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5083 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5082 uu____5083  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5080 uu____5081  in
          FStar_Pprint.group uu____5079  in
        FStar_Pprint.op_Hat_Hat uu____5078 break1

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
            let uu____5105 =
              let uu____5106 =
                let uu____5107 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5107 FStar_Pprint.space  in
              let uu____5108 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5106 uu____5108 FStar_Pprint.dot
               in
            let uu____5109 =
              let uu____5110 = p_trigger trigger  in
              let uu____5111 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5110 uu____5111  in
            prefix2 uu____5105 uu____5109
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5127 =
              let uu____5128 =
                let uu____5129 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5129 FStar_Pprint.space  in
              let uu____5130 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5128 uu____5130 FStar_Pprint.dot
               in
            let uu____5131 =
              let uu____5132 = p_trigger trigger  in
              let uu____5133 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5132 uu____5133  in
            prefix2 uu____5127 uu____5131
        | uu____5134 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5136 -> str "forall"
    | FStar_Parser_AST.QExists uu____5149 -> str "exists"
    | uu____5162 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___65_5163  ->
    match uu___65_5163 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5175 =
          let uu____5176 =
            let uu____5177 = str "pattern"  in
            let uu____5178 =
              let uu____5179 =
                let uu____5180 = p_disjunctivePats pats  in jump2 uu____5180
                 in
              let uu____5181 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5179 uu____5181  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5177 uu____5178  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5176  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5175

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5187 = str "\\/"  in
    FStar_Pprint.separate_map uu____5187 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5193 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5193

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5203 =
              let uu____5204 =
                let uu____5205 = str "fun"  in
                let uu____5206 =
                  let uu____5207 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5207
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5205 uu____5206  in
              let uu____5208 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5204 uu____5208  in
            let uu____5209 = paren_if ps  in uu____5209 uu____5203
        | uu____5212 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5216  ->
      match uu____5216 with
      | (pat,when_opt,e) ->
          let uu____5232 =
            let uu____5233 =
              let uu____5234 =
                let uu____5235 =
                  let uu____5236 =
                    let uu____5237 = p_disjunctivePattern pat  in
                    let uu____5238 =
                      let uu____5239 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5239 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5237 uu____5238  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5236  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5235  in
              FStar_Pprint.group uu____5234  in
            let uu____5240 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5233 uu____5240  in
          FStar_Pprint.group uu____5232

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___66_5241  ->
    match uu___66_5241 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5245 = str "when"  in
        let uu____5246 =
          let uu____5247 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5247 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5245 uu____5246

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5249;_},e1::e2::[])
        ->
        let uu____5254 = str "<==>"  in
        let uu____5255 = p_tmImplies e1  in
        let uu____5256 = p_tmIff e2  in
        infix0 uu____5254 uu____5255 uu____5256
    | uu____5257 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5259;_},e1::e2::[])
        ->
        let uu____5264 = str "==>"  in
        let uu____5265 = p_tmArrow p_tmFormula e1  in
        let uu____5266 = p_tmImplies e2  in
        infix0 uu____5264 uu____5265 uu____5266
    | uu____5267 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5278 =
            let uu____5279 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5284 = p_binder false b  in
                   let uu____5285 =
                     let uu____5286 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5286
                      in
                   FStar_Pprint.op_Hat_Hat uu____5284 uu____5285) bs
               in
            let uu____5287 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5279 uu____5287  in
          FStar_Pprint.group uu____5278
      | uu____5288 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5290;_},e1::e2::[])
        ->
        let uu____5295 = str "\\/"  in
        let uu____5296 = p_tmFormula e1  in
        let uu____5297 = p_tmConjunction e2  in
        infix0 uu____5295 uu____5296 uu____5297
    | uu____5298 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5300;_},e1::e2::[])
        ->
        let uu____5305 = str "/\\"  in
        let uu____5306 = p_tmConjunction e1  in
        let uu____5307 = p_tmTuple e2  in
        infix0 uu____5305 uu____5306 uu____5307
    | uu____5308 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5325 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5325
          (fun uu____5333  ->
             match uu____5333 with | (e1,uu____5339) -> p_tmEq e1) args
    | uu____5340 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5345 =
             let uu____5346 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5346  in
           FStar_Pprint.group uu____5345)

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
               ((FStar_Ident.text_of_id op) = "="))
              || ((FStar_Ident.text_of_id op) = "|>")
            ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5409 = levels op1  in
            (match uu____5409 with
             | (left1,mine,right1) ->
                 let uu____5419 =
                   let uu____5420 = FStar_All.pipe_left str op1  in
                   let uu____5421 = p_tmEqWith' p_X left1 e1  in
                   let uu____5422 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5420 uu____5421 uu____5422  in
                 paren_if_gt curr mine uu____5419)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5423;_},e1::e2::[])
            ->
            let uu____5428 =
              let uu____5429 = p_tmEqWith p_X e1  in
              let uu____5430 =
                let uu____5431 =
                  let uu____5432 =
                    let uu____5433 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5433  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5432  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5431  in
              FStar_Pprint.op_Hat_Hat uu____5429 uu____5430  in
            FStar_Pprint.group uu____5428
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5434;_},e1::[])
            ->
            let uu____5438 = levels "-"  in
            (match uu____5438 with
             | (left1,mine,right1) ->
                 let uu____5448 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5448)
        | uu____5449 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5520)::(e2,uu____5522)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5542 = is_list e  in Prims.op_Negation uu____5542)
            ->
            let op = "::"  in
            let uu____5544 = levels op  in
            (match uu____5544 with
             | (left1,mine,right1) ->
                 let uu____5554 =
                   let uu____5555 = str op  in
                   let uu____5556 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5557 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5555 uu____5556 uu____5557  in
                 paren_if_gt curr mine uu____5554)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5565 = levels op  in
            (match uu____5565 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5579 = p_binder false b  in
                   let uu____5580 =
                     let uu____5581 =
                       let uu____5582 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5582 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5581
                      in
                   FStar_Pprint.op_Hat_Hat uu____5579 uu____5580  in
                 let uu____5583 =
                   let uu____5584 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5585 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5584 uu____5585  in
                 paren_if_gt curr mine uu____5583)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5592 = levels op1  in
            (match uu____5592 with
             | (left1,mine,right1) ->
                 let uu____5602 =
                   let uu____5603 = str op1  in
                   let uu____5604 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5605 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5603 uu____5604 uu____5605  in
                 paren_if_gt curr mine uu____5602)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5624 =
              let uu____5625 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5626 =
                let uu____5627 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5627 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5625 uu____5626  in
            braces_with_nesting uu____5624
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5632;_},e1::[])
            ->
            let uu____5636 =
              let uu____5637 = str "~"  in
              let uu____5638 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5637 uu____5638  in
            FStar_Pprint.group uu____5636
        | uu____5639 -> p_X e

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
        let uu____5646 =
          let uu____5647 = p_lidentOrUnderscore lid  in
          let uu____5648 =
            let uu____5649 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5649  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5647 uu____5648  in
        FStar_Pprint.group uu____5646
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5652 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5654 = p_appTerm e  in
    let uu____5655 =
      let uu____5656 =
        let uu____5657 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5657 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5656  in
    FStar_Pprint.op_Hat_Hat uu____5654 uu____5655

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5662 =
            let uu____5663 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5663 t phi  in
          soft_parens_with_nesting uu____5662
      | FStar_Parser_AST.TAnnotated uu____5664 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5669 ->
          let uu____5670 =
            let uu____5671 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5671
             in
          failwith uu____5670
      | FStar_Parser_AST.TVariable uu____5672 ->
          let uu____5673 =
            let uu____5674 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5674
             in
          failwith uu____5673
      | FStar_Parser_AST.NoName uu____5675 ->
          let uu____5676 =
            let uu____5677 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5677
             in
          failwith uu____5676

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5679  ->
      match uu____5679 with
      | (lid,e) ->
          let uu____5686 =
            let uu____5687 = p_qlident lid  in
            let uu____5688 =
              let uu____5689 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5689
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5687 uu____5688  in
          FStar_Pprint.group uu____5686

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5691 when is_general_application e ->
        let uu____5698 = head_and_args e  in
        (match uu____5698 with
         | (head1,args) ->
             let uu____5723 =
               let uu____5734 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5734
               then
                 let uu____5764 =
                   FStar_Util.take
                     (fun uu____5788  ->
                        match uu____5788 with
                        | (uu____5793,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5764 with
                 | (fs_typ_args,args1) ->
                     let uu____5831 =
                       let uu____5832 = p_indexingTerm head1  in
                       let uu____5833 =
                         let uu____5834 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5834 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5832 uu____5833  in
                     (uu____5831, args1)
               else
                 (let uu____5846 = p_indexingTerm head1  in
                  (uu____5846, args))
                in
             (match uu____5723 with
              | (head_doc,args1) ->
                  let uu____5867 =
                    let uu____5868 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5868 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5867))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5888 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5888)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5906 =
               let uu____5907 = p_quident lid  in
               let uu____5908 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5907 uu____5908  in
             FStar_Pprint.group uu____5906
         | hd1::tl1 ->
             let uu____5925 =
               let uu____5926 =
                 let uu____5927 =
                   let uu____5928 = p_quident lid  in
                   let uu____5929 = p_argTerm hd1  in
                   prefix2 uu____5928 uu____5929  in
                 FStar_Pprint.group uu____5927  in
               let uu____5930 =
                 let uu____5931 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5931  in
               FStar_Pprint.op_Hat_Hat uu____5926 uu____5930  in
             FStar_Pprint.group uu____5925)
    | uu____5936 -> p_indexingTerm e

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
         (let uu____5945 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5945 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5947 = str "#"  in
        let uu____5948 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5947 uu____5948
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5950  ->
    match uu____5950 with | (e,uu____5956) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5961;_},e1::e2::[])
          ->
          let uu____5966 =
            let uu____5967 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5968 =
              let uu____5969 =
                let uu____5970 = p_term false false e2  in
                soft_parens_with_nesting uu____5970  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5969  in
            FStar_Pprint.op_Hat_Hat uu____5967 uu____5968  in
          FStar_Pprint.group uu____5966
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5971;_},e1::e2::[])
          ->
          let uu____5976 =
            let uu____5977 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5978 =
              let uu____5979 =
                let uu____5980 = p_term false false e2  in
                soft_brackets_with_nesting uu____5980  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5979  in
            FStar_Pprint.op_Hat_Hat uu____5977 uu____5978  in
          FStar_Pprint.group uu____5976
      | uu____5981 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5986 = p_quident lid  in
        let uu____5987 =
          let uu____5988 =
            let uu____5989 = p_term false false e1  in
            soft_parens_with_nesting uu____5989  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5988  in
        FStar_Pprint.op_Hat_Hat uu____5986 uu____5987
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5995 = str (FStar_Ident.text_of_id op)  in
        let uu____5996 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5995 uu____5996
    | uu____5997 -> p_atomicTermNotQUident e

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
         | uu____6004 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6011 = str (FStar_Ident.text_of_id op)  in
        let uu____6012 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6011 uu____6012
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6016 =
          let uu____6017 =
            let uu____6018 = str (FStar_Ident.text_of_id op)  in
            let uu____6019 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6018 uu____6019  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6017  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6016
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6034 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6035 =
          let uu____6036 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6037 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6036 p_tmEq uu____6037  in
        let uu____6044 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6034 uu____6035 uu____6044
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6047 =
          let uu____6048 = p_atomicTermNotQUident e1  in
          let uu____6049 =
            let uu____6050 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6050  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6048 uu____6049
           in
        FStar_Pprint.group uu____6047
    | uu____6051 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6056 = p_quident constr_lid  in
        let uu____6057 =
          let uu____6058 =
            let uu____6059 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6059  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6058  in
        FStar_Pprint.op_Hat_Hat uu____6056 uu____6057
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6061 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6061 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6063 = p_term false false e1  in
        soft_parens_with_nesting uu____6063
    | uu____6064 when is_array e ->
        let es = extract_from_list e  in
        let uu____6068 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6069 =
          let uu____6070 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6070
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6073 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6068 uu____6069 uu____6073
    | uu____6074 when is_list e ->
        let uu____6075 =
          let uu____6076 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6077 = extract_from_list e  in
          separate_map_or_flow_last uu____6076
            (fun ps  -> p_noSeqTerm ps false) uu____6077
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6075 FStar_Pprint.rbracket
    | uu____6082 when is_lex_list e ->
        let uu____6083 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6084 =
          let uu____6085 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6086 = extract_from_list e  in
          separate_map_or_flow_last uu____6085
            (fun ps  -> p_noSeqTerm ps false) uu____6086
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6083 uu____6084 FStar_Pprint.rbracket
    | uu____6091 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6095 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6096 =
          let uu____6097 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6097 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6095 uu____6096 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6101 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6102 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6101 uu____6102
    | FStar_Parser_AST.Op (op,args) when
        let uu____6109 = handleable_op op args  in
        Prims.op_Negation uu____6109 ->
        let uu____6110 =
          let uu____6111 =
            let uu____6112 =
              let uu____6113 =
                let uu____6114 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6114
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6113  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6112  in
          Prims.strcat "Operation " uu____6111  in
        failwith uu____6110
    | FStar_Parser_AST.Uvar uu____6115 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6116 = p_term false false e  in
        soft_parens_with_nesting uu____6116
    | FStar_Parser_AST.Const uu____6117 ->
        let uu____6118 = p_term false false e  in
        soft_parens_with_nesting uu____6118
    | FStar_Parser_AST.Op uu____6119 ->
        let uu____6126 = p_term false false e  in
        soft_parens_with_nesting uu____6126
    | FStar_Parser_AST.Tvar uu____6127 ->
        let uu____6128 = p_term false false e  in
        soft_parens_with_nesting uu____6128
    | FStar_Parser_AST.Var uu____6129 ->
        let uu____6130 = p_term false false e  in
        soft_parens_with_nesting uu____6130
    | FStar_Parser_AST.Name uu____6131 ->
        let uu____6132 = p_term false false e  in
        soft_parens_with_nesting uu____6132
    | FStar_Parser_AST.Construct uu____6133 ->
        let uu____6144 = p_term false false e  in
        soft_parens_with_nesting uu____6144
    | FStar_Parser_AST.Abs uu____6145 ->
        let uu____6152 = p_term false false e  in
        soft_parens_with_nesting uu____6152
    | FStar_Parser_AST.App uu____6153 ->
        let uu____6160 = p_term false false e  in
        soft_parens_with_nesting uu____6160
    | FStar_Parser_AST.Let uu____6161 ->
        let uu____6182 = p_term false false e  in
        soft_parens_with_nesting uu____6182
    | FStar_Parser_AST.LetOpen uu____6183 ->
        let uu____6188 = p_term false false e  in
        soft_parens_with_nesting uu____6188
    | FStar_Parser_AST.Seq uu____6189 ->
        let uu____6194 = p_term false false e  in
        soft_parens_with_nesting uu____6194
    | FStar_Parser_AST.Bind uu____6195 ->
        let uu____6202 = p_term false false e  in
        soft_parens_with_nesting uu____6202
    | FStar_Parser_AST.If uu____6203 ->
        let uu____6210 = p_term false false e  in
        soft_parens_with_nesting uu____6210
    | FStar_Parser_AST.Match uu____6211 ->
        let uu____6226 = p_term false false e  in
        soft_parens_with_nesting uu____6226
    | FStar_Parser_AST.TryWith uu____6227 ->
        let uu____6242 = p_term false false e  in
        soft_parens_with_nesting uu____6242
    | FStar_Parser_AST.Ascribed uu____6243 ->
        let uu____6252 = p_term false false e  in
        soft_parens_with_nesting uu____6252
    | FStar_Parser_AST.Record uu____6253 ->
        let uu____6266 = p_term false false e  in
        soft_parens_with_nesting uu____6266
    | FStar_Parser_AST.Project uu____6267 ->
        let uu____6272 = p_term false false e  in
        soft_parens_with_nesting uu____6272
    | FStar_Parser_AST.Product uu____6273 ->
        let uu____6280 = p_term false false e  in
        soft_parens_with_nesting uu____6280
    | FStar_Parser_AST.Sum uu____6281 ->
        let uu____6288 = p_term false false e  in
        soft_parens_with_nesting uu____6288
    | FStar_Parser_AST.QForall uu____6289 ->
        let uu____6302 = p_term false false e  in
        soft_parens_with_nesting uu____6302
    | FStar_Parser_AST.QExists uu____6303 ->
        let uu____6316 = p_term false false e  in
        soft_parens_with_nesting uu____6316
    | FStar_Parser_AST.Refine uu____6317 ->
        let uu____6322 = p_term false false e  in
        soft_parens_with_nesting uu____6322
    | FStar_Parser_AST.NamedTyp uu____6323 ->
        let uu____6328 = p_term false false e  in
        soft_parens_with_nesting uu____6328
    | FStar_Parser_AST.Requires uu____6329 ->
        let uu____6336 = p_term false false e  in
        soft_parens_with_nesting uu____6336
    | FStar_Parser_AST.Ensures uu____6337 ->
        let uu____6344 = p_term false false e  in
        soft_parens_with_nesting uu____6344
    | FStar_Parser_AST.Attributes uu____6345 ->
        let uu____6348 = p_term false false e  in
        soft_parens_with_nesting uu____6348
    | FStar_Parser_AST.Quote uu____6349 ->
        let uu____6354 = p_term false false e  in
        soft_parens_with_nesting uu____6354
    | FStar_Parser_AST.VQuote uu____6355 ->
        let uu____6356 = p_term false false e  in
        soft_parens_with_nesting uu____6356
    | FStar_Parser_AST.Antiquote uu____6357 ->
        let uu____6362 = p_term false false e  in
        soft_parens_with_nesting uu____6362

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___69_6363  ->
    match uu___69_6363 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6367 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6367
    | FStar_Const.Const_string (s,uu____6369) ->
        let uu____6370 = str s  in FStar_Pprint.dquotes uu____6370
    | FStar_Const.Const_bytearray (bytes,uu____6372) ->
        let uu____6377 =
          let uu____6378 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6378  in
        let uu____6379 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6377 uu____6379
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___67_6397 =
          match uu___67_6397 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___68_6401 =
          match uu___68_6401 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6412  ->
               match uu____6412 with
               | (s,w) ->
                   let uu____6419 = signedness s  in
                   let uu____6420 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6419 uu____6420)
            sign_width_opt
           in
        let uu____6421 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6421 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6423 = FStar_Range.string_of_range r  in str uu____6423
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6425 = p_quident lid  in
        let uu____6426 =
          let uu____6427 =
            let uu____6428 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6428  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6427  in
        FStar_Pprint.op_Hat_Hat uu____6425 uu____6426

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6430 = str "u#"  in
    let uu____6431 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6430 uu____6431

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6433;_},u1::u2::[])
        ->
        let uu____6438 =
          let uu____6439 = p_universeFrom u1  in
          let uu____6440 =
            let uu____6441 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6441  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6439 uu____6440  in
        FStar_Pprint.group uu____6438
    | FStar_Parser_AST.App uu____6442 ->
        let uu____6449 = head_and_args u  in
        (match uu____6449 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6475 =
                    let uu____6476 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6477 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6485  ->
                           match uu____6485 with
                           | (u1,uu____6491) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6476 uu____6477  in
                  FStar_Pprint.group uu____6475
              | uu____6492 ->
                  let uu____6493 =
                    let uu____6494 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6494
                     in
                  failwith uu____6493))
    | uu____6495 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6519 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6519
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6520;_},uu____6521::uu____6522::[])
        ->
        let uu____6525 = p_universeFrom u  in
        soft_parens_with_nesting uu____6525
    | FStar_Parser_AST.App uu____6526 ->
        let uu____6533 = p_universeFrom u  in
        soft_parens_with_nesting uu____6533
    | uu____6534 ->
        let uu____6535 =
          let uu____6536 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6536
           in
        failwith uu____6535

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
       | FStar_Parser_AST.Module (uu____6576,decls) ->
           let uu____6582 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6582
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6591,decls,uu____6593) ->
           let uu____6598 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6598
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6649  ->
         match uu____6649 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6689,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6695,decls,uu____6697) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6742 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6755;
                 FStar_Parser_AST.doc = uu____6756;
                 FStar_Parser_AST.quals = uu____6757;
                 FStar_Parser_AST.attrs = uu____6758;_}::uu____6759 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6765 =
                   let uu____6768 =
                     let uu____6771 = FStar_List.tl ds  in d :: uu____6771
                      in
                   d0 :: uu____6768  in
                 (uu____6765, (d0.FStar_Parser_AST.drange))
             | uu____6776 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6742 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6834 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6834 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6930 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6930, comments1))))))
  