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
  fun uu___51_944  ->
    match uu___51_944 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___52_961  ->
      match uu___52_961 with
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
  let levels_from_associativity l uu___53_1704 =
    match uu___53_1704 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
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
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____2207 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2207) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2221  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2302 =
      let uu____2316 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2316 (operatorInfix0ad12 ())  in
    uu____2302 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2429 =
      let uu____2443 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2443 opinfix34  in
    uu____2429 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2509 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2509
    then (Prims.parse_int "1")
    else
      (let uu____2511 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2511
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2517 . FStar_Ident.ident -> 'Auu____2517 Prims.list -> Prims.bool =
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
      | uu____2530 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2564 .
    ('Auu____2564 -> FStar_Pprint.document) ->
      'Auu____2564 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2596 = FStar_ST.op_Bang comment_stack  in
          match uu____2596 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2655 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2655
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2692 =
                    let uu____2693 =
                      let uu____2694 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2694
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2693  in
                  comments_before_pos uu____2692 print_pos lookahead_pos))
              else
                (let uu____2696 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2696))
           in
        let uu____2697 =
          let uu____2702 =
            let uu____2703 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2703  in
          let uu____2704 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2702 uu____2704  in
        match uu____2697 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2710 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2710
              else comments  in
            let uu____2716 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2716
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2729 = FStar_ST.op_Bang comment_stack  in
          match uu____2729 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2813 =
                    let uu____2814 =
                      let uu____2815 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2815  in
                    uu____2814 - lbegin  in
                  max k uu____2813  in
                let doc2 =
                  let uu____2817 =
                    let uu____2818 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2819 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2818 uu____2819  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2817  in
                let uu____2820 =
                  let uu____2821 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2821  in
                place_comments_until_pos (Prims.parse_int "1") uu____2820
                  pos_end doc2))
          | uu____2822 ->
              let lnum =
                let uu____2830 =
                  let uu____2831 = FStar_Range.line_of_pos pos_end  in
                  uu____2831 - lbegin  in
                max (Prims.parse_int "1") uu____2830  in
              let uu____2832 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2832
  
let separate_map_with_comments :
  'Auu____2839 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2839 -> FStar_Pprint.document) ->
          'Auu____2839 Prims.list ->
            ('Auu____2839 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2887 x =
              match uu____2887 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2901 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2901 doc1
                     in
                  let uu____2902 =
                    let uu____2903 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2903  in
                  let uu____2904 =
                    let uu____2905 =
                      let uu____2906 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2906  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2905  in
                  (uu____2902, uu____2904)
               in
            let uu____2907 =
              let uu____2914 = FStar_List.hd xs  in
              let uu____2915 = FStar_List.tl xs  in (uu____2914, uu____2915)
               in
            match uu____2907 with
            | (x,xs1) ->
                let init1 =
                  let uu____2931 =
                    let uu____2932 =
                      let uu____2933 = extract_range x  in
                      FStar_Range.end_of_range uu____2933  in
                    FStar_Range.line_of_pos uu____2932  in
                  let uu____2934 =
                    let uu____2935 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2935  in
                  (uu____2931, uu____2934)  in
                let uu____2936 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2936
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3273 =
      let uu____3274 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3275 =
        let uu____3276 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3277 =
          let uu____3278 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3279 =
            let uu____3280 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3280
             in
          FStar_Pprint.op_Hat_Hat uu____3278 uu____3279  in
        FStar_Pprint.op_Hat_Hat uu____3276 uu____3277  in
      FStar_Pprint.op_Hat_Hat uu____3274 uu____3275  in
    FStar_Pprint.group uu____3273

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3283 =
      let uu____3284 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3284  in
    let uu____3285 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3283 FStar_Pprint.space uu____3285
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3286  ->
    match uu____3286 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3320 =
                match uu____3320 with
                | (kwd,arg) ->
                    let uu____3327 = str "@"  in
                    let uu____3328 =
                      let uu____3329 = str kwd  in
                      let uu____3330 =
                        let uu____3331 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3331
                         in
                      FStar_Pprint.op_Hat_Hat uu____3329 uu____3330  in
                    FStar_Pprint.op_Hat_Hat uu____3327 uu____3328
                 in
              let uu____3332 =
                let uu____3333 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3333 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3332
           in
        let uu____3338 =
          let uu____3339 =
            let uu____3340 =
              let uu____3341 =
                let uu____3342 = str doc1  in
                let uu____3343 =
                  let uu____3344 =
                    let uu____3345 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3345  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3344  in
                FStar_Pprint.op_Hat_Hat uu____3342 uu____3343  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3341  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3340  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3339  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3338

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3349 =
          let uu____3350 = str "val"  in
          let uu____3351 =
            let uu____3352 =
              let uu____3353 = p_lident lid  in
              let uu____3354 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3353 uu____3354  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3352  in
          FStar_Pprint.op_Hat_Hat uu____3350 uu____3351  in
        let uu____3355 = p_typ false t  in
        op_Hat_Slash_Plus_Hat uu____3349 uu____3355
    | FStar_Parser_AST.TopLevelLet (uu____3356,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3381 =
               let uu____3382 = str "let"  in
               let uu____3383 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3382 uu____3383  in
             FStar_Pprint.group uu____3381) lbs
    | uu____3384 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3387 =
          let uu____3388 = str "open"  in
          let uu____3389 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3388 uu____3389  in
        FStar_Pprint.group uu____3387
    | FStar_Parser_AST.Include uid ->
        let uu____3391 =
          let uu____3392 = str "include"  in
          let uu____3393 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3392 uu____3393  in
        FStar_Pprint.group uu____3391
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3396 =
          let uu____3397 = str "module"  in
          let uu____3398 =
            let uu____3399 =
              let uu____3400 = p_uident uid1  in
              let uu____3401 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3400 uu____3401  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3399  in
          FStar_Pprint.op_Hat_Hat uu____3397 uu____3398  in
        let uu____3402 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3396 uu____3402
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3404 =
          let uu____3405 = str "module"  in
          let uu____3406 =
            let uu____3407 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3407  in
          FStar_Pprint.op_Hat_Hat uu____3405 uu____3406  in
        FStar_Pprint.group uu____3404
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3440 = str "effect"  in
          let uu____3441 =
            let uu____3442 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3442  in
          FStar_Pprint.op_Hat_Hat uu____3440 uu____3441  in
        let uu____3443 =
          let uu____3444 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3444 FStar_Pprint.equals
           in
        let uu____3445 = p_typ false t  in
        op_Hat_Slash_Plus_Hat uu____3443 uu____3445
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3463 = str "type"  in
        let uu____3464 = str "and"  in
        precede_break_separate_map uu____3463 uu____3464 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3486 = str "let"  in
          let uu____3487 =
            let uu____3488 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3488 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3486 uu____3487  in
        let uu____3489 =
          let uu____3490 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3490 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3489 p_letbinding lbs
          (fun uu____3498  ->
             match uu____3498 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
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
        let uu____3513 = p_typ false t  in
        op_Hat_Slash_Plus_Hat uu____3507 uu____3513
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3517 =
            let uu____3518 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3518 FStar_Util.is_upper  in
          if uu____3517
          then FStar_Pprint.empty
          else
            (let uu____3520 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3520 FStar_Pprint.space)
           in
        let uu____3521 =
          let uu____3522 =
            let uu____3523 = p_ident id1  in
            let uu____3524 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3523 uu____3524  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3522  in
        let uu____3525 = p_typ false t  in
        op_Hat_Slash_Plus_Hat uu____3521 uu____3525
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3532 = str "exception"  in
        let uu____3533 =
          let uu____3534 =
            let uu____3535 = p_uident uid  in
            let uu____3536 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3541 = str "of"  in
                   let uu____3542 = p_typ false t  in
                   op_Hat_Slash_Plus_Hat uu____3541 uu____3542) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3535 uu____3536  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3534  in
        FStar_Pprint.op_Hat_Hat uu____3532 uu____3533
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3544 = str "new_effect"  in
        let uu____3545 =
          let uu____3546 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3546  in
        FStar_Pprint.op_Hat_Hat uu____3544 uu____3545
    | FStar_Parser_AST.SubEffect se ->
        let uu____3548 = str "sub_effect"  in
        let uu____3549 =
          let uu____3550 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3550  in
        FStar_Pprint.op_Hat_Hat uu____3548 uu____3549
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3553 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3553 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3554 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3555) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3572  ->
    match uu___54_3572 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3574 = str "#set-options"  in
        let uu____3575 =
          let uu____3576 =
            let uu____3577 = str s  in FStar_Pprint.dquotes uu____3577  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3576  in
        FStar_Pprint.op_Hat_Hat uu____3574 uu____3575
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3581 = str "#reset-options"  in
        let uu____3582 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3586 =
                 let uu____3587 = str s  in FStar_Pprint.dquotes uu____3587
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3586) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3581 uu____3582
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
  fun uu____3611  ->
    match uu____3611 with
    | (typedecl,fsdoc_opt) ->
        let uu____3624 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3625 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3624 uu____3625

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3626  ->
    match uu___55_3626 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3641 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3657 =
          let uu____3658 = p_typ false t  in
          prefix2 FStar_Pprint.equals uu____3658  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3705 =
          match uu____3705 with
          | (lid1,t,doc_opt) ->
              let uu____3721 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3721
           in
        let p_fields uu____3735 =
          let uu____3736 =
            let uu____3737 =
              let uu____3738 =
                let uu____3739 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3739 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3738  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3737  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3736  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3803 =
          match uu____3803 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3829 =
                  let uu____3830 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3830  in
                FStar_Range.extend_to_end_of_line uu____3829  in
              let p_constructorBranch decl =
                let uu____3863 =
                  let uu____3864 =
                    let uu____3865 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3865  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3864  in
                FStar_Pprint.group uu____3863  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3885 =
          let uu____3886 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3886  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3901  ->
             let uu____3902 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3902)

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
            let uu____3917 = p_ident lid  in
            let uu____3918 =
              let uu____3919 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3919  in
            FStar_Pprint.op_Hat_Hat uu____3917 uu____3918
          else
            (let binders_doc =
               let uu____3922 = p_typars bs  in
               let uu____3923 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3927 =
                        let uu____3928 =
                          let uu____3929 = p_typ false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3929
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3928
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3927) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3922 uu____3923  in
             let uu____3930 = p_ident lid  in
             let uu____3931 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3930 binders_doc uu____3931)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____3933  ->
      match uu____3933 with
      | (lid,t,doc_opt) ->
          let uu____3949 =
            let uu____3950 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____3951 =
              let uu____3952 = p_lident lid  in
              let uu____3953 =
                let uu____3954 = p_typ ps t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3954  in
              FStar_Pprint.op_Hat_Hat uu____3952 uu____3953  in
            FStar_Pprint.op_Hat_Hat uu____3950 uu____3951  in
          FStar_Pprint.group uu____3949

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____3955  ->
    match uu____3955 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3983 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3984 =
          let uu____3985 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3986 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3991 =
                   let uu____3992 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3992  in
                 let uu____3993 = p_typ false t  in
                 op_Hat_Slash_Plus_Hat uu____3991 uu____3993) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3985 uu____3986  in
        FStar_Pprint.op_Hat_Hat uu____3983 uu____3984

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3994  ->
    match uu____3994 with
    | (pat,uu____4000) ->
        let uu____4001 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4012 =
                let uu____4013 =
                  let uu____4014 =
                    let uu____4015 =
                      let uu____4016 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4016
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4015  in
                  FStar_Pprint.group uu____4014  in
                FStar_Pprint.op_Hat_Hat break1 uu____4013  in
              (pat1, uu____4012)
          | uu____4017 -> (pat, FStar_Pprint.empty)  in
        (match uu____4001 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4021);
                     FStar_Parser_AST.prange = uu____4022;_},pats)
                  ->
                  let uu____4032 =
                    let uu____4033 = p_lident x  in
                    let uu____4034 =
                      let uu____4035 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4035 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4033 uu____4034  in
                  FStar_Pprint.group uu____4032
              | uu____4036 ->
                  let uu____4037 =
                    let uu____4038 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4038 ascr_doc  in
                  FStar_Pprint.group uu____4037))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4039  ->
    match uu____4039 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4047 =
          let uu____4048 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4048  in
        let uu____4049 = p_term false e  in prefix2 uu____4047 uu____4049

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_4050  ->
    match uu___56_4050 with
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
        let uu____4075 = p_uident uid  in
        let uu____4076 = p_binders true bs  in
        let uu____4077 =
          let uu____4078 = p_simpleTerm false t  in
          prefix2 FStar_Pprint.equals uu____4078  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4075 uu____4076 uu____4077

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
          let uu____4087 =
            let uu____4088 =
              let uu____4089 =
                let uu____4090 = p_uident uid  in
                let uu____4091 = p_binders true bs  in
                let uu____4092 =
                  let uu____4093 = p_typ false t  in
                  prefix2 FStar_Pprint.colon uu____4093  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4090 uu____4091 uu____4092
                 in
              FStar_Pprint.group uu____4089  in
            let uu____4094 =
              let uu____4095 = str "with"  in
              let uu____4096 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4095 uu____4096  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4088 uu____4094  in
          braces_with_nesting uu____4087

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
          let uu____4127 =
            let uu____4128 = p_lident lid  in
            let uu____4129 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4128 uu____4129  in
          let uu____4130 = p_simpleTerm ps e  in
          prefix2 uu____4127 uu____4130
      | uu____4131 ->
          let uu____4132 =
            let uu____4133 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4133
             in
          failwith uu____4132

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4191 =
        match uu____4191 with
        | (kwd,t) ->
            let uu____4198 =
              let uu____4199 = str kwd  in
              let uu____4200 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4199 uu____4200  in
            let uu____4201 = p_simpleTerm ps t  in
            prefix2 uu____4198 uu____4201
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4206 =
      let uu____4207 =
        let uu____4208 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4209 =
          let uu____4210 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4210  in
        FStar_Pprint.op_Hat_Hat uu____4208 uu____4209  in
      let uu____4211 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4207 uu____4211  in
    let uu____4212 =
      let uu____4213 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4213  in
    FStar_Pprint.op_Hat_Hat uu____4206 uu____4212

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4214  ->
    match uu___57_4214 with
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
    let uu____4216 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4216

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4217  ->
    match uu___58_4217 with
    | FStar_Parser_AST.Rec  ->
        let uu____4218 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4218
    | FStar_Parser_AST.Mutable  ->
        let uu____4219 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4219
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4220  ->
    match uu___59_4220 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4225 =
          let uu____4226 =
            let uu____4227 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4227  in
          FStar_Pprint.separate_map uu____4226 p_tuplePattern pats  in
        FStar_Pprint.group uu____4225
    | uu____4228 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4235 =
          let uu____4236 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4236 p_constructorPattern pats  in
        FStar_Pprint.group uu____4235
    | uu____4237 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4240;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4245 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4246 = p_constructorPattern hd1  in
        let uu____4247 = p_constructorPattern tl1  in
        infix0 uu____4245 uu____4246 uu____4247
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4249;_},pats)
        ->
        let uu____4255 = p_quident uid  in
        let uu____4256 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4255 uu____4256
    | uu____4257 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4265;
               FStar_Parser_AST.blevel = uu____4266;
               FStar_Parser_AST.aqual = uu____4267;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4273 =
               let uu____4274 = p_ident lid  in
               p_refinement aqual uu____4274 t1 phi  in
             soft_parens_with_nesting uu____4273
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4276;
               FStar_Parser_AST.blevel = uu____4277;
               FStar_Parser_AST.aqual = uu____4278;_},phi))
             ->
             let uu____4280 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4280
         | uu____4281 ->
             let uu____4286 =
               let uu____4287 = p_tuplePattern pat  in
               let uu____4288 =
                 let uu____4289 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4290 =
                   let uu____4291 = p_typ false t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4291  in
                 FStar_Pprint.op_Hat_Hat uu____4289 uu____4290  in
               FStar_Pprint.op_Hat_Hat uu____4287 uu____4288  in
             soft_parens_with_nesting uu____4286)
    | FStar_Parser_AST.PatList pats ->
        let uu____4295 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4295 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4310 =
          match uu____4310 with
          | (lid,pat) ->
              let uu____4317 = p_qlident lid  in
              let uu____4318 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4317 uu____4318
           in
        let uu____4319 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4319
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4329 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4330 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4331 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4329 uu____4330 uu____4331
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4342 =
          let uu____4343 =
            let uu____4344 = str (FStar_Ident.text_of_id op)  in
            let uu____4345 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4344 uu____4345  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4343  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4342
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4353 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4354 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4353 uu____4354
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4356 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4359;
           FStar_Parser_AST.prange = uu____4360;_},uu____4361)
        ->
        let uu____4366 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4366
    | FStar_Parser_AST.PatTuple (uu____4367,false ) ->
        let uu____4372 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4372
    | uu____4373 ->
        let uu____4374 =
          let uu____4375 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4375  in
        failwith uu____4374

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4379 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4380 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4379 uu____4380
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4387;
                   FStar_Parser_AST.blevel = uu____4388;
                   FStar_Parser_AST.aqual = uu____4389;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4391 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4391 t1 phi
            | uu____4392 ->
                let uu____4393 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4394 =
                  let uu____4395 = p_lident lid  in
                  let uu____4396 =
                    let uu____4397 =
                      let uu____4398 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4399 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4398 uu____4399  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4397  in
                  FStar_Pprint.op_Hat_Hat uu____4395 uu____4396  in
                FStar_Pprint.op_Hat_Hat uu____4393 uu____4394
             in
          if is_atomic
          then
            let uu____4400 =
              let uu____4401 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4401  in
            FStar_Pprint.group uu____4400
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4403 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4410;
                  FStar_Parser_AST.blevel = uu____4411;
                  FStar_Parser_AST.aqual = uu____4412;_},phi)
               ->
               if is_atomic
               then
                 let uu____4414 =
                   let uu____4415 =
                     let uu____4416 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4416 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4415  in
                 FStar_Pprint.group uu____4414
               else
                 (let uu____4418 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4418)
           | uu____4419 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4427 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4428 =
            let uu____4429 =
              let uu____4430 =
                let uu____4431 = p_appTerm t  in
                let uu____4432 =
                  let uu____4433 = p_noSeqTerm false phi  in
                  soft_braces_with_nesting uu____4433  in
                FStar_Pprint.op_Hat_Hat uu____4431 uu____4432  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4430  in
            FStar_Pprint.op_Hat_Hat binder uu____4429  in
          FStar_Pprint.op_Hat_Hat uu____4427 uu____4428

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

and (p_term : Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Seq (e1,e2) ->
          let uu____4455 =
            let uu____4456 =
              let uu____4457 = p_noSeqTerm true e1  in
              FStar_Pprint.op_Hat_Hat uu____4457 FStar_Pprint.semi  in
            FStar_Pprint.group uu____4456  in
          let uu____4458 = p_term ps e2  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4455 uu____4458
      | FStar_Parser_AST.Bind (x,e1,e2) ->
          let uu____4462 =
            let uu____4463 =
              let uu____4464 =
                let uu____4465 = p_lident x  in
                let uu____4466 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                    FStar_Pprint.long_left_arrow
                   in
                FStar_Pprint.op_Hat_Hat uu____4465 uu____4466  in
              let uu____4467 =
                let uu____4468 = p_noSeqTerm true e1  in
                let uu____4469 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                    FStar_Pprint.semi
                   in
                FStar_Pprint.op_Hat_Hat uu____4468 uu____4469  in
              op_Hat_Slash_Plus_Hat uu____4464 uu____4467  in
            FStar_Pprint.group uu____4463  in
          let uu____4470 = p_term ps e2  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4462 uu____4470
      | uu____4471 ->
          let uu____4472 = p_noSeqTerm ps e  in FStar_Pprint.group uu____4472

and (p_noSeqTerm :
  Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  ->
    fun e  -> with_comment (p_noSeqTerm' ps) e e.FStar_Parser_AST.range

and (p_noSeqTerm' :
  Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
          let uu____4481 =
            let uu____4482 = p_tmIff e1  in
            let uu____4483 =
              let uu____4484 =
                let uu____4485 = p_typ ps t  in
                FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4485
                 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4484  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4482 uu____4483  in
          FStar_Pprint.group uu____4481
      | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
          let uu____4491 =
            let uu____4492 = p_tmIff e1  in
            let uu____4493 =
              let uu____4494 =
                let uu____4495 =
                  let uu____4496 = p_typ false t  in
                  let uu____4497 =
                    let uu____4498 = str "by"  in
                    let uu____4499 = p_typ ps tac  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4498 uu____4499  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4496 uu____4497  in
                FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4495
                 in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4494  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4492 uu____4493  in
          FStar_Pprint.group uu____4491
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()<-";
             FStar_Ident.idRange = uu____4500;_},e1::e2::e3::[])
          ->
          let uu____4506 =
            let uu____4507 =
              let uu____4508 =
                let uu____4509 = p_atomicTermNotQUident e1  in
                let uu____4510 =
                  let uu____4511 =
                    let uu____4512 =
                      let uu____4513 = p_term false e2  in
                      soft_parens_with_nesting uu____4513  in
                    let uu____4514 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____4512 uu____4514  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4511  in
                FStar_Pprint.op_Hat_Hat uu____4509 uu____4510  in
              FStar_Pprint.group uu____4508  in
            let uu____4515 =
              let uu____4516 = p_noSeqTerm ps e3  in jump2 uu____4516  in
            FStar_Pprint.op_Hat_Hat uu____4507 uu____4515  in
          FStar_Pprint.group uu____4506
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]<-";
             FStar_Ident.idRange = uu____4517;_},e1::e2::e3::[])
          ->
          let uu____4523 =
            let uu____4524 =
              let uu____4525 =
                let uu____4526 = p_atomicTermNotQUident e1  in
                let uu____4527 =
                  let uu____4528 =
                    let uu____4529 =
                      let uu____4530 = p_term false e2  in
                      soft_brackets_with_nesting uu____4530  in
                    let uu____4531 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                        FStar_Pprint.larrow
                       in
                    FStar_Pprint.op_Hat_Hat uu____4529 uu____4531  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4528  in
                FStar_Pprint.op_Hat_Hat uu____4526 uu____4527  in
              FStar_Pprint.group uu____4525  in
            let uu____4532 =
              let uu____4533 = p_noSeqTerm ps e3  in jump2 uu____4533  in
            FStar_Pprint.op_Hat_Hat uu____4524 uu____4532  in
          FStar_Pprint.group uu____4523
      | FStar_Parser_AST.Requires (e1,wtf) ->
          let uu____4543 =
            let uu____4544 = str "requires"  in
            let uu____4545 = p_typ ps e1  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4544 uu____4545  in
          FStar_Pprint.group uu____4543
      | FStar_Parser_AST.Ensures (e1,wtf) ->
          let uu____4555 =
            let uu____4556 = str "ensures"  in
            let uu____4557 = p_typ ps e1  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4556 uu____4557  in
          FStar_Pprint.group uu____4555
      | FStar_Parser_AST.Attributes es ->
          let uu____4561 =
            let uu____4562 = str "attributes"  in
            let uu____4563 = FStar_Pprint.separate_map break1 p_atomicTerm es
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4562 uu____4563  in
          FStar_Pprint.group uu____4561
      | FStar_Parser_AST.If (e1,e2,e3) ->
          if is_unit e3
          then
            let uu____4567 =
              let uu____4568 =
                let uu____4569 = str "if"  in
                let uu____4570 = p_noSeqTerm false e1  in
                op_Hat_Slash_Plus_Hat uu____4569 uu____4570  in
              let uu____4571 =
                let uu____4572 = str "then"  in
                let uu____4573 = p_noSeqTerm ps e2  in
                op_Hat_Slash_Plus_Hat uu____4572 uu____4573  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4568 uu____4571  in
            FStar_Pprint.group uu____4567
          else
            (let e2_doc =
               match e2.FStar_Parser_AST.tm with
               | FStar_Parser_AST.If (uu____4576,uu____4577,e31) when
                   is_unit e31 ->
                   let uu____4579 = p_noSeqTerm false e2  in
                   soft_parens_with_nesting uu____4579
               | uu____4580 -> p_noSeqTerm false e2  in
             let uu____4581 =
               let uu____4582 =
                 let uu____4583 = str "if"  in
                 let uu____4584 = p_noSeqTerm false e1  in
                 op_Hat_Slash_Plus_Hat uu____4583 uu____4584  in
               let uu____4585 =
                 let uu____4586 =
                   let uu____4587 = str "then"  in
                   op_Hat_Slash_Plus_Hat uu____4587 e2_doc  in
                 let uu____4588 =
                   let uu____4589 = str "else"  in
                   let uu____4590 = p_noSeqTerm ps e3  in
                   op_Hat_Slash_Plus_Hat uu____4589 uu____4590  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4586 uu____4588  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4582 uu____4585  in
             FStar_Pprint.group uu____4581)
      | FStar_Parser_AST.TryWith (e1,branches) ->
          let uu____4613 =
            let uu____4614 =
              let uu____4615 =
                let uu____4616 = str "try"  in
                let uu____4617 = p_noSeqTerm false e1  in
                prefix2 uu____4616 uu____4617  in
              let uu____4618 =
                let uu____4619 = str "with"  in
                let uu____4620 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    p_patternBranch branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4619 uu____4620  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4615 uu____4618  in
            FStar_Pprint.group uu____4614  in
          let uu____4629 = paren_if ps  in uu____4629 uu____4613
      | FStar_Parser_AST.Match (e1,branches) ->
          let uu____4654 =
            let uu____4655 =
              let uu____4656 =
                let uu____4657 = str "match"  in
                let uu____4658 = p_noSeqTerm false e1  in
                let uu____4659 = str "with"  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4657 uu____4658 uu____4659
                 in
              let uu____4660 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  p_patternBranch branches
                 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4656 uu____4660  in
            FStar_Pprint.group uu____4655  in
          let uu____4669 = paren_if ps  in uu____4669 uu____4654
      | FStar_Parser_AST.LetOpen (uid,e1) ->
          let uu____4674 =
            let uu____4675 =
              let uu____4676 =
                let uu____4677 = str "let open"  in
                let uu____4678 = p_quident uid  in
                let uu____4679 = str "in"  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4677 uu____4678 uu____4679
                 in
              let uu____4680 = p_term false e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4676 uu____4680  in
            FStar_Pprint.group uu____4675  in
          let uu____4681 = paren_if ps  in uu____4681 uu____4674
      | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
          let let_first =
            let uu____4746 = p_attrs_opt a0  in
            let uu____4747 =
              let uu____4748 =
                let uu____4749 = str "let"  in
                let uu____4750 =
                  let uu____4751 = p_letqualifier q  in
                  let uu____4752 = p_letbinding lb0  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4751 uu____4752  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4749 uu____4750  in
              FStar_Pprint.group uu____4748  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4746 uu____4747  in
          let let_rest =
            match attr_letbindings with
            | [] -> FStar_Pprint.empty
            | uu____4766 ->
                let uu____4781 =
                  precede_break_separate_map FStar_Pprint.empty
                    FStar_Pprint.empty p_attr_letbinding attr_letbindings
                   in
                FStar_Pprint.group uu____4781
             in
          let uu____4794 =
            let uu____4795 =
              let uu____4796 =
                let uu____4797 = str "in"  in
                let uu____4798 = p_term false e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4797 uu____4798  in
              FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4796  in
            FStar_Pprint.op_Hat_Slash_Hat let_first uu____4795  in
          let uu____4799 = paren_if ps  in uu____4799 uu____4794
      | FStar_Parser_AST.Abs
          ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
             FStar_Parser_AST.prange = uu____4804;_}::[],{
                                                           FStar_Parser_AST.tm
                                                             =
                                                             FStar_Parser_AST.Match
                                                             (maybe_x,branches);
                                                           FStar_Parser_AST.range
                                                             = uu____4807;
                                                           FStar_Parser_AST.level
                                                             = uu____4808;_})
          when matches_var maybe_x x ->
          let uu____4835 =
            let uu____4836 =
              let uu____4837 = str "function"  in
              let uu____4838 =
                FStar_Pprint.separate_map FStar_Pprint.hardline
                  p_patternBranch branches
                 in
              FStar_Pprint.op_Hat_Slash_Hat uu____4837 uu____4838  in
            FStar_Pprint.group uu____4836  in
          let uu____4847 = paren_if ps  in uu____4847 uu____4835
      | uu____4850 -> p_typ ps e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_4851  ->
    match uu___60_4851 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4863 =
          let uu____4864 = str "[@"  in
          let uu____4865 =
            let uu____4866 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____4867 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4866 uu____4867  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4864 uu____4865  in
        FStar_Pprint.group uu____4863

and (p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4868  ->
    match uu____4868 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4897 =
          let uu____4898 = p_attrs_opt a  in
          let uu____4899 =
            let uu____4900 =
              let uu____4901 = str "and "  in
              let uu____4902 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4901 uu____4902  in
            FStar_Pprint.group uu____4900  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4898 uu____4899  in
        let uu____4903 = p_term false e  in prefix2 uu____4897 uu____4903

and (p_typ : Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  -> fun e  -> with_comment (p_typ' ps) e e.FStar_Parser_AST.range

and (p_typ' : Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.QForall (bs,trigger,e1) ->
          let uu____4923 =
            let uu____4924 =
              let uu____4925 = p_quantifier e  in
              FStar_Pprint.op_Hat_Hat uu____4925 FStar_Pprint.space  in
            let uu____4926 = p_binders true bs  in
            FStar_Pprint.soft_surround (Prims.parse_int "2")
              (Prims.parse_int "0") uu____4924 uu____4926 FStar_Pprint.dot
             in
          let uu____4927 =
            let uu____4928 = p_trigger trigger  in
            let uu____4929 = p_noSeqTerm ps e1  in
            FStar_Pprint.op_Hat_Hat uu____4928 uu____4929  in
          prefix2 uu____4923 uu____4927
      | FStar_Parser_AST.QExists (bs,trigger,e1) ->
          let uu____4945 =
            let uu____4946 =
              let uu____4947 = p_quantifier e  in
              FStar_Pprint.op_Hat_Hat uu____4947 FStar_Pprint.space  in
            let uu____4948 = p_binders true bs  in
            FStar_Pprint.soft_surround (Prims.parse_int "2")
              (Prims.parse_int "0") uu____4946 uu____4948 FStar_Pprint.dot
             in
          let uu____4949 =
            let uu____4950 = p_trigger trigger  in
            let uu____4951 = p_noSeqTerm ps e1  in
            FStar_Pprint.op_Hat_Hat uu____4950 uu____4951  in
          prefix2 uu____4945 uu____4949
      | uu____4952 -> p_simpleTerm ps e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____4954 -> str "forall"
    | FStar_Parser_AST.QExists uu____4967 -> str "exists"
    | uu____4980 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_4981  ->
    match uu___61_4981 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4993 =
          let uu____4994 =
            let uu____4995 = str "pattern"  in
            let uu____4996 =
              let uu____4997 =
                let uu____4998 = p_disjunctivePats pats  in jump2 uu____4998
                 in
              let uu____4999 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4997 uu____4999  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4995 uu____4996  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4994  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4993

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5005 = str "\\/"  in
    FStar_Pprint.separate_map uu____5005 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5011 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5011

and (p_simpleTerm :
  Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun ps  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Abs (pats,e1) ->
          let uu____5020 =
            let uu____5021 =
              let uu____5022 = str "fun"  in
              let uu____5023 =
                let uu____5024 =
                  FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5024 FStar_Pprint.rarrow
                 in
              op_Hat_Slash_Plus_Hat uu____5022 uu____5023  in
            let uu____5025 = p_term false e1  in
            op_Hat_Slash_Plus_Hat uu____5021 uu____5025  in
          let uu____5026 = paren_if ps  in uu____5026 uu____5020
      | uu____5029 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun uu____5032  ->
    match uu____5032 with
    | (pat,when_opt,e) ->
        let uu____5048 =
          let uu____5049 =
            let uu____5050 =
              let uu____5051 =
                let uu____5052 =
                  let uu____5053 = p_disjunctivePattern pat  in
                  let uu____5054 =
                    let uu____5055 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____5055 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____5053 uu____5054  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5052  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5051  in
            FStar_Pprint.group uu____5050  in
          let uu____5056 = p_term false e  in
          op_Hat_Slash_Plus_Hat uu____5049 uu____5056  in
        FStar_Pprint.group uu____5048

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_5057  ->
    match uu___62_5057 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5061 = str "when"  in
        let uu____5062 =
          let uu____5063 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5063 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5061 uu____5062

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5065;_},e1::e2::[])
        ->
        let uu____5070 = str "<==>"  in
        let uu____5071 = p_tmImplies e1  in
        let uu____5072 = p_tmIff e2  in
        infix0 uu____5070 uu____5071 uu____5072
    | uu____5073 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5075;_},e1::e2::[])
        ->
        let uu____5080 = str "==>"  in
        let uu____5081 = p_tmArrow p_tmFormula e1  in
        let uu____5082 = p_tmImplies e2  in
        infix0 uu____5080 uu____5081 uu____5082
    | uu____5083 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5094 =
            let uu____5095 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5100 = p_binder false b  in
                   let uu____5101 =
                     let uu____5102 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5102
                      in
                   FStar_Pprint.op_Hat_Hat uu____5100 uu____5101) bs
               in
            let uu____5103 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5095 uu____5103  in
          FStar_Pprint.group uu____5094
      | uu____5104 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5106;_},e1::e2::[])
        ->
        let uu____5111 = str "\\/"  in
        let uu____5112 = p_tmFormula e1  in
        let uu____5113 = p_tmConjunction e2  in
        infix0 uu____5111 uu____5112 uu____5113
    | uu____5114 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5116;_},e1::e2::[])
        ->
        let uu____5121 = str "/\\"  in
        let uu____5122 = p_tmConjunction e1  in
        let uu____5123 = p_tmTuple e2  in
        infix0 uu____5121 uu____5122 uu____5123
    | uu____5124 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5141 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5141
          (fun uu____5149  ->
             match uu____5149 with | (e1,uu____5155) -> p_tmEq e1) args
    | uu____5156 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5161 =
             let uu____5162 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5162  in
           FStar_Pprint.group uu____5161)

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
          let uu____5219 = levels op1  in
          (match uu____5219 with
           | (left1,mine,right1) ->
               let uu____5229 =
                 let uu____5230 = FStar_All.pipe_left str op1  in
                 let uu____5231 = p_tmEq' left1 e1  in
                 let uu____5232 = p_tmEq' right1 e2  in
                 infix0 uu____5230 uu____5231 uu____5232  in
               paren_if_gt curr mine uu____5229)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5233;_},e1::e2::[])
          ->
          let uu____5238 =
            let uu____5239 = p_tmEq e1  in
            let uu____5240 =
              let uu____5241 =
                let uu____5242 =
                  let uu____5243 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5243  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5242  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5241  in
            FStar_Pprint.op_Hat_Hat uu____5239 uu____5240  in
          FStar_Pprint.group uu____5238
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5244;_},e1::[])
          ->
          let uu____5248 = levels "-"  in
          (match uu____5248 with
           | (left1,mine,right1) ->
               let uu____5258 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5258)
      | uu____5259 -> p_tmNoEq e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and (p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun curr  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5324)::(e2,uu____5326)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5346 = is_list e  in Prims.op_Negation uu____5346)
          ->
          let op = "::"  in
          let uu____5348 = levels op  in
          (match uu____5348 with
           | (left1,mine,right1) ->
               let uu____5358 =
                 let uu____5359 = str op  in
                 let uu____5360 = p_tmNoEq' left1 e1  in
                 let uu____5361 = p_tmNoEq' right1 e2  in
                 infix0 uu____5359 uu____5360 uu____5361  in
               paren_if_gt curr mine uu____5358)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5369 = levels op  in
          (match uu____5369 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5383 = p_binder false b  in
                 let uu____5384 =
                   let uu____5385 =
                     let uu____5386 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5386 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5385  in
                 FStar_Pprint.op_Hat_Hat uu____5383 uu____5384  in
               let uu____5387 =
                 let uu____5388 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5389 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5388 uu____5389  in
               paren_if_gt curr mine uu____5387)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5396 = levels op1  in
          (match uu____5396 with
           | (left1,mine,right1) ->
               let uu____5406 =
                 let uu____5407 = str op1  in
                 let uu____5408 = p_tmNoEq' left1 e1  in
                 let uu____5409 = p_tmNoEq' right1 e2  in
                 infix0 uu____5407 uu____5408 uu____5409  in
               paren_if_gt curr mine uu____5406)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5412 =
            let uu____5413 = p_lidentOrUnderscore lid  in
            let uu____5414 =
              let uu____5415 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5415  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5413 uu____5414  in
          FStar_Pprint.group uu____5412
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5436 =
            let uu____5437 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5438 =
              let uu____5439 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              separate_map_last uu____5439 p_simpleDef record_fields  in
            FStar_Pprint.op_Hat_Hat uu____5437 uu____5438  in
          braces_with_nesting uu____5436
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5444;_},e1::[])
          ->
          let uu____5448 =
            let uu____5449 = str "~"  in
            let uu____5450 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5449 uu____5450  in
          FStar_Pprint.group uu____5448
      | uu____5451 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5453 = p_appTerm e  in
    let uu____5454 =
      let uu____5455 =
        let uu____5456 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5456 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5455  in
    FStar_Pprint.op_Hat_Hat uu____5453 uu____5454

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5461 =
            let uu____5462 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5462 t phi  in
          soft_parens_with_nesting uu____5461
      | FStar_Parser_AST.TAnnotated uu____5463 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5468 ->
          let uu____5469 =
            let uu____5470 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5470
             in
          failwith uu____5469
      | FStar_Parser_AST.TVariable uu____5471 ->
          let uu____5472 =
            let uu____5473 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5473
             in
          failwith uu____5472
      | FStar_Parser_AST.NoName uu____5474 ->
          let uu____5475 =
            let uu____5476 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5476
             in
          failwith uu____5475

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5478  ->
      match uu____5478 with
      | (lid,e) ->
          let uu____5485 =
            let uu____5486 = p_qlident lid  in
            let uu____5487 =
              let uu____5488 = p_noSeqTerm ps e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5488
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5486 uu____5487  in
          FStar_Pprint.group uu____5485

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5490 when is_general_application e ->
        let uu____5497 = head_and_args e  in
        (match uu____5497 with
         | (head1,args) ->
             let uu____5522 =
               let uu____5533 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5533
               then
                 let uu____5563 =
                   FStar_Util.take
                     (fun uu____5587  ->
                        match uu____5587 with
                        | (uu____5592,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5563 with
                 | (fs_typ_args,args1) ->
                     let uu____5630 =
                       let uu____5631 = p_indexingTerm head1  in
                       let uu____5632 =
                         let uu____5633 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5633 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5631 uu____5632  in
                     (uu____5630, args1)
               else
                 (let uu____5645 = p_indexingTerm head1  in
                  (uu____5645, args))
                in
             (match uu____5522 with
              | (head_doc,args1) ->
                  let uu____5666 =
                    let uu____5667 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5667 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5666))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5687 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5687)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5705 =
               let uu____5706 = p_quident lid  in
               let uu____5707 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5706 uu____5707  in
             FStar_Pprint.group uu____5705
         | hd1::tl1 ->
             let uu____5724 =
               let uu____5725 =
                 let uu____5726 =
                   let uu____5727 = p_quident lid  in
                   let uu____5728 = p_argTerm hd1  in
                   prefix2 uu____5727 uu____5728  in
                 FStar_Pprint.group uu____5726  in
               let uu____5729 =
                 let uu____5730 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5730  in
               FStar_Pprint.op_Hat_Hat uu____5725 uu____5729  in
             FStar_Pprint.group uu____5724)
    | uu____5735 -> p_indexingTerm e

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
         (let uu____5744 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5744 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5746 = str "#"  in
        let uu____5747 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5746 uu____5747
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5749  ->
    match uu____5749 with | (e,uu____5755) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5760;_},e1::e2::[])
          ->
          let uu____5765 =
            let uu____5766 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5767 =
              let uu____5768 =
                let uu____5769 = p_term false e2  in
                soft_parens_with_nesting uu____5769  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5768  in
            FStar_Pprint.op_Hat_Hat uu____5766 uu____5767  in
          FStar_Pprint.group uu____5765
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5770;_},e1::e2::[])
          ->
          let uu____5775 =
            let uu____5776 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5777 =
              let uu____5778 =
                let uu____5779 = p_term false e2  in
                soft_brackets_with_nesting uu____5779  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5778  in
            FStar_Pprint.op_Hat_Hat uu____5776 uu____5777  in
          FStar_Pprint.group uu____5775
      | uu____5780 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5785 = p_quident lid  in
        let uu____5786 =
          let uu____5787 =
            let uu____5788 = p_term false e1  in
            soft_parens_with_nesting uu____5788  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5787  in
        FStar_Pprint.op_Hat_Hat uu____5785 uu____5786
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5794 = str (FStar_Ident.text_of_id op)  in
        let uu____5795 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5794 uu____5795
    | uu____5796 -> p_atomicTermNotQUident e

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
         | uu____5803 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5810 = str (FStar_Ident.text_of_id op)  in
        let uu____5811 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5810 uu____5811
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5815 =
          let uu____5816 =
            let uu____5817 = str (FStar_Ident.text_of_id op)  in
            let uu____5818 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5817 uu____5818  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5816  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5815
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5833 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5834 =
          let uu____5835 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5836 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5835 p_tmEq uu____5836  in
        let uu____5843 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5833 uu____5834 uu____5843
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5846 =
          let uu____5847 = p_atomicTermNotQUident e1  in
          let uu____5848 =
            let uu____5849 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5849  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5847 uu____5848
           in
        FStar_Pprint.group uu____5846
    | uu____5850 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5855 = p_quident constr_lid  in
        let uu____5856 =
          let uu____5857 =
            let uu____5858 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5858  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5857  in
        FStar_Pprint.op_Hat_Hat uu____5855 uu____5856
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5860 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5860 FStar_Pprint.qmark
    | uu____5861 when is_array e ->
        let es = extract_from_list e  in
        let uu____5865 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5866 =
          let uu____5867 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____5867 p_noSeqTerm es  in
        let uu____5868 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5865 uu____5866 uu____5868
    | uu____5869 when is_list e ->
        let uu____5870 =
          let uu____5871 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5872 = extract_from_list e  in
          separate_map_or_flow_last uu____5871 p_noSeqTerm uu____5872  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5870 FStar_Pprint.rbracket
    | uu____5875 when is_lex_list e ->
        let uu____5876 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5877 =
          let uu____5878 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5879 = extract_from_list e  in
          separate_map_or_flow_last uu____5878 p_noSeqTerm uu____5879  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5876 uu____5877 FStar_Pprint.rbracket
    | uu____5882 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5886 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5887 =
          let uu____5888 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5888 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5886 uu____5887 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5892 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5893 = p_term false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5892 uu____5893
    | FStar_Parser_AST.Op (op,args) when
        let uu____5900 = handleable_op op args  in
        Prims.op_Negation uu____5900 ->
        let uu____5901 =
          let uu____5902 =
            let uu____5903 =
              let uu____5904 =
                let uu____5905 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5905
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5904  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5903  in
          Prims.strcat "Operation " uu____5902  in
        failwith uu____5901
    | FStar_Parser_AST.Uvar uu____5906 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5907 = p_term false e  in
        soft_parens_with_nesting uu____5907
    | FStar_Parser_AST.Const uu____5908 ->
        let uu____5909 = p_term false e  in
        soft_parens_with_nesting uu____5909
    | FStar_Parser_AST.Op uu____5910 ->
        let uu____5917 = p_term false e  in
        soft_parens_with_nesting uu____5917
    | FStar_Parser_AST.Tvar uu____5918 ->
        let uu____5919 = p_term false e  in
        soft_parens_with_nesting uu____5919
    | FStar_Parser_AST.Var uu____5920 ->
        let uu____5921 = p_term false e  in
        soft_parens_with_nesting uu____5921
    | FStar_Parser_AST.Name uu____5922 ->
        let uu____5923 = p_term false e  in
        soft_parens_with_nesting uu____5923
    | FStar_Parser_AST.Construct uu____5924 ->
        let uu____5935 = p_term false e  in
        soft_parens_with_nesting uu____5935
    | FStar_Parser_AST.Abs uu____5936 ->
        let uu____5943 = p_term false e  in
        soft_parens_with_nesting uu____5943
    | FStar_Parser_AST.App uu____5944 ->
        let uu____5951 = p_term false e  in
        soft_parens_with_nesting uu____5951
    | FStar_Parser_AST.Let uu____5952 ->
        let uu____5973 = p_term false e  in
        soft_parens_with_nesting uu____5973
    | FStar_Parser_AST.LetOpen uu____5974 ->
        let uu____5979 = p_term false e  in
        soft_parens_with_nesting uu____5979
    | FStar_Parser_AST.Seq uu____5980 ->
        let uu____5985 = p_term false e  in
        soft_parens_with_nesting uu____5985
    | FStar_Parser_AST.Bind uu____5986 ->
        let uu____5993 = p_term false e  in
        soft_parens_with_nesting uu____5993
    | FStar_Parser_AST.If uu____5994 ->
        let uu____6001 = p_term false e  in
        soft_parens_with_nesting uu____6001
    | FStar_Parser_AST.Match uu____6002 ->
        let uu____6017 = p_term false e  in
        soft_parens_with_nesting uu____6017
    | FStar_Parser_AST.TryWith uu____6018 ->
        let uu____6033 = p_term false e  in
        soft_parens_with_nesting uu____6033
    | FStar_Parser_AST.Ascribed uu____6034 ->
        let uu____6043 = p_term false e  in
        soft_parens_with_nesting uu____6043
    | FStar_Parser_AST.Record uu____6044 ->
        let uu____6057 = p_term false e  in
        soft_parens_with_nesting uu____6057
    | FStar_Parser_AST.Project uu____6058 ->
        let uu____6063 = p_term false e  in
        soft_parens_with_nesting uu____6063
    | FStar_Parser_AST.Product uu____6064 ->
        let uu____6071 = p_term false e  in
        soft_parens_with_nesting uu____6071
    | FStar_Parser_AST.Sum uu____6072 ->
        let uu____6079 = p_term false e  in
        soft_parens_with_nesting uu____6079
    | FStar_Parser_AST.QForall uu____6080 ->
        let uu____6093 = p_term false e  in
        soft_parens_with_nesting uu____6093
    | FStar_Parser_AST.QExists uu____6094 ->
        let uu____6107 = p_term false e  in
        soft_parens_with_nesting uu____6107
    | FStar_Parser_AST.Refine uu____6108 ->
        let uu____6113 = p_term false e  in
        soft_parens_with_nesting uu____6113
    | FStar_Parser_AST.NamedTyp uu____6114 ->
        let uu____6119 = p_term false e  in
        soft_parens_with_nesting uu____6119
    | FStar_Parser_AST.Requires uu____6120 ->
        let uu____6127 = p_term false e  in
        soft_parens_with_nesting uu____6127
    | FStar_Parser_AST.Ensures uu____6128 ->
        let uu____6135 = p_term false e  in
        soft_parens_with_nesting uu____6135
    | FStar_Parser_AST.Attributes uu____6136 ->
        let uu____6139 = p_term false e  in
        soft_parens_with_nesting uu____6139

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_6140  ->
    match uu___65_6140 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6144 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6144
    | FStar_Const.Const_string (s,uu____6146) ->
        let uu____6147 = str s  in FStar_Pprint.dquotes uu____6147
    | FStar_Const.Const_bytearray (bytes,uu____6149) ->
        let uu____6154 =
          let uu____6155 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6155  in
        let uu____6156 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6154 uu____6156
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6174 =
          match uu___63_6174 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6178 =
          match uu___64_6178 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6189  ->
               match uu____6189 with
               | (s,w) ->
                   let uu____6196 = signedness s  in
                   let uu____6197 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6196 uu____6197)
            sign_width_opt
           in
        let uu____6198 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6198 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6200 = FStar_Range.string_of_range r  in str uu____6200
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6202 = p_quident lid  in
        let uu____6203 =
          let uu____6204 =
            let uu____6205 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6205  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6204  in
        FStar_Pprint.op_Hat_Hat uu____6202 uu____6203

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6207 = str "u#"  in
    let uu____6208 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6207 uu____6208

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6210;_},u1::u2::[])
        ->
        let uu____6215 =
          let uu____6216 = p_universeFrom u1  in
          let uu____6217 =
            let uu____6218 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6218  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6216 uu____6217  in
        FStar_Pprint.group uu____6215
    | FStar_Parser_AST.App uu____6219 ->
        let uu____6226 = head_and_args u  in
        (match uu____6226 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6252 =
                    let uu____6253 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6254 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6262  ->
                           match uu____6262 with
                           | (u1,uu____6268) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6253 uu____6254  in
                  FStar_Pprint.group uu____6252
              | uu____6269 ->
                  let uu____6270 =
                    let uu____6271 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6271
                     in
                  failwith uu____6270))
    | uu____6272 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6295;_},uu____6296::uu____6297::[])
        ->
        let uu____6300 = p_universeFrom u  in
        soft_parens_with_nesting uu____6300
    | FStar_Parser_AST.App uu____6301 ->
        let uu____6308 = p_universeFrom u  in
        soft_parens_with_nesting uu____6308
    | uu____6309 ->
        let uu____6310 =
          let uu____6311 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6311
           in
        failwith uu____6310

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_term false e 
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
       | FStar_Parser_AST.Module (uu____6351,decls) ->
           let uu____6357 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6357
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6366,decls,uu____6368) ->
           let uu____6373 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6373
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6424  ->
         match uu____6424 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6464,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6470,decls,uu____6472) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6517 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6530;
                 FStar_Parser_AST.doc = uu____6531;
                 FStar_Parser_AST.quals = uu____6532;
                 FStar_Parser_AST.attrs = uu____6533;_}::uu____6534 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6540 =
                   let uu____6543 =
                     let uu____6546 = FStar_List.tl ds  in d :: uu____6546
                      in
                   d0 :: uu____6543  in
                 (uu____6540, (d0.FStar_Parser_AST.drange))
             | uu____6551 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6517 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6609 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6609 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6705 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6705, comments1))))))
  