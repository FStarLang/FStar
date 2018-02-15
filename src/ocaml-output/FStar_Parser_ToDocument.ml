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
    let uu____3287 =
      let uu____3288 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3289 =
        let uu____3290 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3291 =
          let uu____3292 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3293 =
            let uu____3294 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3294
             in
          FStar_Pprint.op_Hat_Hat uu____3292 uu____3293  in
        FStar_Pprint.op_Hat_Hat uu____3290 uu____3291  in
      FStar_Pprint.op_Hat_Hat uu____3288 uu____3289  in
    FStar_Pprint.group uu____3287

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3297 =
      let uu____3298 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3298  in
    let uu____3299 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3297 FStar_Pprint.space uu____3299
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3300  ->
    match uu____3300 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3334 =
                match uu____3334 with
                | (kwd,arg) ->
                    let uu____3341 = str "@"  in
                    let uu____3342 =
                      let uu____3343 = str kwd  in
                      let uu____3344 =
                        let uu____3345 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3345
                         in
                      FStar_Pprint.op_Hat_Hat uu____3343 uu____3344  in
                    FStar_Pprint.op_Hat_Hat uu____3341 uu____3342
                 in
              let uu____3346 =
                let uu____3347 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3347 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3346
           in
        let uu____3352 =
          let uu____3353 =
            let uu____3354 =
              let uu____3355 =
                let uu____3356 = str doc1  in
                let uu____3357 =
                  let uu____3358 =
                    let uu____3359 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3359  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3358  in
                FStar_Pprint.op_Hat_Hat uu____3356 uu____3357  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3355  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3354  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3353  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3352

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3363 =
          let uu____3364 = str "val"  in
          let uu____3365 =
            let uu____3366 =
              let uu____3367 = p_lident lid  in
              let uu____3368 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3367 uu____3368  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3366  in
          FStar_Pprint.op_Hat_Hat uu____3364 uu____3365  in
        let uu____3369 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3363 uu____3369
    | FStar_Parser_AST.TopLevelLet (uu____3370,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3395 =
               let uu____3396 = str "let"  in
               let uu____3397 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3396 uu____3397  in
             FStar_Pprint.group uu____3395) lbs
    | uu____3398 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3401 =
          let uu____3402 = str "open"  in
          let uu____3403 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3402 uu____3403  in
        FStar_Pprint.group uu____3401
    | FStar_Parser_AST.Include uid ->
        let uu____3405 =
          let uu____3406 = str "include"  in
          let uu____3407 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3406 uu____3407  in
        FStar_Pprint.group uu____3405
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3410 =
          let uu____3411 = str "module"  in
          let uu____3412 =
            let uu____3413 =
              let uu____3414 = p_uident uid1  in
              let uu____3415 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3414 uu____3415  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3413  in
          FStar_Pprint.op_Hat_Hat uu____3411 uu____3412  in
        let uu____3416 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3410 uu____3416
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3418 =
          let uu____3419 = str "module"  in
          let uu____3420 =
            let uu____3421 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3421  in
          FStar_Pprint.op_Hat_Hat uu____3419 uu____3420  in
        FStar_Pprint.group uu____3418
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3454 = str "effect"  in
          let uu____3455 =
            let uu____3456 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3456  in
          FStar_Pprint.op_Hat_Hat uu____3454 uu____3455  in
        let uu____3457 =
          let uu____3458 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3458 FStar_Pprint.equals
           in
        let uu____3459 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3457 uu____3459
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3477 = str "type"  in
        let uu____3478 = str "and"  in
        precede_break_separate_map uu____3477 uu____3478 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3500 = str "let"  in
          let uu____3501 =
            let uu____3502 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3502 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3500 uu____3501  in
        let uu____3503 =
          let uu____3504 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3504 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3503 p_letbinding lbs
          (fun uu____3512  ->
             match uu____3512 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3521 =
          let uu____3522 = str "val"  in
          let uu____3523 =
            let uu____3524 =
              let uu____3525 = p_lident lid  in
              let uu____3526 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3525 uu____3526  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3524  in
          FStar_Pprint.op_Hat_Hat uu____3522 uu____3523  in
        let uu____3527 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3521 uu____3527
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3531 =
            let uu____3532 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3532 FStar_Util.is_upper  in
          if uu____3531
          then FStar_Pprint.empty
          else
            (let uu____3534 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3534 FStar_Pprint.space)
           in
        let uu____3535 =
          let uu____3536 =
            let uu____3537 = p_ident id1  in
            let uu____3538 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3537 uu____3538  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3536  in
        let uu____3539 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3535 uu____3539
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3546 = str "exception"  in
        let uu____3547 =
          let uu____3548 =
            let uu____3549 = p_uident uid  in
            let uu____3550 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3554 =
                     let uu____3555 = str "of"  in
                     let uu____3556 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3555 uu____3556  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3554) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3549 uu____3550  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3548  in
        FStar_Pprint.op_Hat_Hat uu____3546 uu____3547
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3558 = str "new_effect"  in
        let uu____3559 =
          let uu____3560 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3560  in
        FStar_Pprint.op_Hat_Hat uu____3558 uu____3559
    | FStar_Parser_AST.SubEffect se ->
        let uu____3562 = str "sub_effect"  in
        let uu____3563 =
          let uu____3564 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3564  in
        FStar_Pprint.op_Hat_Hat uu____3562 uu____3563
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3567 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3567 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3568 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3569) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3586  ->
    match uu___54_3586 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3588 = str "#set-options"  in
        let uu____3589 =
          let uu____3590 =
            let uu____3591 = str s  in FStar_Pprint.dquotes uu____3591  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3590  in
        FStar_Pprint.op_Hat_Hat uu____3588 uu____3589
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3595 = str "#reset-options"  in
        let uu____3596 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3600 =
                 let uu____3601 = str s  in FStar_Pprint.dquotes uu____3601
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3600) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3595 uu____3596
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
  fun uu____3625  ->
    match uu____3625 with
    | (typedecl,fsdoc_opt) ->
        let uu____3638 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3639 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3638 uu____3639

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3640  ->
    match uu___55_3640 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3655 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3671 =
          let uu____3672 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3672  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3719 =
          match uu____3719 with
          | (lid1,t,doc_opt) ->
              let uu____3735 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3735
           in
        let p_fields uu____3749 =
          let uu____3750 =
            let uu____3751 =
              let uu____3752 =
                let uu____3753 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3753 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3752  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3751  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3750  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3817 =
          match uu____3817 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3843 =
                  let uu____3844 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3844  in
                FStar_Range.extend_to_end_of_line uu____3843  in
              let p_constructorBranch decl =
                let uu____3877 =
                  let uu____3878 =
                    let uu____3879 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3879  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3878  in
                FStar_Pprint.group uu____3877  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3899 =
          let uu____3900 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3900  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3915  ->
             let uu____3916 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3916)

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
            let uu____3931 = p_ident lid  in
            let uu____3932 =
              let uu____3933 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3933  in
            FStar_Pprint.op_Hat_Hat uu____3931 uu____3932
          else
            (let binders_doc =
               let uu____3936 = p_typars bs  in
               let uu____3937 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3941 =
                        let uu____3942 =
                          let uu____3943 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3943
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3942
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3941) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3936 uu____3937  in
             let uu____3944 = p_ident lid  in
             let uu____3945 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3944 binders_doc uu____3945)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____3947  ->
      match uu____3947 with
      | (lid,t,doc_opt) ->
          let uu____3963 =
            let uu____3964 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____3965 =
              let uu____3966 = p_lident lid  in
              let uu____3967 =
                let uu____3968 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3968  in
              FStar_Pprint.op_Hat_Hat uu____3966 uu____3967  in
            FStar_Pprint.op_Hat_Hat uu____3964 uu____3965  in
          FStar_Pprint.group uu____3963

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____3969  ->
    match uu____3969 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3997 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3998 =
          let uu____3999 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4000 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4005 =
                   let uu____4006 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4006  in
                 let uu____4007 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4005 uu____4007) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3999 uu____4000  in
        FStar_Pprint.op_Hat_Hat uu____3997 uu____3998

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4008  ->
    match uu____4008 with
    | (pat,uu____4014) ->
        let uu____4015 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4026 =
                let uu____4027 =
                  let uu____4028 =
                    let uu____4029 =
                      let uu____4030 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4030
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4029  in
                  FStar_Pprint.group uu____4028  in
                FStar_Pprint.op_Hat_Hat break1 uu____4027  in
              (pat1, uu____4026)
          | uu____4031 -> (pat, FStar_Pprint.empty)  in
        (match uu____4015 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4035);
                     FStar_Parser_AST.prange = uu____4036;_},pats)
                  ->
                  let uu____4046 =
                    let uu____4047 = p_lident x  in
                    let uu____4048 =
                      let uu____4049 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4049 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4047 uu____4048  in
                  FStar_Pprint.group uu____4046
              | uu____4050 ->
                  let uu____4051 =
                    let uu____4052 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4052 ascr_doc  in
                  FStar_Pprint.group uu____4051))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4053  ->
    match uu____4053 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4061 =
          let uu____4062 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4062  in
        let uu____4063 = p_term false false e  in
        prefix2 uu____4061 uu____4063

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_4064  ->
    match uu___56_4064 with
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
        let uu____4089 = p_uident uid  in
        let uu____4090 = p_binders true bs  in
        let uu____4091 =
          let uu____4092 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4092  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4089 uu____4090 uu____4091

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
          let uu____4101 =
            let uu____4102 =
              let uu____4103 =
                let uu____4104 = p_uident uid  in
                let uu____4105 = p_binders true bs  in
                let uu____4106 =
                  let uu____4107 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4107  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4104 uu____4105 uu____4106
                 in
              FStar_Pprint.group uu____4103  in
            let uu____4108 =
              let uu____4109 = str "with"  in
              let uu____4110 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4109 uu____4110  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4102 uu____4108  in
          braces_with_nesting uu____4101

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
          let uu____4141 =
            let uu____4142 = p_lident lid  in
            let uu____4143 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4142 uu____4143  in
          let uu____4144 = p_simpleTerm ps false e  in
          prefix2 uu____4141 uu____4144
      | uu____4145 ->
          let uu____4146 =
            let uu____4147 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4147
             in
          failwith uu____4146

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4205 =
        match uu____4205 with
        | (kwd,t) ->
            let uu____4212 =
              let uu____4213 = str kwd  in
              let uu____4214 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4213 uu____4214  in
            let uu____4215 = p_simpleTerm ps false t  in
            prefix2 uu____4212 uu____4215
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4220 =
      let uu____4221 =
        let uu____4222 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4223 =
          let uu____4224 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4224  in
        FStar_Pprint.op_Hat_Hat uu____4222 uu____4223  in
      let uu____4225 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4221 uu____4225  in
    let uu____4226 =
      let uu____4227 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4227  in
    FStar_Pprint.op_Hat_Hat uu____4220 uu____4226

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4228  ->
    match uu___57_4228 with
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
    let uu____4230 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4230

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4231  ->
    match uu___58_4231 with
    | FStar_Parser_AST.Rec  ->
        let uu____4232 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4232
    | FStar_Parser_AST.Mutable  ->
        let uu____4233 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4233
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4234  ->
    match uu___59_4234 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4239 =
          let uu____4240 =
            let uu____4241 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4241  in
          FStar_Pprint.separate_map uu____4240 p_tuplePattern pats  in
        FStar_Pprint.group uu____4239
    | uu____4242 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4249 =
          let uu____4250 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4250 p_constructorPattern pats  in
        FStar_Pprint.group uu____4249
    | uu____4251 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4254;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4259 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4260 = p_constructorPattern hd1  in
        let uu____4261 = p_constructorPattern tl1  in
        infix0 uu____4259 uu____4260 uu____4261
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4263;_},pats)
        ->
        let uu____4269 = p_quident uid  in
        let uu____4270 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4269 uu____4270
    | uu____4271 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4279;
               FStar_Parser_AST.blevel = uu____4280;
               FStar_Parser_AST.aqual = uu____4281;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4287 =
               let uu____4288 = p_ident lid  in
               p_refinement aqual uu____4288 t1 phi  in
             soft_parens_with_nesting uu____4287
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4290;
               FStar_Parser_AST.blevel = uu____4291;
               FStar_Parser_AST.aqual = uu____4292;_},phi))
             ->
             let uu____4294 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4294
         | uu____4295 ->
             let uu____4300 =
               let uu____4301 = p_tuplePattern pat  in
               let uu____4302 =
                 let uu____4303 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4304 =
                   let uu____4305 = p_typ false false t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4305  in
                 FStar_Pprint.op_Hat_Hat uu____4303 uu____4304  in
               FStar_Pprint.op_Hat_Hat uu____4301 uu____4302  in
             soft_parens_with_nesting uu____4300)
    | FStar_Parser_AST.PatList pats ->
        let uu____4309 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4309 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4324 =
          match uu____4324 with
          | (lid,pat) ->
              let uu____4331 = p_qlident lid  in
              let uu____4332 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4331 uu____4332
           in
        let uu____4333 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4333
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4343 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4344 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4345 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4343 uu____4344 uu____4345
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4356 =
          let uu____4357 =
            let uu____4358 = str (FStar_Ident.text_of_id op)  in
            let uu____4359 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4358 uu____4359  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4357  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4356
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4367 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4368 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4367 uu____4368
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4370 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4373;
           FStar_Parser_AST.prange = uu____4374;_},uu____4375)
        ->
        let uu____4380 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4380
    | FStar_Parser_AST.PatTuple (uu____4381,false ) ->
        let uu____4386 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4386
    | uu____4387 ->
        let uu____4388 =
          let uu____4389 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4389  in
        failwith uu____4388

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4393 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4394 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4393 uu____4394
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4401;
                   FStar_Parser_AST.blevel = uu____4402;
                   FStar_Parser_AST.aqual = uu____4403;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4405 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4405 t1 phi
            | uu____4406 ->
                let uu____4407 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4408 =
                  let uu____4409 = p_lident lid  in
                  let uu____4410 =
                    let uu____4411 =
                      let uu____4412 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4413 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4412 uu____4413  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4411  in
                  FStar_Pprint.op_Hat_Hat uu____4409 uu____4410  in
                FStar_Pprint.op_Hat_Hat uu____4407 uu____4408
             in
          if is_atomic
          then
            let uu____4414 =
              let uu____4415 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4415  in
            FStar_Pprint.group uu____4414
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4417 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4424;
                  FStar_Parser_AST.blevel = uu____4425;
                  FStar_Parser_AST.aqual = uu____4426;_},phi)
               ->
               if is_atomic
               then
                 let uu____4428 =
                   let uu____4429 =
                     let uu____4430 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4430 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4429  in
                 FStar_Pprint.group uu____4428
               else
                 (let uu____4432 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4432)
           | uu____4433 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4441 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4442 =
            let uu____4443 =
              let uu____4444 =
                let uu____4445 = p_appTerm t  in
                let uu____4446 =
                  let uu____4447 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4447  in
                FStar_Pprint.op_Hat_Hat uu____4445 uu____4446  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4444  in
            FStar_Pprint.op_Hat_Hat binder uu____4443  in
          FStar_Pprint.op_Hat_Hat uu____4441 uu____4442

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
            let uu____4470 =
              let uu____4471 =
                let uu____4472 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4472 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4471  in
            let uu____4473 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4470 uu____4473
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4477 =
              let uu____4478 =
                let uu____4479 =
                  let uu____4480 = p_lident x  in
                  let uu____4481 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4480 uu____4481  in
                let uu____4482 =
                  let uu____4483 = p_noSeqTerm true false e1  in
                  let uu____4484 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4483 uu____4484  in
                op_Hat_Slash_Plus_Hat uu____4479 uu____4482  in
              FStar_Pprint.group uu____4478  in
            let uu____4485 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4477 uu____4485
        | uu____4486 ->
            let uu____4487 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4487

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
            let uu____4498 =
              let uu____4499 = p_tmIff e1  in
              let uu____4500 =
                let uu____4501 =
                  let uu____4502 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4502
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4501  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4499 uu____4500  in
            FStar_Pprint.group uu____4498
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4508 =
              let uu____4509 = p_tmIff e1  in
              let uu____4510 =
                let uu____4511 =
                  let uu____4512 =
                    let uu____4513 = p_typ false false t  in
                    let uu____4514 =
                      let uu____4515 = str "by"  in
                      let uu____4516 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4515 uu____4516  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4513 uu____4514  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4512
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4511  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4509 uu____4510  in
            FStar_Pprint.group uu____4508
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4517;_},e1::e2::e3::[])
            ->
            let uu____4523 =
              let uu____4524 =
                let uu____4525 =
                  let uu____4526 = p_atomicTermNotQUident e1  in
                  let uu____4527 =
                    let uu____4528 =
                      let uu____4529 =
                        let uu____4530 = p_term false false e2  in
                        soft_parens_with_nesting uu____4530  in
                      let uu____4531 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4529 uu____4531  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4528  in
                  FStar_Pprint.op_Hat_Hat uu____4526 uu____4527  in
                FStar_Pprint.group uu____4525  in
              let uu____4532 =
                let uu____4533 = p_noSeqTerm ps pb e3  in jump2 uu____4533
                 in
              FStar_Pprint.op_Hat_Hat uu____4524 uu____4532  in
            FStar_Pprint.group uu____4523
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4534;_},e1::e2::e3::[])
            ->
            let uu____4540 =
              let uu____4541 =
                let uu____4542 =
                  let uu____4543 = p_atomicTermNotQUident e1  in
                  let uu____4544 =
                    let uu____4545 =
                      let uu____4546 =
                        let uu____4547 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4547  in
                      let uu____4548 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4546 uu____4548  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4545  in
                  FStar_Pprint.op_Hat_Hat uu____4543 uu____4544  in
                FStar_Pprint.group uu____4542  in
              let uu____4549 =
                let uu____4550 = p_noSeqTerm ps pb e3  in jump2 uu____4550
                 in
              FStar_Pprint.op_Hat_Hat uu____4541 uu____4549  in
            FStar_Pprint.group uu____4540
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4560 =
              let uu____4561 = str "requires"  in
              let uu____4562 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4561 uu____4562  in
            FStar_Pprint.group uu____4560
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4572 =
              let uu____4573 = str "ensures"  in
              let uu____4574 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4573 uu____4574  in
            FStar_Pprint.group uu____4572
        | FStar_Parser_AST.Attributes es ->
            let uu____4578 =
              let uu____4579 = str "attributes"  in
              let uu____4580 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4579 uu____4580  in
            FStar_Pprint.group uu____4578
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4584 =
                let uu____4585 =
                  let uu____4586 = str "if"  in
                  let uu____4587 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4586 uu____4587  in
                let uu____4588 =
                  let uu____4589 = str "then"  in
                  let uu____4590 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4589 uu____4590  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4585 uu____4588  in
              FStar_Pprint.group uu____4584
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4593,uu____4594,e31) when
                     is_unit e31 ->
                     let uu____4596 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4596
                 | uu____4597 -> p_noSeqTerm false false e2  in
               let uu____4598 =
                 let uu____4599 =
                   let uu____4600 = str "if"  in
                   let uu____4601 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4600 uu____4601  in
                 let uu____4602 =
                   let uu____4603 =
                     let uu____4604 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4604 e2_doc  in
                   let uu____4605 =
                     let uu____4606 = str "else"  in
                     let uu____4607 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4606 uu____4607  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4603 uu____4605  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4599 uu____4602  in
               FStar_Pprint.group uu____4598)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4630 =
              let uu____4631 =
                let uu____4632 =
                  let uu____4633 = str "try"  in
                  let uu____4634 = p_noSeqTerm false false e1  in
                  prefix2 uu____4633 uu____4634  in
                let uu____4635 =
                  let uu____4636 = str "with"  in
                  let uu____4637 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4636 uu____4637  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4632 uu____4635  in
              FStar_Pprint.group uu____4631  in
            let uu____4646 = paren_if (ps || pb)  in uu____4646 uu____4630
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4671 =
              let uu____4672 =
                let uu____4673 =
                  let uu____4674 = str "match"  in
                  let uu____4675 = p_noSeqTerm false false e1  in
                  let uu____4676 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4674 uu____4675 uu____4676
                   in
                let uu____4677 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4673 uu____4677  in
              FStar_Pprint.group uu____4672  in
            let uu____4686 = paren_if (ps || pb)  in uu____4686 uu____4671
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4691 =
              let uu____4692 =
                let uu____4693 =
                  let uu____4694 = str "let open"  in
                  let uu____4695 = p_quident uid  in
                  let uu____4696 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4694 uu____4695 uu____4696
                   in
                let uu____4697 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4693 uu____4697  in
              FStar_Pprint.group uu____4692  in
            let uu____4698 = paren_if ps  in uu____4698 uu____4691
        | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
            let let_first =
              let uu____4763 = p_attrs_opt a0  in
              let uu____4764 =
                let uu____4765 =
                  let uu____4766 = str "let"  in
                  let uu____4767 =
                    let uu____4768 = p_letqualifier q  in
                    let uu____4769 = p_letbinding lb0  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4768 uu____4769  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4766 uu____4767  in
                FStar_Pprint.group uu____4765  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4763 uu____4764  in
            let let_rest =
              match attr_letbindings with
              | [] -> FStar_Pprint.empty
              | uu____4783 ->
                  let uu____4798 =
                    precede_break_separate_map FStar_Pprint.empty
                      FStar_Pprint.empty p_attr_letbinding attr_letbindings
                     in
                  FStar_Pprint.group uu____4798
               in
            let uu____4811 =
              let uu____4812 =
                let uu____4813 =
                  let uu____4814 = str "in"  in
                  let uu____4815 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4814 uu____4815  in
                FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4813  in
              FStar_Pprint.op_Hat_Slash_Hat let_first uu____4812  in
            let uu____4816 = paren_if ps  in uu____4816 uu____4811
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4821;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____4824;
                                                             FStar_Parser_AST.level
                                                               = uu____4825;_})
            when matches_var maybe_x x ->
            let uu____4852 =
              let uu____4853 =
                let uu____4854 = str "function"  in
                let uu____4855 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4854 uu____4855  in
              FStar_Pprint.group uu____4853  in
            let uu____4864 = paren_if (ps || pb)  in uu____4864 uu____4852
        | uu____4867 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_4868  ->
    match uu___60_4868 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4880 =
          let uu____4881 = str "[@"  in
          let uu____4882 =
            let uu____4883 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____4884 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4883 uu____4884  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4881 uu____4882  in
        FStar_Pprint.group uu____4880

and (p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4885  ->
    match uu____4885 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4914 =
          let uu____4915 = p_attrs_opt a  in
          let uu____4916 =
            let uu____4917 =
              let uu____4918 = str "and "  in
              let uu____4919 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4918 uu____4919  in
            FStar_Pprint.group uu____4917  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4915 uu____4916  in
        let uu____4920 = p_term false false e  in
        prefix2 uu____4914 uu____4920

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
            let uu____4942 =
              let uu____4943 =
                let uu____4944 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____4944 FStar_Pprint.space  in
              let uu____4945 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____4943 uu____4945 FStar_Pprint.dot
               in
            let uu____4946 =
              let uu____4947 = p_trigger trigger  in
              let uu____4948 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4947 uu____4948  in
            prefix2 uu____4942 uu____4946
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____4964 =
              let uu____4965 =
                let uu____4966 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____4966 FStar_Pprint.space  in
              let uu____4967 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____4965 uu____4967 FStar_Pprint.dot
               in
            let uu____4968 =
              let uu____4969 = p_trigger trigger  in
              let uu____4970 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4969 uu____4970  in
            prefix2 uu____4964 uu____4968
        | uu____4971 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____4973 -> str "forall"
    | FStar_Parser_AST.QExists uu____4986 -> str "exists"
    | uu____4999 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_5000  ->
    match uu___61_5000 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5012 =
          let uu____5013 =
            let uu____5014 = str "pattern"  in
            let uu____5015 =
              let uu____5016 =
                let uu____5017 = p_disjunctivePats pats  in jump2 uu____5017
                 in
              let uu____5018 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5016 uu____5018  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5014 uu____5015  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5013  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5012

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5024 = str "\\/"  in
    FStar_Pprint.separate_map uu____5024 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5030 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5030

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5040 =
              let uu____5041 =
                let uu____5042 = str "fun"  in
                let uu____5043 =
                  let uu____5044 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5044
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5042 uu____5043  in
              let uu____5045 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5041 uu____5045  in
            let uu____5046 = paren_if ps  in uu____5046 uu____5040
        | uu____5049 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5053  ->
      match uu____5053 with
      | (pat,when_opt,e) ->
          let uu____5069 =
            let uu____5070 =
              let uu____5071 =
                let uu____5072 =
                  let uu____5073 =
                    let uu____5074 = p_disjunctivePattern pat  in
                    let uu____5075 =
                      let uu____5076 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5076 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5074 uu____5075  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5073  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5072  in
              FStar_Pprint.group uu____5071  in
            let uu____5077 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5070 uu____5077  in
          FStar_Pprint.group uu____5069

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_5078  ->
    match uu___62_5078 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5082 = str "when"  in
        let uu____5083 =
          let uu____5084 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5084 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5082 uu____5083

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5086;_},e1::e2::[])
        ->
        let uu____5091 = str "<==>"  in
        let uu____5092 = p_tmImplies e1  in
        let uu____5093 = p_tmIff e2  in
        infix0 uu____5091 uu____5092 uu____5093
    | uu____5094 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5096;_},e1::e2::[])
        ->
        let uu____5101 = str "==>"  in
        let uu____5102 = p_tmArrow p_tmFormula e1  in
        let uu____5103 = p_tmImplies e2  in
        infix0 uu____5101 uu____5102 uu____5103
    | uu____5104 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5115 =
            let uu____5116 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5121 = p_binder false b  in
                   let uu____5122 =
                     let uu____5123 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5123
                      in
                   FStar_Pprint.op_Hat_Hat uu____5121 uu____5122) bs
               in
            let uu____5124 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5116 uu____5124  in
          FStar_Pprint.group uu____5115
      | uu____5125 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5127;_},e1::e2::[])
        ->
        let uu____5132 = str "\\/"  in
        let uu____5133 = p_tmFormula e1  in
        let uu____5134 = p_tmConjunction e2  in
        infix0 uu____5132 uu____5133 uu____5134
    | uu____5135 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5137;_},e1::e2::[])
        ->
        let uu____5142 = str "/\\"  in
        let uu____5143 = p_tmConjunction e1  in
        let uu____5144 = p_tmTuple e2  in
        infix0 uu____5142 uu____5143 uu____5144
    | uu____5145 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5162 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5162
          (fun uu____5170  ->
             match uu____5170 with | (e1,uu____5176) -> p_tmEq e1) args
    | uu____5177 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5182 =
             let uu____5183 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5183  in
           FStar_Pprint.group uu____5182)

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
          let uu____5240 = levels op1  in
          (match uu____5240 with
           | (left1,mine,right1) ->
               let uu____5250 =
                 let uu____5251 = FStar_All.pipe_left str op1  in
                 let uu____5252 = p_tmEq' left1 e1  in
                 let uu____5253 = p_tmEq' right1 e2  in
                 infix0 uu____5251 uu____5252 uu____5253  in
               paren_if_gt curr mine uu____5250)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5254;_},e1::e2::[])
          ->
          let uu____5259 =
            let uu____5260 = p_tmEq e1  in
            let uu____5261 =
              let uu____5262 =
                let uu____5263 =
                  let uu____5264 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5264  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5263  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5262  in
            FStar_Pprint.op_Hat_Hat uu____5260 uu____5261  in
          FStar_Pprint.group uu____5259
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5265;_},e1::[])
          ->
          let uu____5269 = levels "-"  in
          (match uu____5269 with
           | (left1,mine,right1) ->
               let uu____5279 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5279)
      | uu____5280 -> p_tmNoEq e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and (p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun curr  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5345)::(e2,uu____5347)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5367 = is_list e  in Prims.op_Negation uu____5367)
          ->
          let op = "::"  in
          let uu____5369 = levels op  in
          (match uu____5369 with
           | (left1,mine,right1) ->
               let uu____5379 =
                 let uu____5380 = str op  in
                 let uu____5381 = p_tmNoEq' left1 e1  in
                 let uu____5382 = p_tmNoEq' right1 e2  in
                 infix0 uu____5380 uu____5381 uu____5382  in
               paren_if_gt curr mine uu____5379)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5390 = levels op  in
          (match uu____5390 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5404 = p_binder false b  in
                 let uu____5405 =
                   let uu____5406 =
                     let uu____5407 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5407 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5406  in
                 FStar_Pprint.op_Hat_Hat uu____5404 uu____5405  in
               let uu____5408 =
                 let uu____5409 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5410 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5409 uu____5410  in
               paren_if_gt curr mine uu____5408)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5417 = levels op1  in
          (match uu____5417 with
           | (left1,mine,right1) ->
               let uu____5427 =
                 let uu____5428 = str op1  in
                 let uu____5429 = p_tmNoEq' left1 e1  in
                 let uu____5430 = p_tmNoEq' right1 e2  in
                 infix0 uu____5428 uu____5429 uu____5430  in
               paren_if_gt curr mine uu____5427)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5433 =
            let uu____5434 = p_lidentOrUnderscore lid  in
            let uu____5435 =
              let uu____5436 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5436  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5434 uu____5435  in
          FStar_Pprint.group uu____5433
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5457 =
            let uu____5458 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5459 =
              let uu____5460 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              separate_map_last uu____5460 p_simpleDef record_fields  in
            FStar_Pprint.op_Hat_Hat uu____5458 uu____5459  in
          braces_with_nesting uu____5457
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5465;_},e1::[])
          ->
          let uu____5469 =
            let uu____5470 = str "~"  in
            let uu____5471 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5470 uu____5471  in
          FStar_Pprint.group uu____5469
      | uu____5472 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5474 = p_appTerm e  in
    let uu____5475 =
      let uu____5476 =
        let uu____5477 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5477 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5476  in
    FStar_Pprint.op_Hat_Hat uu____5474 uu____5475

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5482 =
            let uu____5483 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5483 t phi  in
          soft_parens_with_nesting uu____5482
      | FStar_Parser_AST.TAnnotated uu____5484 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5489 ->
          let uu____5490 =
            let uu____5491 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5491
             in
          failwith uu____5490
      | FStar_Parser_AST.TVariable uu____5492 ->
          let uu____5493 =
            let uu____5494 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5494
             in
          failwith uu____5493
      | FStar_Parser_AST.NoName uu____5495 ->
          let uu____5496 =
            let uu____5497 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5497
             in
          failwith uu____5496

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5499  ->
      match uu____5499 with
      | (lid,e) ->
          let uu____5506 =
            let uu____5507 = p_qlident lid  in
            let uu____5508 =
              let uu____5509 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5509
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5507 uu____5508  in
          FStar_Pprint.group uu____5506

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5511 when is_general_application e ->
        let uu____5518 = head_and_args e  in
        (match uu____5518 with
         | (head1,args) ->
             let uu____5543 =
               let uu____5554 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5554
               then
                 let uu____5584 =
                   FStar_Util.take
                     (fun uu____5608  ->
                        match uu____5608 with
                        | (uu____5613,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5584 with
                 | (fs_typ_args,args1) ->
                     let uu____5651 =
                       let uu____5652 = p_indexingTerm head1  in
                       let uu____5653 =
                         let uu____5654 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5654 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5652 uu____5653  in
                     (uu____5651, args1)
               else
                 (let uu____5666 = p_indexingTerm head1  in
                  (uu____5666, args))
                in
             (match uu____5543 with
              | (head_doc,args1) ->
                  let uu____5687 =
                    let uu____5688 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5688 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5687))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5708 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5708)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5726 =
               let uu____5727 = p_quident lid  in
               let uu____5728 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5727 uu____5728  in
             FStar_Pprint.group uu____5726
         | hd1::tl1 ->
             let uu____5745 =
               let uu____5746 =
                 let uu____5747 =
                   let uu____5748 = p_quident lid  in
                   let uu____5749 = p_argTerm hd1  in
                   prefix2 uu____5748 uu____5749  in
                 FStar_Pprint.group uu____5747  in
               let uu____5750 =
                 let uu____5751 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5751  in
               FStar_Pprint.op_Hat_Hat uu____5746 uu____5750  in
             FStar_Pprint.group uu____5745)
    | uu____5756 -> p_indexingTerm e

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
         (let uu____5765 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5765 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5767 = str "#"  in
        let uu____5768 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5767 uu____5768
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5770  ->
    match uu____5770 with | (e,uu____5776) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5781;_},e1::e2::[])
          ->
          let uu____5786 =
            let uu____5787 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5788 =
              let uu____5789 =
                let uu____5790 = p_term false false e2  in
                soft_parens_with_nesting uu____5790  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5789  in
            FStar_Pprint.op_Hat_Hat uu____5787 uu____5788  in
          FStar_Pprint.group uu____5786
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5791;_},e1::e2::[])
          ->
          let uu____5796 =
            let uu____5797 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5798 =
              let uu____5799 =
                let uu____5800 = p_term false false e2  in
                soft_brackets_with_nesting uu____5800  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5799  in
            FStar_Pprint.op_Hat_Hat uu____5797 uu____5798  in
          FStar_Pprint.group uu____5796
      | uu____5801 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5806 = p_quident lid  in
        let uu____5807 =
          let uu____5808 =
            let uu____5809 = p_term false false e1  in
            soft_parens_with_nesting uu____5809  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5808  in
        FStar_Pprint.op_Hat_Hat uu____5806 uu____5807
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5815 = str (FStar_Ident.text_of_id op)  in
        let uu____5816 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5815 uu____5816
    | uu____5817 -> p_atomicTermNotQUident e

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
         | uu____5824 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5831 = str (FStar_Ident.text_of_id op)  in
        let uu____5832 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5831 uu____5832
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5836 =
          let uu____5837 =
            let uu____5838 = str (FStar_Ident.text_of_id op)  in
            let uu____5839 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5838 uu____5839  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5837  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5836
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5854 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5855 =
          let uu____5856 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5857 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5856 p_tmEq uu____5857  in
        let uu____5864 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5854 uu____5855 uu____5864
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5867 =
          let uu____5868 = p_atomicTermNotQUident e1  in
          let uu____5869 =
            let uu____5870 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5870  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5868 uu____5869
           in
        FStar_Pprint.group uu____5867
    | uu____5871 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5876 = p_quident constr_lid  in
        let uu____5877 =
          let uu____5878 =
            let uu____5879 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5879  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5878  in
        FStar_Pprint.op_Hat_Hat uu____5876 uu____5877
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5881 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5881 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5883 = p_term false false e1  in
        soft_parens_with_nesting uu____5883
    | uu____5884 when is_array e ->
        let es = extract_from_list e  in
        let uu____5888 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5889 =
          let uu____5890 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____5890
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____5893 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5888 uu____5889 uu____5893
    | uu____5894 when is_list e ->
        let uu____5895 =
          let uu____5896 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5897 = extract_from_list e  in
          separate_map_or_flow_last uu____5896
            (fun ps  -> p_noSeqTerm ps false) uu____5897
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5895 FStar_Pprint.rbracket
    | uu____5902 when is_lex_list e ->
        let uu____5903 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5904 =
          let uu____5905 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5906 = extract_from_list e  in
          separate_map_or_flow_last uu____5905
            (fun ps  -> p_noSeqTerm ps false) uu____5906
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5903 uu____5904 FStar_Pprint.rbracket
    | uu____5911 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5915 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5916 =
          let uu____5917 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5917 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5915 uu____5916 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5921 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5922 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5921 uu____5922
    | FStar_Parser_AST.Op (op,args) when
        let uu____5929 = handleable_op op args  in
        Prims.op_Negation uu____5929 ->
        let uu____5930 =
          let uu____5931 =
            let uu____5932 =
              let uu____5933 =
                let uu____5934 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5934
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5933  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5932  in
          Prims.strcat "Operation " uu____5931  in
        failwith uu____5930
    | FStar_Parser_AST.Uvar uu____5935 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5936 = p_term false false e  in
        soft_parens_with_nesting uu____5936
    | FStar_Parser_AST.Const uu____5937 ->
        let uu____5938 = p_term false false e  in
        soft_parens_with_nesting uu____5938
    | FStar_Parser_AST.Op uu____5939 ->
        let uu____5946 = p_term false false e  in
        soft_parens_with_nesting uu____5946
    | FStar_Parser_AST.Tvar uu____5947 ->
        let uu____5948 = p_term false false e  in
        soft_parens_with_nesting uu____5948
    | FStar_Parser_AST.Var uu____5949 ->
        let uu____5950 = p_term false false e  in
        soft_parens_with_nesting uu____5950
    | FStar_Parser_AST.Name uu____5951 ->
        let uu____5952 = p_term false false e  in
        soft_parens_with_nesting uu____5952
    | FStar_Parser_AST.Construct uu____5953 ->
        let uu____5964 = p_term false false e  in
        soft_parens_with_nesting uu____5964
    | FStar_Parser_AST.Abs uu____5965 ->
        let uu____5972 = p_term false false e  in
        soft_parens_with_nesting uu____5972
    | FStar_Parser_AST.App uu____5973 ->
        let uu____5980 = p_term false false e  in
        soft_parens_with_nesting uu____5980
    | FStar_Parser_AST.Let uu____5981 ->
        let uu____6002 = p_term false false e  in
        soft_parens_with_nesting uu____6002
    | FStar_Parser_AST.LetOpen uu____6003 ->
        let uu____6008 = p_term false false e  in
        soft_parens_with_nesting uu____6008
    | FStar_Parser_AST.Seq uu____6009 ->
        let uu____6014 = p_term false false e  in
        soft_parens_with_nesting uu____6014
    | FStar_Parser_AST.Bind uu____6015 ->
        let uu____6022 = p_term false false e  in
        soft_parens_with_nesting uu____6022
    | FStar_Parser_AST.If uu____6023 ->
        let uu____6030 = p_term false false e  in
        soft_parens_with_nesting uu____6030
    | FStar_Parser_AST.Match uu____6031 ->
        let uu____6046 = p_term false false e  in
        soft_parens_with_nesting uu____6046
    | FStar_Parser_AST.TryWith uu____6047 ->
        let uu____6062 = p_term false false e  in
        soft_parens_with_nesting uu____6062
    | FStar_Parser_AST.Ascribed uu____6063 ->
        let uu____6072 = p_term false false e  in
        soft_parens_with_nesting uu____6072
    | FStar_Parser_AST.Record uu____6073 ->
        let uu____6086 = p_term false false e  in
        soft_parens_with_nesting uu____6086
    | FStar_Parser_AST.Project uu____6087 ->
        let uu____6092 = p_term false false e  in
        soft_parens_with_nesting uu____6092
    | FStar_Parser_AST.Product uu____6093 ->
        let uu____6100 = p_term false false e  in
        soft_parens_with_nesting uu____6100
    | FStar_Parser_AST.Sum uu____6101 ->
        let uu____6108 = p_term false false e  in
        soft_parens_with_nesting uu____6108
    | FStar_Parser_AST.QForall uu____6109 ->
        let uu____6122 = p_term false false e  in
        soft_parens_with_nesting uu____6122
    | FStar_Parser_AST.QExists uu____6123 ->
        let uu____6136 = p_term false false e  in
        soft_parens_with_nesting uu____6136
    | FStar_Parser_AST.Refine uu____6137 ->
        let uu____6142 = p_term false false e  in
        soft_parens_with_nesting uu____6142
    | FStar_Parser_AST.NamedTyp uu____6143 ->
        let uu____6148 = p_term false false e  in
        soft_parens_with_nesting uu____6148
    | FStar_Parser_AST.Requires uu____6149 ->
        let uu____6156 = p_term false false e  in
        soft_parens_with_nesting uu____6156
    | FStar_Parser_AST.Ensures uu____6157 ->
        let uu____6164 = p_term false false e  in
        soft_parens_with_nesting uu____6164
    | FStar_Parser_AST.Attributes uu____6165 ->
        let uu____6168 = p_term false false e  in
        soft_parens_with_nesting uu____6168

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_6169  ->
    match uu___65_6169 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6173 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6173
    | FStar_Const.Const_string (s,uu____6175) ->
        let uu____6176 = str s  in FStar_Pprint.dquotes uu____6176
    | FStar_Const.Const_bytearray (bytes,uu____6178) ->
        let uu____6183 =
          let uu____6184 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6184  in
        let uu____6185 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6183 uu____6185
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6203 =
          match uu___63_6203 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6207 =
          match uu___64_6207 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6218  ->
               match uu____6218 with
               | (s,w) ->
                   let uu____6225 = signedness s  in
                   let uu____6226 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6225 uu____6226)
            sign_width_opt
           in
        let uu____6227 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6227 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6229 = FStar_Range.string_of_range r  in str uu____6229
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6231 = p_quident lid  in
        let uu____6232 =
          let uu____6233 =
            let uu____6234 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6234  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6233  in
        FStar_Pprint.op_Hat_Hat uu____6231 uu____6232

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6236 = str "u#"  in
    let uu____6237 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6236 uu____6237

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6239;_},u1::u2::[])
        ->
        let uu____6244 =
          let uu____6245 = p_universeFrom u1  in
          let uu____6246 =
            let uu____6247 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6247  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6245 uu____6246  in
        FStar_Pprint.group uu____6244
    | FStar_Parser_AST.App uu____6248 ->
        let uu____6255 = head_and_args u  in
        (match uu____6255 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6281 =
                    let uu____6282 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6283 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6291  ->
                           match uu____6291 with
                           | (u1,uu____6297) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6282 uu____6283  in
                  FStar_Pprint.group uu____6281
              | uu____6298 ->
                  let uu____6299 =
                    let uu____6300 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6300
                     in
                  failwith uu____6299))
    | uu____6301 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6325 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6325
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6326;_},uu____6327::uu____6328::[])
        ->
        let uu____6331 = p_universeFrom u  in
        soft_parens_with_nesting uu____6331
    | FStar_Parser_AST.App uu____6332 ->
        let uu____6339 = p_universeFrom u  in
        soft_parens_with_nesting uu____6339
    | uu____6340 ->
        let uu____6341 =
          let uu____6342 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6342
           in
        failwith uu____6341

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
       | FStar_Parser_AST.Module (uu____6382,decls) ->
           let uu____6388 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6388
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6397,decls,uu____6399) ->
           let uu____6404 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6404
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6455  ->
         match uu____6455 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6495,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6501,decls,uu____6503) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6548 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6561;
                 FStar_Parser_AST.doc = uu____6562;
                 FStar_Parser_AST.quals = uu____6563;
                 FStar_Parser_AST.attrs = uu____6564;_}::uu____6565 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6571 =
                   let uu____6574 =
                     let uu____6577 = FStar_List.tl ds  in d :: uu____6577
                      in
                   d0 :: uu____6574  in
                 (uu____6571, (d0.FStar_Parser_AST.drange))
             | uu____6582 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6548 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6640 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6640 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6736 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6736, comments1))))))
  