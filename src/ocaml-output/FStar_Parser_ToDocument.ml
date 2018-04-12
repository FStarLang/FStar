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
    let uu____3325 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3326 =
      let uu____3327 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3328 =
        let uu____3329 = p_qualifiers d.FStar_Parser_AST.quals  in
        let uu____3330 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat uu____3329 uu____3330  in
      FStar_Pprint.op_Hat_Hat uu____3327 uu____3328  in
    FStar_Pprint.op_Hat_Hat uu____3325 uu____3326

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3332 ->
        let uu____3333 =
          let uu____3334 =
            let uu____3337 =
              let uu____3338 = str "@ "  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3338  in
            let uu____3339 =
              let uu____3342 =
                let uu____3343 =
                  let uu____3344 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3344  in
                FStar_Pprint.align uu____3343  in
              [uu____3342; FStar_Pprint.rbracket]  in
            uu____3337 :: uu____3339  in
          FStar_Pprint.flow FStar_Pprint.empty uu____3334  in
        FStar_Pprint.op_Hat_Hat uu____3333 FStar_Pprint.hardline

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3347  ->
    match uu____3347 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3381 =
                match uu____3381 with
                | (kwd,arg) ->
                    let uu____3388 = str "@"  in
                    let uu____3389 =
                      let uu____3390 = str kwd  in
                      let uu____3391 =
                        let uu____3392 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3392
                         in
                      FStar_Pprint.op_Hat_Hat uu____3390 uu____3391  in
                    FStar_Pprint.op_Hat_Hat uu____3388 uu____3389
                 in
              let uu____3393 =
                let uu____3394 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3394 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3393
           in
        let uu____3399 =
          let uu____3400 =
            let uu____3401 =
              let uu____3402 =
                let uu____3403 = str doc1  in
                let uu____3404 =
                  let uu____3405 =
                    let uu____3406 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3406  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3405  in
                FStar_Pprint.op_Hat_Hat uu____3403 uu____3404  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3402  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3401  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3400  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3399

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3410 =
          let uu____3411 = str "val"  in
          let uu____3412 =
            let uu____3413 =
              let uu____3414 = p_lident lid  in
              let uu____3415 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3414 uu____3415  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3413  in
          FStar_Pprint.op_Hat_Hat uu____3411 uu____3412  in
        let uu____3416 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3410 uu____3416
    | FStar_Parser_AST.TopLevelLet (uu____3417,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3442 =
               let uu____3443 = str "let"  in
               let uu____3444 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3443 uu____3444  in
             FStar_Pprint.group uu____3442) lbs
    | uu____3445 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3448 =
          let uu____3449 = str "open"  in
          let uu____3450 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3449 uu____3450  in
        FStar_Pprint.group uu____3448
    | FStar_Parser_AST.Include uid ->
        let uu____3452 =
          let uu____3453 = str "include"  in
          let uu____3454 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3453 uu____3454  in
        FStar_Pprint.group uu____3452
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3457 =
          let uu____3458 = str "module"  in
          let uu____3459 =
            let uu____3460 =
              let uu____3461 = p_uident uid1  in
              let uu____3462 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3461 uu____3462  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3460  in
          FStar_Pprint.op_Hat_Hat uu____3458 uu____3459  in
        let uu____3463 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3457 uu____3463
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3465 =
          let uu____3466 = str "module"  in
          let uu____3467 =
            let uu____3468 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3468  in
          FStar_Pprint.op_Hat_Hat uu____3466 uu____3467  in
        FStar_Pprint.group uu____3465
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3501 = str "effect"  in
          let uu____3502 =
            let uu____3503 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3503  in
          FStar_Pprint.op_Hat_Hat uu____3501 uu____3502  in
        let uu____3504 =
          let uu____3505 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3505 FStar_Pprint.equals
           in
        let uu____3506 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3504 uu____3506
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3524 = str "type"  in
        let uu____3525 = str "and"  in
        precede_break_separate_map uu____3524 uu____3525 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3547 = str "let"  in
          let uu____3548 =
            let uu____3549 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3549 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3547 uu____3548  in
        let uu____3550 =
          let uu____3551 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3551 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3550 p_letbinding lbs
          (fun uu____3559  ->
             match uu____3559 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3568 =
          let uu____3569 = str "val"  in
          let uu____3570 =
            let uu____3571 =
              let uu____3572 = p_lident lid  in
              let uu____3573 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3572 uu____3573  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3571  in
          FStar_Pprint.op_Hat_Hat uu____3569 uu____3570  in
        let uu____3574 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3568 uu____3574
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3578 =
            let uu____3579 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3579 FStar_Util.is_upper  in
          if uu____3578
          then FStar_Pprint.empty
          else
            (let uu____3581 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3581 FStar_Pprint.space)
           in
        let uu____3582 =
          let uu____3583 =
            let uu____3584 = p_ident id1  in
            let uu____3585 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3584 uu____3585  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3583  in
        let uu____3586 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3582 uu____3586
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3593 = str "exception"  in
        let uu____3594 =
          let uu____3595 =
            let uu____3596 = p_uident uid  in
            let uu____3597 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3601 =
                     let uu____3602 = str "of"  in
                     let uu____3603 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3602 uu____3603  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3601) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3596 uu____3597  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3595  in
        FStar_Pprint.op_Hat_Hat uu____3593 uu____3594
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3605 = str "new_effect"  in
        let uu____3606 =
          let uu____3607 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3607  in
        FStar_Pprint.op_Hat_Hat uu____3605 uu____3606
    | FStar_Parser_AST.SubEffect se ->
        let uu____3609 = str "sub_effect"  in
        let uu____3610 =
          let uu____3611 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3611  in
        FStar_Pprint.op_Hat_Hat uu____3609 uu____3610
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3614 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3614 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3615 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3616) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3634 = str "%splice"  in
        let uu____3635 =
          let uu____3636 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3636  in
        FStar_Pprint.op_Hat_Hat uu____3634 uu____3635

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3637  ->
    match uu___54_3637 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3639 = str "#set-options"  in
        let uu____3640 =
          let uu____3641 =
            let uu____3642 = str s  in FStar_Pprint.dquotes uu____3642  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3641  in
        FStar_Pprint.op_Hat_Hat uu____3639 uu____3640
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3646 = str "#reset-options"  in
        let uu____3647 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3651 =
                 let uu____3652 = str s  in FStar_Pprint.dquotes uu____3652
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3651) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3646 uu____3647
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
  fun uu____3676  ->
    match uu____3676 with
    | (typedecl,fsdoc_opt) ->
        let uu____3689 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3690 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3689 uu____3690

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3691  ->
    match uu___55_3691 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3706 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3722 =
          let uu____3723 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3723  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3770 =
          match uu____3770 with
          | (lid1,t,doc_opt) ->
              let uu____3786 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3786
           in
        let p_fields uu____3800 =
          let uu____3801 =
            let uu____3802 =
              let uu____3803 =
                let uu____3804 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3804 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3803  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3802  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3801  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3868 =
          match uu____3868 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3894 =
                  let uu____3895 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3895  in
                FStar_Range.extend_to_end_of_line uu____3894  in
              let p_constructorBranch decl =
                let uu____3928 =
                  let uu____3929 =
                    let uu____3930 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3930  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3929  in
                FStar_Pprint.group uu____3928  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3950 =
          FStar_Pprint.separate_map FStar_Pprint.hardline
            p_constructorBranchAndComments ct_decls
           in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3965  ->
             let uu____3966 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3966)

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
            let uu____3981 = p_ident lid  in
            let uu____3982 =
              let uu____3983 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3983  in
            FStar_Pprint.op_Hat_Hat uu____3981 uu____3982
          else
            (let binders_doc =
               let uu____3986 = p_typars bs  in
               let uu____3987 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3991 =
                        let uu____3992 =
                          let uu____3993 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3993
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3992
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3991) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3986 uu____3987  in
             let uu____3994 = p_ident lid  in
             let uu____3995 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3994 binders_doc uu____3995)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____3997  ->
      match uu____3997 with
      | (lid,t,doc_opt) ->
          let uu____4013 =
            let uu____4014 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4015 =
              let uu____4016 = p_lident lid  in
              let uu____4017 =
                let uu____4018 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4018  in
              FStar_Pprint.op_Hat_Hat uu____4016 uu____4017  in
            FStar_Pprint.op_Hat_Hat uu____4014 uu____4015  in
          FStar_Pprint.group uu____4013

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4019  ->
    match uu____4019 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4047 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4048 =
          let uu____4049 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4050 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4055 =
                   let uu____4056 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4056  in
                 let uu____4057 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4055 uu____4057) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4049 uu____4050  in
        FStar_Pprint.op_Hat_Hat uu____4047 uu____4048

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4058  ->
    match uu____4058 with
    | (pat,uu____4064) ->
        let uu____4065 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4084 =
                let uu____4085 =
                  let uu____4086 =
                    let uu____4087 =
                      let uu____4088 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4088
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4087  in
                  FStar_Pprint.group uu____4086  in
                FStar_Pprint.op_Hat_Hat break1 uu____4085  in
              (pat1, uu____4084)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4100 =
                let uu____4101 =
                  let uu____4102 =
                    let uu____4103 =
                      let uu____4104 =
                        let uu____4105 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4105
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4104
                       in
                    FStar_Pprint.group uu____4103  in
                  let uu____4106 =
                    let uu____4107 =
                      let uu____4108 = str "by"  in
                      let uu____4109 =
                        let uu____4110 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4110
                         in
                      FStar_Pprint.op_Hat_Hat uu____4108 uu____4109  in
                    FStar_Pprint.group uu____4107  in
                  FStar_Pprint.op_Hat_Hat uu____4102 uu____4106  in
                FStar_Pprint.op_Hat_Hat break1 uu____4101  in
              (pat1, uu____4100)
          | uu____4111 -> (pat, FStar_Pprint.empty)  in
        (match uu____4065 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4115);
                     FStar_Parser_AST.prange = uu____4116;_},pats)
                  ->
                  let uu____4126 =
                    let uu____4127 = p_lident x  in
                    let uu____4128 =
                      let uu____4129 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4129 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4127 uu____4128  in
                  FStar_Pprint.group uu____4126
              | uu____4130 ->
                  let uu____4131 =
                    let uu____4132 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4132 ascr_doc  in
                  FStar_Pprint.group uu____4131))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4133  ->
    match uu____4133 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4141 =
          let uu____4142 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4142  in
        let uu____4143 = p_term false false e  in
        prefix2 uu____4141 uu____4143

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_4144  ->
    match uu___56_4144 with
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
        let uu____4169 = p_uident uid  in
        let uu____4170 = p_binders true bs  in
        let uu____4171 =
          let uu____4172 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4172  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4169 uu____4170 uu____4171

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
          let uu____4181 =
            let uu____4182 =
              let uu____4183 =
                let uu____4184 = p_uident uid  in
                let uu____4185 = p_binders true bs  in
                let uu____4186 =
                  let uu____4187 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4187  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4184 uu____4185 uu____4186
                 in
              FStar_Pprint.group uu____4183  in
            let uu____4188 =
              let uu____4189 = str "with"  in
              let uu____4190 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4189 uu____4190  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4182 uu____4188  in
          braces_with_nesting uu____4181

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
          let uu____4221 =
            let uu____4222 = p_lident lid  in
            let uu____4223 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4222 uu____4223  in
          let uu____4224 = p_simpleTerm ps false e  in
          prefix2 uu____4221 uu____4224
      | uu____4225 ->
          let uu____4226 =
            let uu____4227 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4227
             in
          failwith uu____4226

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4285 =
        match uu____4285 with
        | (kwd,t) ->
            let uu____4292 =
              let uu____4293 = str kwd  in
              let uu____4294 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4293 uu____4294  in
            let uu____4295 = p_simpleTerm ps false t  in
            prefix2 uu____4292 uu____4295
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4300 =
      let uu____4301 =
        let uu____4302 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4303 =
          let uu____4304 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4304  in
        FStar_Pprint.op_Hat_Hat uu____4302 uu____4303  in
      let uu____4305 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4301 uu____4305  in
    let uu____4306 =
      let uu____4307 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4307  in
    FStar_Pprint.op_Hat_Hat uu____4300 uu____4306

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4308  ->
    match uu___57_4308 with
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
    | uu____4310 ->
        let uu____4311 =
          let uu____4312 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4312  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4311 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4315  ->
    match uu___58_4315 with
    | FStar_Parser_AST.Rec  ->
        let uu____4316 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4316
    | FStar_Parser_AST.Mutable  ->
        let uu____4317 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4317
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4318  ->
    match uu___59_4318 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4323 =
          let uu____4324 =
            let uu____4325 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4325  in
          FStar_Pprint.separate_map uu____4324 p_tuplePattern pats  in
        FStar_Pprint.group uu____4323
    | uu____4326 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4333 =
          let uu____4334 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4334 p_constructorPattern pats  in
        FStar_Pprint.group uu____4333
    | uu____4335 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4338;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4343 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4344 = p_constructorPattern hd1  in
        let uu____4345 = p_constructorPattern tl1  in
        infix0 uu____4343 uu____4344 uu____4345
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4347;_},pats)
        ->
        let uu____4353 = p_quident uid  in
        let uu____4354 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4353 uu____4354
    | uu____4355 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4371;
               FStar_Parser_AST.blevel = uu____4372;
               FStar_Parser_AST.aqual = uu____4373;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4379 =
               let uu____4380 = p_ident lid  in
               p_refinement aqual uu____4380 t1 phi  in
             soft_parens_with_nesting uu____4379
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4382;
               FStar_Parser_AST.blevel = uu____4383;
               FStar_Parser_AST.aqual = uu____4384;_},phi))
             ->
             let uu____4386 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4386
         | uu____4387 ->
             let uu____4392 =
               let uu____4393 = p_tuplePattern pat  in
               let uu____4394 =
                 let uu____4395 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4396 =
                   let uu____4397 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4397  in
                 FStar_Pprint.op_Hat_Hat uu____4395 uu____4396  in
               FStar_Pprint.op_Hat_Hat uu____4393 uu____4394  in
             soft_parens_with_nesting uu____4392)
    | FStar_Parser_AST.PatList pats ->
        let uu____4401 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4401 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4416 =
          match uu____4416 with
          | (lid,pat) ->
              let uu____4423 = p_qlident lid  in
              let uu____4424 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4423 uu____4424
           in
        let uu____4425 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4425
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4435 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4436 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4437 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4435 uu____4436 uu____4437
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4448 =
          let uu____4449 =
            let uu____4450 = str (FStar_Ident.text_of_id op)  in
            let uu____4451 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4450 uu____4451  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4449  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4448
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4459 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4460 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4459 uu____4460
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4462 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4465;
           FStar_Parser_AST.prange = uu____4466;_},uu____4467)
        ->
        let uu____4472 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4472
    | FStar_Parser_AST.PatTuple (uu____4473,false ) ->
        let uu____4478 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4478
    | uu____4479 ->
        let uu____4480 =
          let uu____4481 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4481  in
        failwith uu____4480

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4485 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4486 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4485 uu____4486
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4493;
                   FStar_Parser_AST.blevel = uu____4494;
                   FStar_Parser_AST.aqual = uu____4495;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4497 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4497 t1 phi
            | uu____4498 ->
                let uu____4499 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4500 =
                  let uu____4501 = p_lident lid  in
                  let uu____4502 =
                    let uu____4503 =
                      let uu____4504 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4505 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4504 uu____4505  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4503  in
                  FStar_Pprint.op_Hat_Hat uu____4501 uu____4502  in
                FStar_Pprint.op_Hat_Hat uu____4499 uu____4500
             in
          if is_atomic
          then
            let uu____4506 =
              let uu____4507 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4507  in
            FStar_Pprint.group uu____4506
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4509 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4516;
                  FStar_Parser_AST.blevel = uu____4517;
                  FStar_Parser_AST.aqual = uu____4518;_},phi)
               ->
               if is_atomic
               then
                 let uu____4520 =
                   let uu____4521 =
                     let uu____4522 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4522 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4521  in
                 FStar_Pprint.group uu____4520
               else
                 (let uu____4524 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4524)
           | uu____4525 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4533 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4534 =
            let uu____4535 =
              let uu____4536 =
                let uu____4537 = p_appTerm t  in
                let uu____4538 =
                  let uu____4539 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4539  in
                FStar_Pprint.op_Hat_Hat uu____4537 uu____4538  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4536  in
            FStar_Pprint.op_Hat_Hat binder uu____4535  in
          FStar_Pprint.op_Hat_Hat uu____4533 uu____4534

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
            let uu____4562 =
              let uu____4563 =
                let uu____4564 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4564 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4563  in
            let uu____4565 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4562 uu____4565
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4569 =
              let uu____4570 =
                let uu____4571 =
                  let uu____4572 = p_lident x  in
                  let uu____4573 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4572 uu____4573  in
                let uu____4574 =
                  let uu____4575 = p_noSeqTerm true false e1  in
                  let uu____4576 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4575 uu____4576  in
                op_Hat_Slash_Plus_Hat uu____4571 uu____4574  in
              FStar_Pprint.group uu____4570  in
            let uu____4577 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4569 uu____4577
        | uu____4578 ->
            let uu____4579 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4579

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
            let uu____4590 =
              let uu____4591 = p_tmIff e1  in
              let uu____4592 =
                let uu____4593 =
                  let uu____4594 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4594
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4593  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4591 uu____4592  in
            FStar_Pprint.group uu____4590
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4600 =
              let uu____4601 = p_tmIff e1  in
              let uu____4602 =
                let uu____4603 =
                  let uu____4604 =
                    let uu____4605 = p_typ false false t  in
                    let uu____4606 =
                      let uu____4607 = str "by"  in
                      let uu____4608 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4607 uu____4608  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4605 uu____4606  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4604
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4603  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4601 uu____4602  in
            FStar_Pprint.group uu____4600
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4609;_},e1::e2::e3::[])
            ->
            let uu____4615 =
              let uu____4616 =
                let uu____4617 =
                  let uu____4618 = p_atomicTermNotQUident e1  in
                  let uu____4619 =
                    let uu____4620 =
                      let uu____4621 =
                        let uu____4622 = p_term false false e2  in
                        soft_parens_with_nesting uu____4622  in
                      let uu____4623 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4621 uu____4623  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4620  in
                  FStar_Pprint.op_Hat_Hat uu____4618 uu____4619  in
                FStar_Pprint.group uu____4617  in
              let uu____4624 =
                let uu____4625 = p_noSeqTerm ps pb e3  in jump2 uu____4625
                 in
              FStar_Pprint.op_Hat_Hat uu____4616 uu____4624  in
            FStar_Pprint.group uu____4615
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4626;_},e1::e2::e3::[])
            ->
            let uu____4632 =
              let uu____4633 =
                let uu____4634 =
                  let uu____4635 = p_atomicTermNotQUident e1  in
                  let uu____4636 =
                    let uu____4637 =
                      let uu____4638 =
                        let uu____4639 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4639  in
                      let uu____4640 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4638 uu____4640  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4637  in
                  FStar_Pprint.op_Hat_Hat uu____4635 uu____4636  in
                FStar_Pprint.group uu____4634  in
              let uu____4641 =
                let uu____4642 = p_noSeqTerm ps pb e3  in jump2 uu____4642
                 in
              FStar_Pprint.op_Hat_Hat uu____4633 uu____4641  in
            FStar_Pprint.group uu____4632
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4652 =
              let uu____4653 = str "requires"  in
              let uu____4654 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4653 uu____4654  in
            FStar_Pprint.group uu____4652
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4664 =
              let uu____4665 = str "ensures"  in
              let uu____4666 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4665 uu____4666  in
            FStar_Pprint.group uu____4664
        | FStar_Parser_AST.Attributes es ->
            let uu____4670 =
              let uu____4671 = str "attributes"  in
              let uu____4672 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4671 uu____4672  in
            FStar_Pprint.group uu____4670
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4676 =
                let uu____4677 =
                  let uu____4678 = str "if"  in
                  let uu____4679 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4678 uu____4679  in
                let uu____4680 =
                  let uu____4681 = str "then"  in
                  let uu____4682 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4681 uu____4682  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4677 uu____4680  in
              FStar_Pprint.group uu____4676
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4685,uu____4686,e31) when
                     is_unit e31 ->
                     let uu____4688 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4688
                 | uu____4689 -> p_noSeqTerm false false e2  in
               let uu____4690 =
                 let uu____4691 =
                   let uu____4692 = str "if"  in
                   let uu____4693 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4692 uu____4693  in
                 let uu____4694 =
                   let uu____4695 =
                     let uu____4696 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4696 e2_doc  in
                   let uu____4697 =
                     let uu____4698 = str "else"  in
                     let uu____4699 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4698 uu____4699  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4695 uu____4697  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4691 uu____4694  in
               FStar_Pprint.group uu____4690)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4722 =
              let uu____4723 =
                let uu____4724 =
                  let uu____4725 = str "try"  in
                  let uu____4726 = p_noSeqTerm false false e1  in
                  prefix2 uu____4725 uu____4726  in
                let uu____4727 =
                  let uu____4728 = str "with"  in
                  let uu____4729 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4728 uu____4729  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4724 uu____4727  in
              FStar_Pprint.group uu____4723  in
            let uu____4738 = paren_if (ps || pb)  in uu____4738 uu____4722
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4763 =
              let uu____4764 =
                let uu____4765 =
                  let uu____4766 = str "match"  in
                  let uu____4767 = p_noSeqTerm false false e1  in
                  let uu____4768 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4766 uu____4767 uu____4768
                   in
                let uu____4769 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4765 uu____4769  in
              FStar_Pprint.group uu____4764  in
            let uu____4778 = paren_if (ps || pb)  in uu____4778 uu____4763
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4783 =
              let uu____4784 =
                let uu____4785 =
                  let uu____4786 = str "let open"  in
                  let uu____4787 = p_quident uid  in
                  let uu____4788 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4786 uu____4787 uu____4788
                   in
                let uu____4789 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4785 uu____4789  in
              FStar_Pprint.group uu____4784  in
            let uu____4790 = paren_if ps  in uu____4790 uu____4783
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____4846 is_last =
              match uu____4846 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____4879 =
                          let uu____4880 = str "let"  in
                          let uu____4881 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4880 uu____4881
                           in
                        FStar_Pprint.group uu____4879
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____4882 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____4887 =
                    if is_last
                    then
                      let uu____4888 =
                        let uu____4889 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____4890 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____4889 doc_expr
                          uu____4890
                         in
                      FStar_Pprint.group uu____4888
                    else
                      (let uu____4892 =
                         let uu____4893 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____4893 doc_expr
                          in
                       FStar_Pprint.group uu____4892)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____4887
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____4939 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____4939
                     else
                       (let uu____4947 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____4947)) lbs
               in
            let lbs_doc =
              let uu____4955 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____4955  in
            let uu____4956 =
              let uu____4957 =
                let uu____4958 =
                  let uu____4959 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____4959
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____4958  in
              FStar_Pprint.group uu____4957  in
            let uu____4960 = paren_if ps  in uu____4960 uu____4956
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4965;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____4968;
                                                             FStar_Parser_AST.level
                                                               = uu____4969;_})
            when matches_var maybe_x x ->
            let uu____4996 =
              let uu____4997 =
                let uu____4998 = str "function"  in
                let uu____4999 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4998 uu____4999  in
              FStar_Pprint.group uu____4997  in
            let uu____5008 = paren_if (ps || pb)  in uu____5008 uu____4996
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5012 =
              let uu____5013 = str "quote"  in
              let uu____5014 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5013 uu____5014  in
            FStar_Pprint.group uu____5012
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5016 =
              let uu____5017 = str "`"  in
              let uu____5018 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5017 uu____5018  in
            FStar_Pprint.group uu____5016
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5020 =
              let uu____5021 = str "%`"  in
              let uu____5022 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5021 uu____5022  in
            FStar_Pprint.group uu____5020
        | uu____5023 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_5024  ->
    match uu___60_5024 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5036 =
          let uu____5037 =
            let uu____5038 = str "[@"  in
            let uu____5039 =
              let uu____5040 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5041 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5040 uu____5041  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5038 uu____5039  in
          FStar_Pprint.group uu____5037  in
        FStar_Pprint.op_Hat_Hat uu____5036 break1

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
            let uu____5063 =
              let uu____5064 =
                let uu____5065 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5065 FStar_Pprint.space  in
              let uu____5066 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5064 uu____5066 FStar_Pprint.dot
               in
            let uu____5067 =
              let uu____5068 = p_trigger trigger  in
              let uu____5069 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5068 uu____5069  in
            prefix2 uu____5063 uu____5067
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5085 =
              let uu____5086 =
                let uu____5087 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5087 FStar_Pprint.space  in
              let uu____5088 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5086 uu____5088 FStar_Pprint.dot
               in
            let uu____5089 =
              let uu____5090 = p_trigger trigger  in
              let uu____5091 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5090 uu____5091  in
            prefix2 uu____5085 uu____5089
        | uu____5092 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5094 -> str "forall"
    | FStar_Parser_AST.QExists uu____5107 -> str "exists"
    | uu____5120 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_5121  ->
    match uu___61_5121 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5133 =
          let uu____5134 =
            let uu____5135 = str "pattern"  in
            let uu____5136 =
              let uu____5137 =
                let uu____5138 = p_disjunctivePats pats  in jump2 uu____5138
                 in
              let uu____5139 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5137 uu____5139  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5135 uu____5136  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5134  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5133

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5145 = str "\\/"  in
    FStar_Pprint.separate_map uu____5145 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5151 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5151

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5161 =
              let uu____5162 =
                let uu____5163 = str "fun"  in
                let uu____5164 =
                  let uu____5165 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5165
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5163 uu____5164  in
              let uu____5166 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5162 uu____5166  in
            let uu____5167 = paren_if ps  in uu____5167 uu____5161
        | uu____5170 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5174  ->
      match uu____5174 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let uu____5194 =
              let uu____5195 =
                let uu____5196 =
                  let uu____5197 =
                    let uu____5198 =
                      let uu____5199 = p_tuplePattern p  in
                      let uu____5200 =
                        let uu____5201 = p_maybeWhen when_opt  in
                        FStar_Pprint.op_Hat_Hat uu____5201
                          FStar_Pprint.rarrow
                         in
                      op_Hat_Slash_Plus_Hat uu____5199 uu____5200  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5198  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5197  in
                FStar_Pprint.group uu____5196  in
              let uu____5202 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat uu____5195 uu____5202  in
            FStar_Pprint.group uu____5194  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5211 =
                      let uu____5212 =
                        let uu____5213 =
                          let uu____5214 =
                            let uu____5215 =
                              let uu____5216 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5216  in
                            FStar_Pprint.separate_map uu____5215
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          let uu____5217 =
                            FStar_Pprint.op_Hat_Hat break1 last_pat_branch
                             in
                          FStar_Pprint.op_Hat_Hat uu____5214 uu____5217  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5213
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5212  in
                    FStar_Pprint.group uu____5211
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5218 -> one_pattern_branch pat)

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_5219  ->
    match uu___62_5219 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5223 = str "when"  in
        let uu____5224 =
          let uu____5225 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5225 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5223 uu____5224

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5227;_},e1::e2::[])
        ->
        let uu____5232 = str "<==>"  in
        let uu____5233 = p_tmImplies e1  in
        let uu____5234 = p_tmIff e2  in
        infix0 uu____5232 uu____5233 uu____5234
    | uu____5235 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5237;_},e1::e2::[])
        ->
        let uu____5242 = str "==>"  in
        let uu____5243 = p_tmArrow p_tmFormula e1  in
        let uu____5244 = p_tmImplies e2  in
        infix0 uu____5242 uu____5243 uu____5244
    | uu____5245 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5256 =
            let uu____5257 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5262 = p_binder false b  in
                   let uu____5263 =
                     let uu____5264 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5264
                      in
                   FStar_Pprint.op_Hat_Hat uu____5262 uu____5263) bs
               in
            let uu____5265 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5257 uu____5265  in
          FStar_Pprint.group uu____5256
      | uu____5266 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5268;_},e1::e2::[])
        ->
        let uu____5273 = str "\\/"  in
        let uu____5274 = p_tmFormula e1  in
        let uu____5275 = p_tmConjunction e2  in
        infix0 uu____5273 uu____5274 uu____5275
    | uu____5276 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5278;_},e1::e2::[])
        ->
        let uu____5283 = str "/\\"  in
        let uu____5284 = p_tmConjunction e1  in
        let uu____5285 = p_tmTuple e2  in
        infix0 uu____5283 uu____5284 uu____5285
    | uu____5286 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5303 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5303
          (fun uu____5311  ->
             match uu____5311 with | (e1,uu____5317) -> p_tmEq e1) args
    | uu____5318 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5323 =
             let uu____5324 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5324  in
           FStar_Pprint.group uu____5323)

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
            let uu____5387 = levels op1  in
            (match uu____5387 with
             | (left1,mine,right1) ->
                 let uu____5397 =
                   let uu____5398 = FStar_All.pipe_left str op1  in
                   let uu____5399 = p_tmEqWith' p_X left1 e1  in
                   let uu____5400 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5398 uu____5399 uu____5400  in
                 paren_if_gt curr mine uu____5397)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5401;_},e1::e2::[])
            ->
            let uu____5406 =
              let uu____5407 = p_tmEqWith p_X e1  in
              let uu____5408 =
                let uu____5409 =
                  let uu____5410 =
                    let uu____5411 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5411  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5410  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5409  in
              FStar_Pprint.op_Hat_Hat uu____5407 uu____5408  in
            FStar_Pprint.group uu____5406
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5412;_},e1::[])
            ->
            let uu____5416 = levels "-"  in
            (match uu____5416 with
             | (left1,mine,right1) ->
                 let uu____5426 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5426)
        | uu____5427 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5498)::(e2,uu____5500)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5520 = is_list e  in Prims.op_Negation uu____5520)
            ->
            let op = "::"  in
            let uu____5522 = levels op  in
            (match uu____5522 with
             | (left1,mine,right1) ->
                 let uu____5532 =
                   let uu____5533 = str op  in
                   let uu____5534 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5535 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5533 uu____5534 uu____5535  in
                 paren_if_gt curr mine uu____5532)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5543 = levels op  in
            (match uu____5543 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5557 = p_binder false b  in
                   let uu____5558 =
                     let uu____5559 =
                       let uu____5560 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5560 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5559
                      in
                   FStar_Pprint.op_Hat_Hat uu____5557 uu____5558  in
                 let uu____5561 =
                   let uu____5562 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5563 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5562 uu____5563  in
                 paren_if_gt curr mine uu____5561)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5570 = levels op1  in
            (match uu____5570 with
             | (left1,mine,right1) ->
                 let uu____5580 =
                   let uu____5581 = str op1  in
                   let uu____5582 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5583 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5581 uu____5582 uu____5583  in
                 paren_if_gt curr mine uu____5580)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5602 =
              let uu____5603 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5604 =
                let uu____5605 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5605 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5603 uu____5604  in
            braces_with_nesting uu____5602
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5610;_},e1::[])
            ->
            let uu____5614 =
              let uu____5615 = str "~"  in
              let uu____5616 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5615 uu____5616  in
            FStar_Pprint.group uu____5614
        | uu____5617 -> p_X e

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
        let uu____5624 =
          let uu____5625 = p_lidentOrUnderscore lid  in
          let uu____5626 =
            let uu____5627 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5627  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5625 uu____5626  in
        FStar_Pprint.group uu____5624
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5630 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5632 = p_appTerm e  in
    let uu____5633 =
      let uu____5634 =
        let uu____5635 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5635 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5634  in
    FStar_Pprint.op_Hat_Hat uu____5632 uu____5633

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5640 =
            let uu____5641 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5641 t phi  in
          soft_parens_with_nesting uu____5640
      | FStar_Parser_AST.TAnnotated uu____5642 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5647 ->
          let uu____5648 =
            let uu____5649 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5649
             in
          failwith uu____5648
      | FStar_Parser_AST.TVariable uu____5650 ->
          let uu____5651 =
            let uu____5652 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5652
             in
          failwith uu____5651
      | FStar_Parser_AST.NoName uu____5653 ->
          let uu____5654 =
            let uu____5655 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5655
             in
          failwith uu____5654

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5657  ->
      match uu____5657 with
      | (lid,e) ->
          let uu____5664 =
            let uu____5665 = p_qlident lid  in
            let uu____5666 =
              let uu____5667 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5667
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5665 uu____5666  in
          FStar_Pprint.group uu____5664

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5669 when is_general_application e ->
        let uu____5676 = head_and_args e  in
        (match uu____5676 with
         | (head1,args) ->
             let uu____5701 =
               let uu____5712 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5712
               then
                 let uu____5742 =
                   FStar_Util.take
                     (fun uu____5766  ->
                        match uu____5766 with
                        | (uu____5771,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5742 with
                 | (fs_typ_args,args1) ->
                     let uu____5809 =
                       let uu____5810 = p_indexingTerm head1  in
                       let uu____5811 =
                         let uu____5812 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5812 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5810 uu____5811  in
                     (uu____5809, args1)
               else
                 (let uu____5824 = p_indexingTerm head1  in
                  (uu____5824, args))
                in
             (match uu____5701 with
              | (head_doc,args1) ->
                  let uu____5845 =
                    let uu____5846 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5846 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5845))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5866 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5866)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5884 =
               let uu____5885 = p_quident lid  in
               let uu____5886 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5885 uu____5886  in
             FStar_Pprint.group uu____5884
         | hd1::tl1 ->
             let uu____5903 =
               let uu____5904 =
                 let uu____5905 =
                   let uu____5906 = p_quident lid  in
                   let uu____5907 = p_argTerm hd1  in
                   prefix2 uu____5906 uu____5907  in
                 FStar_Pprint.group uu____5905  in
               let uu____5908 =
                 let uu____5909 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5909  in
               FStar_Pprint.op_Hat_Hat uu____5904 uu____5908  in
             FStar_Pprint.group uu____5903)
    | uu____5914 -> p_indexingTerm e

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
         (let uu____5923 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5923 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5925 = str "#"  in
        let uu____5926 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5925 uu____5926
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5928  ->
    match uu____5928 with | (e,uu____5934) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5939;_},e1::e2::[])
          ->
          let uu____5944 =
            let uu____5945 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5946 =
              let uu____5947 =
                let uu____5948 = p_term false false e2  in
                soft_parens_with_nesting uu____5948  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5947  in
            FStar_Pprint.op_Hat_Hat uu____5945 uu____5946  in
          FStar_Pprint.group uu____5944
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5949;_},e1::e2::[])
          ->
          let uu____5954 =
            let uu____5955 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5956 =
              let uu____5957 =
                let uu____5958 = p_term false false e2  in
                soft_brackets_with_nesting uu____5958  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5957  in
            FStar_Pprint.op_Hat_Hat uu____5955 uu____5956  in
          FStar_Pprint.group uu____5954
      | uu____5959 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5964 = p_quident lid  in
        let uu____5965 =
          let uu____5966 =
            let uu____5967 = p_term false false e1  in
            soft_parens_with_nesting uu____5967  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5966  in
        FStar_Pprint.op_Hat_Hat uu____5964 uu____5965
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5973 = str (FStar_Ident.text_of_id op)  in
        let uu____5974 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5973 uu____5974
    | uu____5975 -> p_atomicTermNotQUident e

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
         | uu____5982 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5989 = str (FStar_Ident.text_of_id op)  in
        let uu____5990 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5989 uu____5990
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5994 =
          let uu____5995 =
            let uu____5996 = str (FStar_Ident.text_of_id op)  in
            let uu____5997 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5996 uu____5997  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5995  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5994
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6012 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6013 =
          let uu____6014 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6015 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6014 p_tmEq uu____6015  in
        let uu____6022 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6012 uu____6013 uu____6022
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6025 =
          let uu____6026 = p_atomicTermNotQUident e1  in
          let uu____6027 =
            let uu____6028 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6028  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6026 uu____6027
           in
        FStar_Pprint.group uu____6025
    | uu____6029 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6034 = p_quident constr_lid  in
        let uu____6035 =
          let uu____6036 =
            let uu____6037 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6037  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6036  in
        FStar_Pprint.op_Hat_Hat uu____6034 uu____6035
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6039 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6039 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6041 = p_term false false e1  in
        soft_parens_with_nesting uu____6041
    | uu____6042 when is_array e ->
        let es = extract_from_list e  in
        let uu____6046 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6047 =
          let uu____6048 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6048
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6051 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6046 uu____6047 uu____6051
    | uu____6052 when is_list e ->
        let uu____6053 =
          let uu____6054 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6055 = extract_from_list e  in
          separate_map_or_flow_last uu____6054
            (fun ps  -> p_noSeqTerm ps false) uu____6055
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6053 FStar_Pprint.rbracket
    | uu____6060 when is_lex_list e ->
        let uu____6061 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6062 =
          let uu____6063 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6064 = extract_from_list e  in
          separate_map_or_flow_last uu____6063
            (fun ps  -> p_noSeqTerm ps false) uu____6064
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6061 uu____6062 FStar_Pprint.rbracket
    | uu____6069 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6073 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6074 =
          let uu____6075 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6075 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6073 uu____6074 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6079 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6080 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6079 uu____6080
    | FStar_Parser_AST.Op (op,args) when
        let uu____6087 = handleable_op op args  in
        Prims.op_Negation uu____6087 ->
        let uu____6088 =
          let uu____6089 =
            let uu____6090 =
              let uu____6091 =
                let uu____6092 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6092
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6091  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6090  in
          Prims.strcat "Operation " uu____6089  in
        failwith uu____6088
    | FStar_Parser_AST.Uvar uu____6093 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6094 = p_term false false e  in
        soft_parens_with_nesting uu____6094
    | FStar_Parser_AST.Const uu____6095 ->
        let uu____6096 = p_term false false e  in
        soft_parens_with_nesting uu____6096
    | FStar_Parser_AST.Op uu____6097 ->
        let uu____6104 = p_term false false e  in
        soft_parens_with_nesting uu____6104
    | FStar_Parser_AST.Tvar uu____6105 ->
        let uu____6106 = p_term false false e  in
        soft_parens_with_nesting uu____6106
    | FStar_Parser_AST.Var uu____6107 ->
        let uu____6108 = p_term false false e  in
        soft_parens_with_nesting uu____6108
    | FStar_Parser_AST.Name uu____6109 ->
        let uu____6110 = p_term false false e  in
        soft_parens_with_nesting uu____6110
    | FStar_Parser_AST.Construct uu____6111 ->
        let uu____6122 = p_term false false e  in
        soft_parens_with_nesting uu____6122
    | FStar_Parser_AST.Abs uu____6123 ->
        let uu____6130 = p_term false false e  in
        soft_parens_with_nesting uu____6130
    | FStar_Parser_AST.App uu____6131 ->
        let uu____6138 = p_term false false e  in
        soft_parens_with_nesting uu____6138
    | FStar_Parser_AST.Let uu____6139 ->
        let uu____6160 = p_term false false e  in
        soft_parens_with_nesting uu____6160
    | FStar_Parser_AST.LetOpen uu____6161 ->
        let uu____6166 = p_term false false e  in
        soft_parens_with_nesting uu____6166
    | FStar_Parser_AST.Seq uu____6167 ->
        let uu____6172 = p_term false false e  in
        soft_parens_with_nesting uu____6172
    | FStar_Parser_AST.Bind uu____6173 ->
        let uu____6180 = p_term false false e  in
        soft_parens_with_nesting uu____6180
    | FStar_Parser_AST.If uu____6181 ->
        let uu____6188 = p_term false false e  in
        soft_parens_with_nesting uu____6188
    | FStar_Parser_AST.Match uu____6189 ->
        let uu____6204 = p_term false false e  in
        soft_parens_with_nesting uu____6204
    | FStar_Parser_AST.TryWith uu____6205 ->
        let uu____6220 = p_term false false e  in
        soft_parens_with_nesting uu____6220
    | FStar_Parser_AST.Ascribed uu____6221 ->
        let uu____6230 = p_term false false e  in
        soft_parens_with_nesting uu____6230
    | FStar_Parser_AST.Record uu____6231 ->
        let uu____6244 = p_term false false e  in
        soft_parens_with_nesting uu____6244
    | FStar_Parser_AST.Project uu____6245 ->
        let uu____6250 = p_term false false e  in
        soft_parens_with_nesting uu____6250
    | FStar_Parser_AST.Product uu____6251 ->
        let uu____6258 = p_term false false e  in
        soft_parens_with_nesting uu____6258
    | FStar_Parser_AST.Sum uu____6259 ->
        let uu____6266 = p_term false false e  in
        soft_parens_with_nesting uu____6266
    | FStar_Parser_AST.QForall uu____6267 ->
        let uu____6280 = p_term false false e  in
        soft_parens_with_nesting uu____6280
    | FStar_Parser_AST.QExists uu____6281 ->
        let uu____6294 = p_term false false e  in
        soft_parens_with_nesting uu____6294
    | FStar_Parser_AST.Refine uu____6295 ->
        let uu____6300 = p_term false false e  in
        soft_parens_with_nesting uu____6300
    | FStar_Parser_AST.NamedTyp uu____6301 ->
        let uu____6306 = p_term false false e  in
        soft_parens_with_nesting uu____6306
    | FStar_Parser_AST.Requires uu____6307 ->
        let uu____6314 = p_term false false e  in
        soft_parens_with_nesting uu____6314
    | FStar_Parser_AST.Ensures uu____6315 ->
        let uu____6322 = p_term false false e  in
        soft_parens_with_nesting uu____6322
    | FStar_Parser_AST.Attributes uu____6323 ->
        let uu____6326 = p_term false false e  in
        soft_parens_with_nesting uu____6326
    | FStar_Parser_AST.Quote uu____6327 ->
        let uu____6332 = p_term false false e  in
        soft_parens_with_nesting uu____6332
    | FStar_Parser_AST.VQuote uu____6333 ->
        let uu____6334 = p_term false false e  in
        soft_parens_with_nesting uu____6334

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_6335  ->
    match uu___65_6335 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6339 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6339
    | FStar_Const.Const_string (s,uu____6341) ->
        let uu____6342 = str s  in FStar_Pprint.dquotes uu____6342
    | FStar_Const.Const_bytearray (bytes,uu____6344) ->
        let uu____6349 =
          let uu____6350 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6350  in
        let uu____6351 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6349 uu____6351
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6369 =
          match uu___63_6369 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6373 =
          match uu___64_6373 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6384  ->
               match uu____6384 with
               | (s,w) ->
                   let uu____6391 = signedness s  in
                   let uu____6392 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6391 uu____6392)
            sign_width_opt
           in
        let uu____6393 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6393 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6395 = FStar_Range.string_of_range r  in str uu____6395
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6397 = p_quident lid  in
        let uu____6398 =
          let uu____6399 =
            let uu____6400 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6400  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6399  in
        FStar_Pprint.op_Hat_Hat uu____6397 uu____6398

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6402 = str "u#"  in
    let uu____6403 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6402 uu____6403

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6405;_},u1::u2::[])
        ->
        let uu____6410 =
          let uu____6411 = p_universeFrom u1  in
          let uu____6412 =
            let uu____6413 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6413  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6411 uu____6412  in
        FStar_Pprint.group uu____6410
    | FStar_Parser_AST.App uu____6414 ->
        let uu____6421 = head_and_args u  in
        (match uu____6421 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6447 =
                    let uu____6448 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6449 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6457  ->
                           match uu____6457 with
                           | (u1,uu____6463) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6448 uu____6449  in
                  FStar_Pprint.group uu____6447
              | uu____6464 ->
                  let uu____6465 =
                    let uu____6466 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6466
                     in
                  failwith uu____6465))
    | uu____6467 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6491 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6491
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6492;_},uu____6493::uu____6494::[])
        ->
        let uu____6497 = p_universeFrom u  in
        soft_parens_with_nesting uu____6497
    | FStar_Parser_AST.App uu____6498 ->
        let uu____6505 = p_universeFrom u  in
        soft_parens_with_nesting uu____6505
    | uu____6506 ->
        let uu____6507 =
          let uu____6508 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6508
           in
        failwith uu____6507

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
       | FStar_Parser_AST.Module (uu____6548,decls) ->
           let uu____6554 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6554
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6563,decls,uu____6565) ->
           let uu____6570 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6570
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6621  ->
         match uu____6621 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6661,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6667,decls,uu____6669) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6714 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6727;
                 FStar_Parser_AST.doc = uu____6728;
                 FStar_Parser_AST.quals = uu____6729;
                 FStar_Parser_AST.attrs = uu____6730;_}::uu____6731 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6737 =
                   let uu____6740 =
                     let uu____6743 = FStar_List.tl ds  in d :: uu____6743
                      in
                   d0 :: uu____6740  in
                 (uu____6737, (d0.FStar_Parser_AST.drange))
             | uu____6748 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6714 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6806 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6806 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6902 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6902, comments1))))))
  