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
    let uu____3339 =
      let uu____3340 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3341 =
        let uu____3342 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3343 =
          let uu____3344 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3345 =
            let uu____3346 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3346
             in
          FStar_Pprint.op_Hat_Hat uu____3344 uu____3345  in
        FStar_Pprint.op_Hat_Hat uu____3342 uu____3343  in
      FStar_Pprint.op_Hat_Hat uu____3340 uu____3341  in
    FStar_Pprint.group uu____3339

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3349 =
      let uu____3350 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3350  in
    let uu____3351 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3349 FStar_Pprint.space uu____3351
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3352  ->
    match uu____3352 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3386 =
                match uu____3386 with
                | (kwd,arg) ->
                    let uu____3393 = str "@"  in
                    let uu____3394 =
                      let uu____3395 = str kwd  in
                      let uu____3396 =
                        let uu____3397 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3397
                         in
                      FStar_Pprint.op_Hat_Hat uu____3395 uu____3396  in
                    FStar_Pprint.op_Hat_Hat uu____3393 uu____3394
                 in
              let uu____3398 =
                let uu____3399 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3399 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3398
           in
        let uu____3404 =
          let uu____3405 =
            let uu____3406 =
              let uu____3407 =
                let uu____3408 = str doc1  in
                let uu____3409 =
                  let uu____3410 =
                    let uu____3411 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3411  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3410  in
                FStar_Pprint.op_Hat_Hat uu____3408 uu____3409  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3407  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3406  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3405  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3404

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3415 =
          let uu____3416 = str "val"  in
          let uu____3417 =
            let uu____3418 =
              let uu____3419 = p_lident lid  in
              let uu____3420 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3419 uu____3420  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3418  in
          FStar_Pprint.op_Hat_Hat uu____3416 uu____3417  in
        let uu____3421 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3415 uu____3421
    | FStar_Parser_AST.TopLevelLet (uu____3422,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3447 =
               let uu____3448 = str "let"  in
               let uu____3449 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3448 uu____3449  in
             FStar_Pprint.group uu____3447) lbs
    | uu____3450 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3453 =
          let uu____3454 = str "open"  in
          let uu____3455 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3454 uu____3455  in
        FStar_Pprint.group uu____3453
    | FStar_Parser_AST.Include uid ->
        let uu____3457 =
          let uu____3458 = str "include"  in
          let uu____3459 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3458 uu____3459  in
        FStar_Pprint.group uu____3457
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3462 =
          let uu____3463 = str "module"  in
          let uu____3464 =
            let uu____3465 =
              let uu____3466 = p_uident uid1  in
              let uu____3467 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3466 uu____3467  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3465  in
          FStar_Pprint.op_Hat_Hat uu____3463 uu____3464  in
        let uu____3468 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3462 uu____3468
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3470 =
          let uu____3471 = str "module"  in
          let uu____3472 =
            let uu____3473 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3473  in
          FStar_Pprint.op_Hat_Hat uu____3471 uu____3472  in
        FStar_Pprint.group uu____3470
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3506 = str "effect"  in
          let uu____3507 =
            let uu____3508 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3508  in
          FStar_Pprint.op_Hat_Hat uu____3506 uu____3507  in
        let uu____3509 =
          let uu____3510 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3510 FStar_Pprint.equals
           in
        let uu____3511 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3509 uu____3511
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3529 = str "type"  in
        let uu____3530 = str "and"  in
        precede_break_separate_map uu____3529 uu____3530 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3552 = str "let"  in
          let uu____3553 =
            let uu____3554 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3554 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3552 uu____3553  in
        let uu____3555 =
          let uu____3556 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3556 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3555 p_letbinding lbs
          (fun uu____3564  ->
             match uu____3564 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3573 =
          let uu____3574 = str "val"  in
          let uu____3575 =
            let uu____3576 =
              let uu____3577 = p_lident lid  in
              let uu____3578 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3577 uu____3578  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3576  in
          FStar_Pprint.op_Hat_Hat uu____3574 uu____3575  in
        let uu____3579 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3573 uu____3579
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3583 =
            let uu____3584 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3584 FStar_Util.is_upper  in
          if uu____3583
          then FStar_Pprint.empty
          else
            (let uu____3586 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3586 FStar_Pprint.space)
           in
        let uu____3587 =
          let uu____3588 =
            let uu____3589 = p_ident id1  in
            let uu____3590 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3589 uu____3590  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3588  in
        let uu____3591 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3587 uu____3591
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3598 = str "exception"  in
        let uu____3599 =
          let uu____3600 =
            let uu____3601 = p_uident uid  in
            let uu____3602 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3606 =
                     let uu____3607 = str "of"  in
                     let uu____3608 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3607 uu____3608  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3606) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3601 uu____3602  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3600  in
        FStar_Pprint.op_Hat_Hat uu____3598 uu____3599
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3610 = str "new_effect"  in
        let uu____3611 =
          let uu____3612 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3612  in
        FStar_Pprint.op_Hat_Hat uu____3610 uu____3611
    | FStar_Parser_AST.SubEffect se ->
        let uu____3614 = str "sub_effect"  in
        let uu____3615 =
          let uu____3616 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3616  in
        FStar_Pprint.op_Hat_Hat uu____3614 uu____3615
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3619 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3619 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3620 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3621) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3638  ->
    match uu___54_3638 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3640 = str "#set-options"  in
        let uu____3641 =
          let uu____3642 =
            let uu____3643 = str s  in FStar_Pprint.dquotes uu____3643  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3642  in
        FStar_Pprint.op_Hat_Hat uu____3640 uu____3641
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3647 = str "#reset-options"  in
        let uu____3648 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3652 =
                 let uu____3653 = str s  in FStar_Pprint.dquotes uu____3653
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3652) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3647 uu____3648
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
  fun uu____3677  ->
    match uu____3677 with
    | (typedecl,fsdoc_opt) ->
        let uu____3690 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3691 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3690 uu____3691

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3692  ->
    match uu___55_3692 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3707 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3723 =
          let uu____3724 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3724  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3771 =
          match uu____3771 with
          | (lid1,t,doc_opt) ->
              let uu____3787 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3787
           in
        let p_fields uu____3801 =
          let uu____3802 =
            let uu____3803 =
              let uu____3804 =
                let uu____3805 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3805 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3804  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3803  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3802  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3869 =
          match uu____3869 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3895 =
                  let uu____3896 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3896  in
                FStar_Range.extend_to_end_of_line uu____3895  in
              let p_constructorBranch decl =
                let uu____3929 =
                  let uu____3930 =
                    let uu____3931 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3931  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3930  in
                FStar_Pprint.group uu____3929  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3951 =
          let uu____3952 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3952  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3967  ->
             let uu____3968 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3968)

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
            let uu____3983 = p_ident lid  in
            let uu____3984 =
              let uu____3985 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3985  in
            FStar_Pprint.op_Hat_Hat uu____3983 uu____3984
          else
            (let binders_doc =
               let uu____3988 = p_typars bs  in
               let uu____3989 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3993 =
                        let uu____3994 =
                          let uu____3995 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3995
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3994
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3993) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3988 uu____3989  in
             let uu____3996 = p_ident lid  in
             let uu____3997 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3996 binders_doc uu____3997)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____3999  ->
      match uu____3999 with
      | (lid,t,doc_opt) ->
          let uu____4015 =
            let uu____4016 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4017 =
              let uu____4018 = p_lident lid  in
              let uu____4019 =
                let uu____4020 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4020  in
              FStar_Pprint.op_Hat_Hat uu____4018 uu____4019  in
            FStar_Pprint.op_Hat_Hat uu____4016 uu____4017  in
          FStar_Pprint.group uu____4015

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4021  ->
    match uu____4021 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4049 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4050 =
          let uu____4051 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4052 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4057 =
                   let uu____4058 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4058  in
                 let uu____4059 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4057 uu____4059) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4051 uu____4052  in
        FStar_Pprint.op_Hat_Hat uu____4049 uu____4050

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4060  ->
    match uu____4060 with
    | (pat,uu____4066) ->
        let uu____4067 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4078 =
                let uu____4079 =
                  let uu____4080 =
                    let uu____4081 =
                      let uu____4082 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4082
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4081  in
                  FStar_Pprint.group uu____4080  in
                FStar_Pprint.op_Hat_Hat break1 uu____4079  in
              (pat1, uu____4078)
          | uu____4083 -> (pat, FStar_Pprint.empty)  in
        (match uu____4067 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4087);
                     FStar_Parser_AST.prange = uu____4088;_},pats)
                  ->
                  let uu____4098 =
                    let uu____4099 = p_lident x  in
                    let uu____4100 =
                      let uu____4101 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4101 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4099 uu____4100  in
                  FStar_Pprint.group uu____4098
              | uu____4102 ->
                  let uu____4103 =
                    let uu____4104 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4104 ascr_doc  in
                  FStar_Pprint.group uu____4103))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4105  ->
    match uu____4105 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4113 =
          let uu____4114 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4114  in
        let uu____4115 = p_term false false e  in
        prefix2 uu____4113 uu____4115

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_4116  ->
    match uu___56_4116 with
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
        let uu____4141 = p_uident uid  in
        let uu____4142 = p_binders true bs  in
        let uu____4143 =
          let uu____4144 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4144  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4141 uu____4142 uu____4143

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
          let uu____4153 =
            let uu____4154 =
              let uu____4155 =
                let uu____4156 = p_uident uid  in
                let uu____4157 = p_binders true bs  in
                let uu____4158 =
                  let uu____4159 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4159  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4156 uu____4157 uu____4158
                 in
              FStar_Pprint.group uu____4155  in
            let uu____4160 =
              let uu____4161 = str "with"  in
              let uu____4162 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4161 uu____4162  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4154 uu____4160  in
          braces_with_nesting uu____4153

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
          let uu____4193 =
            let uu____4194 = p_lident lid  in
            let uu____4195 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4194 uu____4195  in
          let uu____4196 = p_simpleTerm ps false e  in
          prefix2 uu____4193 uu____4196
      | uu____4197 ->
          let uu____4198 =
            let uu____4199 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4199
             in
          failwith uu____4198

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4257 =
        match uu____4257 with
        | (kwd,t) ->
            let uu____4264 =
              let uu____4265 = str kwd  in
              let uu____4266 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4265 uu____4266  in
            let uu____4267 = p_simpleTerm ps false t  in
            prefix2 uu____4264 uu____4267
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4272 =
      let uu____4273 =
        let uu____4274 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4275 =
          let uu____4276 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4276  in
        FStar_Pprint.op_Hat_Hat uu____4274 uu____4275  in
      let uu____4277 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4273 uu____4277  in
    let uu____4278 =
      let uu____4279 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4279  in
    FStar_Pprint.op_Hat_Hat uu____4272 uu____4278

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4280  ->
    match uu___57_4280 with
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
    let uu____4282 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4282

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4283  ->
    match uu___58_4283 with
    | FStar_Parser_AST.Rec  ->
        let uu____4284 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4284
    | FStar_Parser_AST.Mutable  ->
        let uu____4285 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4285
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4286  ->
    match uu___59_4286 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4291 =
          let uu____4292 =
            let uu____4293 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4293  in
          FStar_Pprint.separate_map uu____4292 p_tuplePattern pats  in
        FStar_Pprint.group uu____4291
    | uu____4294 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4301 =
          let uu____4302 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4302 p_constructorPattern pats  in
        FStar_Pprint.group uu____4301
    | uu____4303 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4306;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4311 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4312 = p_constructorPattern hd1  in
        let uu____4313 = p_constructorPattern tl1  in
        infix0 uu____4311 uu____4312 uu____4313
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4315;_},pats)
        ->
        let uu____4321 = p_quident uid  in
        let uu____4322 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4321 uu____4322
    | uu____4323 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4331;
               FStar_Parser_AST.blevel = uu____4332;
               FStar_Parser_AST.aqual = uu____4333;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4339 =
               let uu____4340 = p_ident lid  in
               p_refinement aqual uu____4340 t1 phi  in
             soft_parens_with_nesting uu____4339
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4342;
               FStar_Parser_AST.blevel = uu____4343;
               FStar_Parser_AST.aqual = uu____4344;_},phi))
             ->
             let uu____4346 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4346
         | uu____4347 ->
             let uu____4352 =
               let uu____4353 = p_tuplePattern pat  in
               let uu____4354 =
                 let uu____4355 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4356 =
                   let uu____4357 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4357  in
                 FStar_Pprint.op_Hat_Hat uu____4355 uu____4356  in
               FStar_Pprint.op_Hat_Hat uu____4353 uu____4354  in
             soft_parens_with_nesting uu____4352)
    | FStar_Parser_AST.PatList pats ->
        let uu____4361 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4361 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4376 =
          match uu____4376 with
          | (lid,pat) ->
              let uu____4383 = p_qlident lid  in
              let uu____4384 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4383 uu____4384
           in
        let uu____4385 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4385
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4395 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4396 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4397 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4395 uu____4396 uu____4397
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4408 =
          let uu____4409 =
            let uu____4410 = str (FStar_Ident.text_of_id op)  in
            let uu____4411 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4410 uu____4411  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4409  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4408
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4419 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4420 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4419 uu____4420
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4422 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4425;
           FStar_Parser_AST.prange = uu____4426;_},uu____4427)
        ->
        let uu____4432 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4432
    | FStar_Parser_AST.PatTuple (uu____4433,false ) ->
        let uu____4438 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4438
    | uu____4439 ->
        let uu____4440 =
          let uu____4441 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4441  in
        failwith uu____4440

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4445 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4446 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4445 uu____4446
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4453;
                   FStar_Parser_AST.blevel = uu____4454;
                   FStar_Parser_AST.aqual = uu____4455;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4457 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4457 t1 phi
            | uu____4458 ->
                let uu____4459 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4460 =
                  let uu____4461 = p_lident lid  in
                  let uu____4462 =
                    let uu____4463 =
                      let uu____4464 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4465 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4464 uu____4465  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4463  in
                  FStar_Pprint.op_Hat_Hat uu____4461 uu____4462  in
                FStar_Pprint.op_Hat_Hat uu____4459 uu____4460
             in
          if is_atomic
          then
            let uu____4466 =
              let uu____4467 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4467  in
            FStar_Pprint.group uu____4466
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4469 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4476;
                  FStar_Parser_AST.blevel = uu____4477;
                  FStar_Parser_AST.aqual = uu____4478;_},phi)
               ->
               if is_atomic
               then
                 let uu____4480 =
                   let uu____4481 =
                     let uu____4482 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4482 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4481  in
                 FStar_Pprint.group uu____4480
               else
                 (let uu____4484 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4484)
           | uu____4485 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4493 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4494 =
            let uu____4495 =
              let uu____4496 =
                let uu____4497 = p_appTerm t  in
                let uu____4498 =
                  let uu____4499 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4499  in
                FStar_Pprint.op_Hat_Hat uu____4497 uu____4498  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4496  in
            FStar_Pprint.op_Hat_Hat binder uu____4495  in
          FStar_Pprint.op_Hat_Hat uu____4493 uu____4494

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
            let uu____4522 =
              let uu____4523 =
                let uu____4524 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4524 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4523  in
            let uu____4525 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4522 uu____4525
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4529 =
              let uu____4530 =
                let uu____4531 =
                  let uu____4532 = p_lident x  in
                  let uu____4533 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4532 uu____4533  in
                let uu____4534 =
                  let uu____4535 = p_noSeqTerm true false e1  in
                  let uu____4536 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4535 uu____4536  in
                op_Hat_Slash_Plus_Hat uu____4531 uu____4534  in
              FStar_Pprint.group uu____4530  in
            let uu____4537 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4529 uu____4537
        | uu____4538 ->
            let uu____4539 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4539

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
            let uu____4550 =
              let uu____4551 = p_tmIff e1  in
              let uu____4552 =
                let uu____4553 =
                  let uu____4554 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4554
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4553  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4551 uu____4552  in
            FStar_Pprint.group uu____4550
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4560 =
              let uu____4561 = p_tmIff e1  in
              let uu____4562 =
                let uu____4563 =
                  let uu____4564 =
                    let uu____4565 = p_typ false false t  in
                    let uu____4566 =
                      let uu____4567 = str "by"  in
                      let uu____4568 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4567 uu____4568  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4565 uu____4566  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4564
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4563  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4561 uu____4562  in
            FStar_Pprint.group uu____4560
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4569;_},e1::e2::e3::[])
            ->
            let uu____4575 =
              let uu____4576 =
                let uu____4577 =
                  let uu____4578 = p_atomicTermNotQUident e1  in
                  let uu____4579 =
                    let uu____4580 =
                      let uu____4581 =
                        let uu____4582 = p_term false false e2  in
                        soft_parens_with_nesting uu____4582  in
                      let uu____4583 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4581 uu____4583  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4580  in
                  FStar_Pprint.op_Hat_Hat uu____4578 uu____4579  in
                FStar_Pprint.group uu____4577  in
              let uu____4584 =
                let uu____4585 = p_noSeqTerm ps pb e3  in jump2 uu____4585
                 in
              FStar_Pprint.op_Hat_Hat uu____4576 uu____4584  in
            FStar_Pprint.group uu____4575
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4586;_},e1::e2::e3::[])
            ->
            let uu____4592 =
              let uu____4593 =
                let uu____4594 =
                  let uu____4595 = p_atomicTermNotQUident e1  in
                  let uu____4596 =
                    let uu____4597 =
                      let uu____4598 =
                        let uu____4599 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4599  in
                      let uu____4600 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4598 uu____4600  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4597  in
                  FStar_Pprint.op_Hat_Hat uu____4595 uu____4596  in
                FStar_Pprint.group uu____4594  in
              let uu____4601 =
                let uu____4602 = p_noSeqTerm ps pb e3  in jump2 uu____4602
                 in
              FStar_Pprint.op_Hat_Hat uu____4593 uu____4601  in
            FStar_Pprint.group uu____4592
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4612 =
              let uu____4613 = str "requires"  in
              let uu____4614 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4613 uu____4614  in
            FStar_Pprint.group uu____4612
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4624 =
              let uu____4625 = str "ensures"  in
              let uu____4626 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4625 uu____4626  in
            FStar_Pprint.group uu____4624
        | FStar_Parser_AST.Attributes es ->
            let uu____4630 =
              let uu____4631 = str "attributes"  in
              let uu____4632 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4631 uu____4632  in
            FStar_Pprint.group uu____4630
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4636 =
                let uu____4637 =
                  let uu____4638 = str "if"  in
                  let uu____4639 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4638 uu____4639  in
                let uu____4640 =
                  let uu____4641 = str "then"  in
                  let uu____4642 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4641 uu____4642  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4637 uu____4640  in
              FStar_Pprint.group uu____4636
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4645,uu____4646,e31) when
                     is_unit e31 ->
                     let uu____4648 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4648
                 | uu____4649 -> p_noSeqTerm false false e2  in
               let uu____4650 =
                 let uu____4651 =
                   let uu____4652 = str "if"  in
                   let uu____4653 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4652 uu____4653  in
                 let uu____4654 =
                   let uu____4655 =
                     let uu____4656 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4656 e2_doc  in
                   let uu____4657 =
                     let uu____4658 = str "else"  in
                     let uu____4659 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4658 uu____4659  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4655 uu____4657  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4651 uu____4654  in
               FStar_Pprint.group uu____4650)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4682 =
              let uu____4683 =
                let uu____4684 =
                  let uu____4685 = str "try"  in
                  let uu____4686 = p_noSeqTerm false false e1  in
                  prefix2 uu____4685 uu____4686  in
                let uu____4687 =
                  let uu____4688 = str "with"  in
                  let uu____4689 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4688 uu____4689  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4684 uu____4687  in
              FStar_Pprint.group uu____4683  in
            let uu____4698 = paren_if (ps || pb)  in uu____4698 uu____4682
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4723 =
              let uu____4724 =
                let uu____4725 =
                  let uu____4726 = str "match"  in
                  let uu____4727 = p_noSeqTerm false false e1  in
                  let uu____4728 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4726 uu____4727 uu____4728
                   in
                let uu____4729 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4725 uu____4729  in
              FStar_Pprint.group uu____4724  in
            let uu____4738 = paren_if (ps || pb)  in uu____4738 uu____4723
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4743 =
              let uu____4744 =
                let uu____4745 =
                  let uu____4746 = str "let open"  in
                  let uu____4747 = p_quident uid  in
                  let uu____4748 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4746 uu____4747 uu____4748
                   in
                let uu____4749 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4745 uu____4749  in
              FStar_Pprint.group uu____4744  in
            let uu____4750 = paren_if ps  in uu____4750 uu____4743
        | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
            let let_first =
              let uu____4815 = p_attrs_opt a0  in
              let uu____4816 =
                let uu____4817 =
                  let uu____4818 = str "let"  in
                  let uu____4819 =
                    let uu____4820 = p_letqualifier q  in
                    let uu____4821 = p_letbinding lb0  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4820 uu____4821  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4818 uu____4819  in
                FStar_Pprint.group uu____4817  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4815 uu____4816  in
            let let_rest =
              match attr_letbindings with
              | [] -> FStar_Pprint.empty
              | uu____4835 ->
                  let uu____4850 =
                    precede_break_separate_map FStar_Pprint.empty
                      FStar_Pprint.empty p_attr_letbinding attr_letbindings
                     in
                  FStar_Pprint.group uu____4850
               in
            let uu____4863 =
              let uu____4864 =
                let uu____4865 =
                  let uu____4866 = str "in"  in
                  let uu____4867 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4866 uu____4867  in
                FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4865  in
              FStar_Pprint.op_Hat_Slash_Hat let_first uu____4864  in
            let uu____4868 = paren_if ps  in uu____4868 uu____4863
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4873;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____4876;
                                                             FStar_Parser_AST.level
                                                               = uu____4877;_})
            when matches_var maybe_x x ->
            let uu____4904 =
              let uu____4905 =
                let uu____4906 = str "function"  in
                let uu____4907 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4906 uu____4907  in
              FStar_Pprint.group uu____4905  in
            let uu____4916 = paren_if (ps || pb)  in uu____4916 uu____4904
        | FStar_Parser_AST.Quote (e1,true ) ->
            let uu____4920 =
              let uu____4921 = str "quote"  in
              let uu____4922 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4921 uu____4922  in
            FStar_Pprint.group uu____4920
        | FStar_Parser_AST.Quote (e1,false ) ->
            let uu____4924 =
              let uu____4925 = str "`"  in
              let uu____4926 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4925 uu____4926  in
            FStar_Pprint.group uu____4924
        | uu____4927 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_4928  ->
    match uu___60_4928 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4940 =
          let uu____4941 = str "[@"  in
          let uu____4942 =
            let uu____4943 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____4944 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4943 uu____4944  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4941 uu____4942  in
        FStar_Pprint.group uu____4940

and (p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4945  ->
    match uu____4945 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4974 =
          let uu____4975 = p_attrs_opt a  in
          let uu____4976 =
            let uu____4977 =
              let uu____4978 = str "and "  in
              let uu____4979 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4978 uu____4979  in
            FStar_Pprint.group uu____4977  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4975 uu____4976  in
        let uu____4980 = p_term false false e  in
        prefix2 uu____4974 uu____4980

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
            let uu____5002 =
              let uu____5003 =
                let uu____5004 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5004 FStar_Pprint.space  in
              let uu____5005 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5003 uu____5005 FStar_Pprint.dot
               in
            let uu____5006 =
              let uu____5007 = p_trigger trigger  in
              let uu____5008 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5007 uu____5008  in
            prefix2 uu____5002 uu____5006
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5024 =
              let uu____5025 =
                let uu____5026 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5026 FStar_Pprint.space  in
              let uu____5027 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5025 uu____5027 FStar_Pprint.dot
               in
            let uu____5028 =
              let uu____5029 = p_trigger trigger  in
              let uu____5030 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5029 uu____5030  in
            prefix2 uu____5024 uu____5028
        | uu____5031 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5033 -> str "forall"
    | FStar_Parser_AST.QExists uu____5046 -> str "exists"
    | uu____5059 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_5060  ->
    match uu___61_5060 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5072 =
          let uu____5073 =
            let uu____5074 = str "pattern"  in
            let uu____5075 =
              let uu____5076 =
                let uu____5077 = p_disjunctivePats pats  in jump2 uu____5077
                 in
              let uu____5078 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5076 uu____5078  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5074 uu____5075  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5073  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5072

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5084 = str "\\/"  in
    FStar_Pprint.separate_map uu____5084 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5090 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5090

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5100 =
              let uu____5101 =
                let uu____5102 = str "fun"  in
                let uu____5103 =
                  let uu____5104 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5104
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5102 uu____5103  in
              let uu____5105 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5101 uu____5105  in
            let uu____5106 = paren_if ps  in uu____5106 uu____5100
        | uu____5109 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5113  ->
      match uu____5113 with
      | (pat,when_opt,e) ->
          let uu____5129 =
            let uu____5130 =
              let uu____5131 =
                let uu____5132 =
                  let uu____5133 =
                    let uu____5134 = p_disjunctivePattern pat  in
                    let uu____5135 =
                      let uu____5136 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5136 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5134 uu____5135  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5133  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5132  in
              FStar_Pprint.group uu____5131  in
            let uu____5137 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5130 uu____5137  in
          FStar_Pprint.group uu____5129

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_5138  ->
    match uu___62_5138 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5142 = str "when"  in
        let uu____5143 =
          let uu____5144 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5144 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5142 uu____5143

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5146;_},e1::e2::[])
        ->
        let uu____5151 = str "<==>"  in
        let uu____5152 = p_tmImplies e1  in
        let uu____5153 = p_tmIff e2  in
        infix0 uu____5151 uu____5152 uu____5153
    | uu____5154 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5156;_},e1::e2::[])
        ->
        let uu____5161 = str "==>"  in
        let uu____5162 = p_tmArrow p_tmFormula e1  in
        let uu____5163 = p_tmImplies e2  in
        infix0 uu____5161 uu____5162 uu____5163
    | uu____5164 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5175 =
            let uu____5176 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5181 = p_binder false b  in
                   let uu____5182 =
                     let uu____5183 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5183
                      in
                   FStar_Pprint.op_Hat_Hat uu____5181 uu____5182) bs
               in
            let uu____5184 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5176 uu____5184  in
          FStar_Pprint.group uu____5175
      | uu____5185 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5187;_},e1::e2::[])
        ->
        let uu____5192 = str "\\/"  in
        let uu____5193 = p_tmFormula e1  in
        let uu____5194 = p_tmConjunction e2  in
        infix0 uu____5192 uu____5193 uu____5194
    | uu____5195 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5197;_},e1::e2::[])
        ->
        let uu____5202 = str "/\\"  in
        let uu____5203 = p_tmConjunction e1  in
        let uu____5204 = p_tmTuple e2  in
        infix0 uu____5202 uu____5203 uu____5204
    | uu____5205 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5222 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5222
          (fun uu____5230  ->
             match uu____5230 with | (e1,uu____5236) -> p_tmEq e1) args
    | uu____5237 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5242 =
             let uu____5243 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5243  in
           FStar_Pprint.group uu____5242)

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
            let uu____5306 = levels op1  in
            (match uu____5306 with
             | (left1,mine,right1) ->
                 let uu____5316 =
                   let uu____5317 = FStar_All.pipe_left str op1  in
                   let uu____5318 = p_tmEqWith' p_X left1 e1  in
                   let uu____5319 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5317 uu____5318 uu____5319  in
                 paren_if_gt curr mine uu____5316)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5320;_},e1::e2::[])
            ->
            let uu____5325 =
              let uu____5326 = p_tmEqWith p_X e1  in
              let uu____5327 =
                let uu____5328 =
                  let uu____5329 =
                    let uu____5330 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5330  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5329  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5328  in
              FStar_Pprint.op_Hat_Hat uu____5326 uu____5327  in
            FStar_Pprint.group uu____5325
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5331;_},e1::[])
            ->
            let uu____5335 = levels "-"  in
            (match uu____5335 with
             | (left1,mine,right1) ->
                 let uu____5345 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5345)
        | uu____5346 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5417)::(e2,uu____5419)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5439 = is_list e  in Prims.op_Negation uu____5439)
            ->
            let op = "::"  in
            let uu____5441 = levels op  in
            (match uu____5441 with
             | (left1,mine,right1) ->
                 let uu____5451 =
                   let uu____5452 = str op  in
                   let uu____5453 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5454 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5452 uu____5453 uu____5454  in
                 paren_if_gt curr mine uu____5451)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5462 = levels op  in
            (match uu____5462 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5476 = p_binder false b  in
                   let uu____5477 =
                     let uu____5478 =
                       let uu____5479 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5479 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5478
                      in
                   FStar_Pprint.op_Hat_Hat uu____5476 uu____5477  in
                 let uu____5480 =
                   let uu____5481 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5482 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5481 uu____5482  in
                 paren_if_gt curr mine uu____5480)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5489 = levels op1  in
            (match uu____5489 with
             | (left1,mine,right1) ->
                 let uu____5499 =
                   let uu____5500 = str op1  in
                   let uu____5501 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5502 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5500 uu____5501 uu____5502  in
                 paren_if_gt curr mine uu____5499)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5521 =
              let uu____5522 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5523 =
                let uu____5524 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5524 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5522 uu____5523  in
            braces_with_nesting uu____5521
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5529;_},e1::[])
            ->
            let uu____5533 =
              let uu____5534 = str "~"  in
              let uu____5535 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5534 uu____5535  in
            FStar_Pprint.group uu____5533
        | uu____5536 -> p_X e

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
        let uu____5543 =
          let uu____5544 = p_lidentOrUnderscore lid  in
          let uu____5545 =
            let uu____5546 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5546  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5544 uu____5545  in
        FStar_Pprint.group uu____5543
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5549 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5551 = p_appTerm e  in
    let uu____5552 =
      let uu____5553 =
        let uu____5554 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5554 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5553  in
    FStar_Pprint.op_Hat_Hat uu____5551 uu____5552

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5559 =
            let uu____5560 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5560 t phi  in
          soft_parens_with_nesting uu____5559
      | FStar_Parser_AST.TAnnotated uu____5561 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5566 ->
          let uu____5567 =
            let uu____5568 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5568
             in
          failwith uu____5567
      | FStar_Parser_AST.TVariable uu____5569 ->
          let uu____5570 =
            let uu____5571 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5571
             in
          failwith uu____5570
      | FStar_Parser_AST.NoName uu____5572 ->
          let uu____5573 =
            let uu____5574 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5574
             in
          failwith uu____5573

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5576  ->
      match uu____5576 with
      | (lid,e) ->
          let uu____5583 =
            let uu____5584 = p_qlident lid  in
            let uu____5585 =
              let uu____5586 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5586
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5584 uu____5585  in
          FStar_Pprint.group uu____5583

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5588 when is_general_application e ->
        let uu____5595 = head_and_args e  in
        (match uu____5595 with
         | (head1,args) ->
             let uu____5620 =
               let uu____5631 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5631
               then
                 let uu____5661 =
                   FStar_Util.take
                     (fun uu____5685  ->
                        match uu____5685 with
                        | (uu____5690,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5661 with
                 | (fs_typ_args,args1) ->
                     let uu____5728 =
                       let uu____5729 = p_indexingTerm head1  in
                       let uu____5730 =
                         let uu____5731 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5731 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5729 uu____5730  in
                     (uu____5728, args1)
               else
                 (let uu____5743 = p_indexingTerm head1  in
                  (uu____5743, args))
                in
             (match uu____5620 with
              | (head_doc,args1) ->
                  let uu____5764 =
                    let uu____5765 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5765 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5764))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5785 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5785)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5803 =
               let uu____5804 = p_quident lid  in
               let uu____5805 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5804 uu____5805  in
             FStar_Pprint.group uu____5803
         | hd1::tl1 ->
             let uu____5822 =
               let uu____5823 =
                 let uu____5824 =
                   let uu____5825 = p_quident lid  in
                   let uu____5826 = p_argTerm hd1  in
                   prefix2 uu____5825 uu____5826  in
                 FStar_Pprint.group uu____5824  in
               let uu____5827 =
                 let uu____5828 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5828  in
               FStar_Pprint.op_Hat_Hat uu____5823 uu____5827  in
             FStar_Pprint.group uu____5822)
    | uu____5833 -> p_indexingTerm e

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
         (let uu____5842 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5842 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5844 = str "#"  in
        let uu____5845 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5844 uu____5845
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5847  ->
    match uu____5847 with | (e,uu____5853) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5858;_},e1::e2::[])
          ->
          let uu____5863 =
            let uu____5864 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5865 =
              let uu____5866 =
                let uu____5867 = p_term false false e2  in
                soft_parens_with_nesting uu____5867  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5866  in
            FStar_Pprint.op_Hat_Hat uu____5864 uu____5865  in
          FStar_Pprint.group uu____5863
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5868;_},e1::e2::[])
          ->
          let uu____5873 =
            let uu____5874 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5875 =
              let uu____5876 =
                let uu____5877 = p_term false false e2  in
                soft_brackets_with_nesting uu____5877  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5876  in
            FStar_Pprint.op_Hat_Hat uu____5874 uu____5875  in
          FStar_Pprint.group uu____5873
      | uu____5878 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5883 = p_quident lid  in
        let uu____5884 =
          let uu____5885 =
            let uu____5886 = p_term false false e1  in
            soft_parens_with_nesting uu____5886  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5885  in
        FStar_Pprint.op_Hat_Hat uu____5883 uu____5884
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5892 = str (FStar_Ident.text_of_id op)  in
        let uu____5893 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5892 uu____5893
    | uu____5894 -> p_atomicTermNotQUident e

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
         | uu____5901 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5908 = str (FStar_Ident.text_of_id op)  in
        let uu____5909 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5908 uu____5909
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5913 =
          let uu____5914 =
            let uu____5915 = str (FStar_Ident.text_of_id op)  in
            let uu____5916 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5915 uu____5916  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5914  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5913
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5931 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5932 =
          let uu____5933 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5934 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5933 p_tmEq uu____5934  in
        let uu____5941 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5931 uu____5932 uu____5941
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5944 =
          let uu____5945 = p_atomicTermNotQUident e1  in
          let uu____5946 =
            let uu____5947 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5947  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5945 uu____5946
           in
        FStar_Pprint.group uu____5944
    | uu____5948 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5953 = p_quident constr_lid  in
        let uu____5954 =
          let uu____5955 =
            let uu____5956 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5956  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5955  in
        FStar_Pprint.op_Hat_Hat uu____5953 uu____5954
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5958 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5958 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5960 = p_term false false e1  in
        soft_parens_with_nesting uu____5960
    | uu____5961 when is_array e ->
        let es = extract_from_list e  in
        let uu____5965 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5966 =
          let uu____5967 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____5967
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____5970 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5965 uu____5966 uu____5970
    | uu____5971 when is_list e ->
        let uu____5972 =
          let uu____5973 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5974 = extract_from_list e  in
          separate_map_or_flow_last uu____5973
            (fun ps  -> p_noSeqTerm ps false) uu____5974
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5972 FStar_Pprint.rbracket
    | uu____5979 when is_lex_list e ->
        let uu____5980 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5981 =
          let uu____5982 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5983 = extract_from_list e  in
          separate_map_or_flow_last uu____5982
            (fun ps  -> p_noSeqTerm ps false) uu____5983
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5980 uu____5981 FStar_Pprint.rbracket
    | uu____5988 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5992 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5993 =
          let uu____5994 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5994 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5992 uu____5993 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5998 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5999 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5998 uu____5999
    | FStar_Parser_AST.Op (op,args) when
        let uu____6006 = handleable_op op args  in
        Prims.op_Negation uu____6006 ->
        let uu____6007 =
          let uu____6008 =
            let uu____6009 =
              let uu____6010 =
                let uu____6011 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6011
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6010  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6009  in
          Prims.strcat "Operation " uu____6008  in
        failwith uu____6007
    | FStar_Parser_AST.Uvar uu____6012 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6013 = p_term false false e  in
        soft_parens_with_nesting uu____6013
    | FStar_Parser_AST.Const uu____6014 ->
        let uu____6015 = p_term false false e  in
        soft_parens_with_nesting uu____6015
    | FStar_Parser_AST.Op uu____6016 ->
        let uu____6023 = p_term false false e  in
        soft_parens_with_nesting uu____6023
    | FStar_Parser_AST.Tvar uu____6024 ->
        let uu____6025 = p_term false false e  in
        soft_parens_with_nesting uu____6025
    | FStar_Parser_AST.Var uu____6026 ->
        let uu____6027 = p_term false false e  in
        soft_parens_with_nesting uu____6027
    | FStar_Parser_AST.Name uu____6028 ->
        let uu____6029 = p_term false false e  in
        soft_parens_with_nesting uu____6029
    | FStar_Parser_AST.Construct uu____6030 ->
        let uu____6041 = p_term false false e  in
        soft_parens_with_nesting uu____6041
    | FStar_Parser_AST.Abs uu____6042 ->
        let uu____6049 = p_term false false e  in
        soft_parens_with_nesting uu____6049
    | FStar_Parser_AST.App uu____6050 ->
        let uu____6057 = p_term false false e  in
        soft_parens_with_nesting uu____6057
    | FStar_Parser_AST.Let uu____6058 ->
        let uu____6079 = p_term false false e  in
        soft_parens_with_nesting uu____6079
    | FStar_Parser_AST.LetOpen uu____6080 ->
        let uu____6085 = p_term false false e  in
        soft_parens_with_nesting uu____6085
    | FStar_Parser_AST.Seq uu____6086 ->
        let uu____6091 = p_term false false e  in
        soft_parens_with_nesting uu____6091
    | FStar_Parser_AST.Bind uu____6092 ->
        let uu____6099 = p_term false false e  in
        soft_parens_with_nesting uu____6099
    | FStar_Parser_AST.If uu____6100 ->
        let uu____6107 = p_term false false e  in
        soft_parens_with_nesting uu____6107
    | FStar_Parser_AST.Match uu____6108 ->
        let uu____6123 = p_term false false e  in
        soft_parens_with_nesting uu____6123
    | FStar_Parser_AST.TryWith uu____6124 ->
        let uu____6139 = p_term false false e  in
        soft_parens_with_nesting uu____6139
    | FStar_Parser_AST.Ascribed uu____6140 ->
        let uu____6149 = p_term false false e  in
        soft_parens_with_nesting uu____6149
    | FStar_Parser_AST.Record uu____6150 ->
        let uu____6163 = p_term false false e  in
        soft_parens_with_nesting uu____6163
    | FStar_Parser_AST.Project uu____6164 ->
        let uu____6169 = p_term false false e  in
        soft_parens_with_nesting uu____6169
    | FStar_Parser_AST.Product uu____6170 ->
        let uu____6177 = p_term false false e  in
        soft_parens_with_nesting uu____6177
    | FStar_Parser_AST.Sum uu____6178 ->
        let uu____6185 = p_term false false e  in
        soft_parens_with_nesting uu____6185
    | FStar_Parser_AST.QForall uu____6186 ->
        let uu____6199 = p_term false false e  in
        soft_parens_with_nesting uu____6199
    | FStar_Parser_AST.QExists uu____6200 ->
        let uu____6213 = p_term false false e  in
        soft_parens_with_nesting uu____6213
    | FStar_Parser_AST.Refine uu____6214 ->
        let uu____6219 = p_term false false e  in
        soft_parens_with_nesting uu____6219
    | FStar_Parser_AST.NamedTyp uu____6220 ->
        let uu____6225 = p_term false false e  in
        soft_parens_with_nesting uu____6225
    | FStar_Parser_AST.Requires uu____6226 ->
        let uu____6233 = p_term false false e  in
        soft_parens_with_nesting uu____6233
    | FStar_Parser_AST.Ensures uu____6234 ->
        let uu____6241 = p_term false false e  in
        soft_parens_with_nesting uu____6241
    | FStar_Parser_AST.Attributes uu____6242 ->
        let uu____6245 = p_term false false e  in
        soft_parens_with_nesting uu____6245
    | FStar_Parser_AST.Quote uu____6246 ->
        let uu____6251 = p_term false false e  in
        soft_parens_with_nesting uu____6251

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_6252  ->
    match uu___65_6252 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6256 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6256
    | FStar_Const.Const_string (s,uu____6258) ->
        let uu____6259 = str s  in FStar_Pprint.dquotes uu____6259
    | FStar_Const.Const_bytearray (bytes,uu____6261) ->
        let uu____6266 =
          let uu____6267 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6267  in
        let uu____6268 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6266 uu____6268
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6286 =
          match uu___63_6286 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6290 =
          match uu___64_6290 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6301  ->
               match uu____6301 with
               | (s,w) ->
                   let uu____6308 = signedness s  in
                   let uu____6309 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6308 uu____6309)
            sign_width_opt
           in
        let uu____6310 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6310 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6312 = FStar_Range.string_of_range r  in str uu____6312
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6314 = p_quident lid  in
        let uu____6315 =
          let uu____6316 =
            let uu____6317 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6317  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6316  in
        FStar_Pprint.op_Hat_Hat uu____6314 uu____6315

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6319 = str "u#"  in
    let uu____6320 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6319 uu____6320

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6322;_},u1::u2::[])
        ->
        let uu____6327 =
          let uu____6328 = p_universeFrom u1  in
          let uu____6329 =
            let uu____6330 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6330  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6328 uu____6329  in
        FStar_Pprint.group uu____6327
    | FStar_Parser_AST.App uu____6331 ->
        let uu____6338 = head_and_args u  in
        (match uu____6338 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6364 =
                    let uu____6365 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6366 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6374  ->
                           match uu____6374 with
                           | (u1,uu____6380) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6365 uu____6366  in
                  FStar_Pprint.group uu____6364
              | uu____6381 ->
                  let uu____6382 =
                    let uu____6383 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6383
                     in
                  failwith uu____6382))
    | uu____6384 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6408 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6408
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6409;_},uu____6410::uu____6411::[])
        ->
        let uu____6414 = p_universeFrom u  in
        soft_parens_with_nesting uu____6414
    | FStar_Parser_AST.App uu____6415 ->
        let uu____6422 = p_universeFrom u  in
        soft_parens_with_nesting uu____6422
    | uu____6423 ->
        let uu____6424 =
          let uu____6425 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6425
           in
        failwith uu____6424

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
       | FStar_Parser_AST.Module (uu____6465,decls) ->
           let uu____6471 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6471
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6480,decls,uu____6482) ->
           let uu____6487 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6487
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6538  ->
         match uu____6538 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6578,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6584,decls,uu____6586) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6631 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6644;
                 FStar_Parser_AST.doc = uu____6645;
                 FStar_Parser_AST.quals = uu____6646;
                 FStar_Parser_AST.attrs = uu____6647;_}::uu____6648 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6654 =
                   let uu____6657 =
                     let uu____6660 = FStar_List.tl ds  in d :: uu____6660
                      in
                   d0 :: uu____6657  in
                 (uu____6654, (d0.FStar_Parser_AST.drange))
             | uu____6665 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6631 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6723 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6723 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6819 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6819, comments1))))))
  