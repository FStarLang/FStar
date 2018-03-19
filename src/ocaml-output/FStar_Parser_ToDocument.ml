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
    | FStar_Parser_AST.Splice t ->
        let uu____3639 = str "%splice"  in
        let uu____3640 =
          let uu____3641 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3641  in
        FStar_Pprint.op_Hat_Hat uu____3639 uu____3640

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___54_3642  ->
    match uu___54_3642 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3644 = str "#set-options"  in
        let uu____3645 =
          let uu____3646 =
            let uu____3647 = str s  in FStar_Pprint.dquotes uu____3647  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3646  in
        FStar_Pprint.op_Hat_Hat uu____3644 uu____3645
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3651 = str "#reset-options"  in
        let uu____3652 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3656 =
                 let uu____3657 = str s  in FStar_Pprint.dquotes uu____3657
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3656) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3651 uu____3652
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
  fun uu____3681  ->
    match uu____3681 with
    | (typedecl,fsdoc_opt) ->
        let uu____3694 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3695 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3694 uu____3695

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___55_3696  ->
    match uu___55_3696 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3711 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3727 =
          let uu____3728 = p_typ false false t  in
          prefix2 FStar_Pprint.equals uu____3728  in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments ps uu____3775 =
          match uu____3775 with
          | (lid1,t,doc_opt) ->
              let uu____3791 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                uu____3791
           in
        let p_fields uu____3805 =
          let uu____3806 =
            let uu____3807 =
              let uu____3808 =
                let uu____3809 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3809 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3808  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3807  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3806  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3873 =
          match uu____3873 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3899 =
                  let uu____3900 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3900  in
                FStar_Range.extend_to_end_of_line uu____3899  in
              let p_constructorBranch decl =
                let uu____3933 =
                  let uu____3934 =
                    let uu____3935 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3935  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3934  in
                FStar_Pprint.group uu____3933  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3955 =
          let uu____3956 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3956  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3971  ->
             let uu____3972 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3972)

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
            let uu____3987 = p_ident lid  in
            let uu____3988 =
              let uu____3989 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3989  in
            FStar_Pprint.op_Hat_Hat uu____3987 uu____3988
          else
            (let binders_doc =
               let uu____3992 = p_typars bs  in
               let uu____3993 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3997 =
                        let uu____3998 =
                          let uu____3999 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3999
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3998
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3997) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3992 uu____3993  in
             let uu____4000 = p_ident lid  in
             let uu____4001 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4000 binders_doc uu____4001)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4003  ->
      match uu____4003 with
      | (lid,t,doc_opt) ->
          let uu____4019 =
            let uu____4020 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4021 =
              let uu____4022 = p_lident lid  in
              let uu____4023 =
                let uu____4024 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4024  in
              FStar_Pprint.op_Hat_Hat uu____4022 uu____4023  in
            FStar_Pprint.op_Hat_Hat uu____4020 uu____4021  in
          FStar_Pprint.group uu____4019

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4025  ->
    match uu____4025 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4053 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4054 =
          let uu____4055 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4056 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4061 =
                   let uu____4062 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4062  in
                 let uu____4063 = p_typ false false t  in
                 op_Hat_Slash_Plus_Hat uu____4061 uu____4063) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4055 uu____4056  in
        FStar_Pprint.op_Hat_Hat uu____4053 uu____4054

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4064  ->
    match uu____4064 with
    | (pat,uu____4070) ->
        let uu____4071 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4090 =
                let uu____4091 =
                  let uu____4092 =
                    let uu____4093 =
                      let uu____4094 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4094
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4093  in
                  FStar_Pprint.group uu____4092  in
                FStar_Pprint.op_Hat_Hat break1 uu____4091  in
              (pat1, uu____4090)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4106 =
                let uu____4107 =
                  let uu____4108 =
                    let uu____4109 =
                      let uu____4110 =
                        let uu____4111 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4111
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4110
                       in
                    FStar_Pprint.group uu____4109  in
                  let uu____4112 =
                    let uu____4113 =
                      let uu____4114 = str "by"  in
                      let uu____4115 =
                        let uu____4116 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4116
                         in
                      FStar_Pprint.op_Hat_Hat uu____4114 uu____4115  in
                    FStar_Pprint.group uu____4113  in
                  FStar_Pprint.op_Hat_Hat uu____4108 uu____4112  in
                FStar_Pprint.op_Hat_Hat break1 uu____4107  in
              (pat1, uu____4106)
          | uu____4117 -> (pat, FStar_Pprint.empty)  in
        (match uu____4071 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4121);
                     FStar_Parser_AST.prange = uu____4122;_},pats)
                  ->
                  let uu____4132 =
                    let uu____4133 = p_lident x  in
                    let uu____4134 =
                      let uu____4135 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4135 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4133 uu____4134  in
                  FStar_Pprint.group uu____4132
              | uu____4136 ->
                  let uu____4137 =
                    let uu____4138 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4138 ascr_doc  in
                  FStar_Pprint.group uu____4137))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4139  ->
    match uu____4139 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4147 =
          let uu____4148 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4148  in
        let uu____4149 = p_term false false e  in
        prefix2 uu____4147 uu____4149

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___56_4150  ->
    match uu___56_4150 with
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
        let uu____4175 = p_uident uid  in
        let uu____4176 = p_binders true bs  in
        let uu____4177 =
          let uu____4178 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4178  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4175 uu____4176 uu____4177

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
          let uu____4187 =
            let uu____4188 =
              let uu____4189 =
                let uu____4190 = p_uident uid  in
                let uu____4191 = p_binders true bs  in
                let uu____4192 =
                  let uu____4193 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4193  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4190 uu____4191 uu____4192
                 in
              FStar_Pprint.group uu____4189  in
            let uu____4194 =
              let uu____4195 = str "with"  in
              let uu____4196 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4195 uu____4196  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4188 uu____4194  in
          braces_with_nesting uu____4187

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
          let uu____4227 =
            let uu____4228 = p_lident lid  in
            let uu____4229 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4228 uu____4229  in
          let uu____4230 = p_simpleTerm ps false e  in
          prefix2 uu____4227 uu____4230
      | uu____4231 ->
          let uu____4232 =
            let uu____4233 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4233
             in
          failwith uu____4232

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4291 =
        match uu____4291 with
        | (kwd,t) ->
            let uu____4298 =
              let uu____4299 = str kwd  in
              let uu____4300 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4299 uu____4300  in
            let uu____4301 = p_simpleTerm ps false t  in
            prefix2 uu____4298 uu____4301
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4306 =
      let uu____4307 =
        let uu____4308 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4309 =
          let uu____4310 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4310  in
        FStar_Pprint.op_Hat_Hat uu____4308 uu____4309  in
      let uu____4311 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4307 uu____4311  in
    let uu____4312 =
      let uu____4313 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4313  in
    FStar_Pprint.op_Hat_Hat uu____4306 uu____4312

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___57_4314  ->
    match uu___57_4314 with
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
    let uu____4316 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4316

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___58_4317  ->
    match uu___58_4317 with
    | FStar_Parser_AST.Rec  ->
        let uu____4318 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4318
    | FStar_Parser_AST.Mutable  ->
        let uu____4319 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4319
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___59_4320  ->
    match uu___59_4320 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4325 =
          let uu____4326 =
            let uu____4327 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4327  in
          FStar_Pprint.separate_map uu____4326 p_tuplePattern pats  in
        FStar_Pprint.group uu____4325
    | uu____4328 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4335 =
          let uu____4336 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4336 p_constructorPattern pats  in
        FStar_Pprint.group uu____4335
    | uu____4337 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4340;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4345 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4346 = p_constructorPattern hd1  in
        let uu____4347 = p_constructorPattern tl1  in
        infix0 uu____4345 uu____4346 uu____4347
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4349;_},pats)
        ->
        let uu____4355 = p_quident uid  in
        let uu____4356 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4355 uu____4356
    | uu____4357 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4373;
               FStar_Parser_AST.blevel = uu____4374;
               FStar_Parser_AST.aqual = uu____4375;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4381 =
               let uu____4382 = p_ident lid  in
               p_refinement aqual uu____4382 t1 phi  in
             soft_parens_with_nesting uu____4381
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4384;
               FStar_Parser_AST.blevel = uu____4385;
               FStar_Parser_AST.aqual = uu____4386;_},phi))
             ->
             let uu____4388 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4388
         | uu____4389 ->
             let uu____4394 =
               let uu____4395 = p_tuplePattern pat  in
               let uu____4396 =
                 let uu____4397 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4398 =
                   let uu____4399 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4399  in
                 FStar_Pprint.op_Hat_Hat uu____4397 uu____4398  in
               FStar_Pprint.op_Hat_Hat uu____4395 uu____4396  in
             soft_parens_with_nesting uu____4394)
    | FStar_Parser_AST.PatList pats ->
        let uu____4403 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4403 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4418 =
          match uu____4418 with
          | (lid,pat) ->
              let uu____4425 = p_qlident lid  in
              let uu____4426 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4425 uu____4426
           in
        let uu____4427 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4427
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4437 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4438 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4439 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4437 uu____4438 uu____4439
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4450 =
          let uu____4451 =
            let uu____4452 = str (FStar_Ident.text_of_id op)  in
            let uu____4453 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4452 uu____4453  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4451  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4450
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4461 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4462 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4461 uu____4462
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4464 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4467;
           FStar_Parser_AST.prange = uu____4468;_},uu____4469)
        ->
        let uu____4474 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4474
    | FStar_Parser_AST.PatTuple (uu____4475,false ) ->
        let uu____4480 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4480
    | uu____4481 ->
        let uu____4482 =
          let uu____4483 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4483  in
        failwith uu____4482

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4487 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4488 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4487 uu____4488
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4495;
                   FStar_Parser_AST.blevel = uu____4496;
                   FStar_Parser_AST.aqual = uu____4497;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4499 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4499 t1 phi
            | uu____4500 ->
                let uu____4501 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4502 =
                  let uu____4503 = p_lident lid  in
                  let uu____4504 =
                    let uu____4505 =
                      let uu____4506 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4507 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4506 uu____4507  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4505  in
                  FStar_Pprint.op_Hat_Hat uu____4503 uu____4504  in
                FStar_Pprint.op_Hat_Hat uu____4501 uu____4502
             in
          if is_atomic
          then
            let uu____4508 =
              let uu____4509 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4509  in
            FStar_Pprint.group uu____4508
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4511 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4518;
                  FStar_Parser_AST.blevel = uu____4519;
                  FStar_Parser_AST.aqual = uu____4520;_},phi)
               ->
               if is_atomic
               then
                 let uu____4522 =
                   let uu____4523 =
                     let uu____4524 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4524 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4523  in
                 FStar_Pprint.group uu____4522
               else
                 (let uu____4526 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4526)
           | uu____4527 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4535 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4536 =
            let uu____4537 =
              let uu____4538 =
                let uu____4539 = p_appTerm t  in
                let uu____4540 =
                  let uu____4541 = p_noSeqTerm false false phi  in
                  soft_braces_with_nesting uu____4541  in
                FStar_Pprint.op_Hat_Hat uu____4539 uu____4540  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4538  in
            FStar_Pprint.op_Hat_Hat binder uu____4537  in
          FStar_Pprint.op_Hat_Hat uu____4535 uu____4536

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
            let uu____4564 =
              let uu____4565 =
                let uu____4566 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4566 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4565  in
            let uu____4567 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4564 uu____4567
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4571 =
              let uu____4572 =
                let uu____4573 =
                  let uu____4574 = p_lident x  in
                  let uu____4575 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4574 uu____4575  in
                let uu____4576 =
                  let uu____4577 = p_noSeqTerm true false e1  in
                  let uu____4578 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4577 uu____4578  in
                op_Hat_Slash_Plus_Hat uu____4573 uu____4576  in
              FStar_Pprint.group uu____4572  in
            let uu____4579 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4571 uu____4579
        | uu____4580 ->
            let uu____4581 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4581

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
            let uu____4592 =
              let uu____4593 = p_tmIff e1  in
              let uu____4594 =
                let uu____4595 =
                  let uu____4596 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4596
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4595  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4593 uu____4594  in
            FStar_Pprint.group uu____4592
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4602 =
              let uu____4603 = p_tmIff e1  in
              let uu____4604 =
                let uu____4605 =
                  let uu____4606 =
                    let uu____4607 = p_typ false false t  in
                    let uu____4608 =
                      let uu____4609 = str "by"  in
                      let uu____4610 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4609 uu____4610  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4607 uu____4608  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4606
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4605  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4603 uu____4604  in
            FStar_Pprint.group uu____4602
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4611;_},e1::e2::e3::[])
            ->
            let uu____4617 =
              let uu____4618 =
                let uu____4619 =
                  let uu____4620 = p_atomicTermNotQUident e1  in
                  let uu____4621 =
                    let uu____4622 =
                      let uu____4623 =
                        let uu____4624 = p_term false false e2  in
                        soft_parens_with_nesting uu____4624  in
                      let uu____4625 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4623 uu____4625  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4622  in
                  FStar_Pprint.op_Hat_Hat uu____4620 uu____4621  in
                FStar_Pprint.group uu____4619  in
              let uu____4626 =
                let uu____4627 = p_noSeqTerm ps pb e3  in jump2 uu____4627
                 in
              FStar_Pprint.op_Hat_Hat uu____4618 uu____4626  in
            FStar_Pprint.group uu____4617
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4628;_},e1::e2::e3::[])
            ->
            let uu____4634 =
              let uu____4635 =
                let uu____4636 =
                  let uu____4637 = p_atomicTermNotQUident e1  in
                  let uu____4638 =
                    let uu____4639 =
                      let uu____4640 =
                        let uu____4641 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4641  in
                      let uu____4642 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4640 uu____4642  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4639  in
                  FStar_Pprint.op_Hat_Hat uu____4637 uu____4638  in
                FStar_Pprint.group uu____4636  in
              let uu____4643 =
                let uu____4644 = p_noSeqTerm ps pb e3  in jump2 uu____4644
                 in
              FStar_Pprint.op_Hat_Hat uu____4635 uu____4643  in
            FStar_Pprint.group uu____4634
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4654 =
              let uu____4655 = str "requires"  in
              let uu____4656 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4655 uu____4656  in
            FStar_Pprint.group uu____4654
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4666 =
              let uu____4667 = str "ensures"  in
              let uu____4668 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4667 uu____4668  in
            FStar_Pprint.group uu____4666
        | FStar_Parser_AST.Attributes es ->
            let uu____4672 =
              let uu____4673 = str "attributes"  in
              let uu____4674 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4673 uu____4674  in
            FStar_Pprint.group uu____4672
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4678 =
                let uu____4679 =
                  let uu____4680 = str "if"  in
                  let uu____4681 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4680 uu____4681  in
                let uu____4682 =
                  let uu____4683 = str "then"  in
                  let uu____4684 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4683 uu____4684  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4679 uu____4682  in
              FStar_Pprint.group uu____4678
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4687,uu____4688,e31) when
                     is_unit e31 ->
                     let uu____4690 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4690
                 | uu____4691 -> p_noSeqTerm false false e2  in
               let uu____4692 =
                 let uu____4693 =
                   let uu____4694 = str "if"  in
                   let uu____4695 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4694 uu____4695  in
                 let uu____4696 =
                   let uu____4697 =
                     let uu____4698 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4698 e2_doc  in
                   let uu____4699 =
                     let uu____4700 = str "else"  in
                     let uu____4701 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4700 uu____4701  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4697 uu____4699  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4693 uu____4696  in
               FStar_Pprint.group uu____4692)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4724 =
              let uu____4725 =
                let uu____4726 =
                  let uu____4727 = str "try"  in
                  let uu____4728 = p_noSeqTerm false false e1  in
                  prefix2 uu____4727 uu____4728  in
                let uu____4729 =
                  let uu____4730 = str "with"  in
                  let uu____4731 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4730 uu____4731  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4726 uu____4729  in
              FStar_Pprint.group uu____4725  in
            let uu____4740 = paren_if (ps || pb)  in uu____4740 uu____4724
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4765 =
              let uu____4766 =
                let uu____4767 =
                  let uu____4768 = str "match"  in
                  let uu____4769 = p_noSeqTerm false false e1  in
                  let uu____4770 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4768 uu____4769 uu____4770
                   in
                let uu____4771 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4767 uu____4771  in
              FStar_Pprint.group uu____4766  in
            let uu____4780 = paren_if (ps || pb)  in uu____4780 uu____4765
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4785 =
              let uu____4786 =
                let uu____4787 =
                  let uu____4788 = str "let open"  in
                  let uu____4789 = p_quident uid  in
                  let uu____4790 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4788 uu____4789 uu____4790
                   in
                let uu____4791 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4787 uu____4791  in
              FStar_Pprint.group uu____4786  in
            let uu____4792 = paren_if ps  in uu____4792 uu____4785
        | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
            let let_first =
              let uu____4857 = p_attrs_opt a0  in
              let uu____4858 =
                let uu____4859 =
                  let uu____4860 = str "let"  in
                  let uu____4861 =
                    let uu____4862 = p_letqualifier q  in
                    let uu____4863 = p_letbinding lb0  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4862 uu____4863  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4860 uu____4861  in
                FStar_Pprint.group uu____4859  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4857 uu____4858  in
            let let_rest =
              match attr_letbindings with
              | [] -> FStar_Pprint.empty
              | uu____4877 ->
                  let uu____4892 =
                    precede_break_separate_map FStar_Pprint.empty
                      FStar_Pprint.empty p_attr_letbinding attr_letbindings
                     in
                  FStar_Pprint.group uu____4892
               in
            let uu____4905 =
              let uu____4906 =
                let uu____4907 =
                  let uu____4908 = str "in"  in
                  let uu____4909 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4908 uu____4909  in
                FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4907  in
              FStar_Pprint.op_Hat_Slash_Hat let_first uu____4906  in
            let uu____4910 = paren_if ps  in uu____4910 uu____4905
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____4915;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____4918;
                                                             FStar_Parser_AST.level
                                                               = uu____4919;_})
            when matches_var maybe_x x ->
            let uu____4946 =
              let uu____4947 =
                let uu____4948 = str "function"  in
                let uu____4949 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4948 uu____4949  in
              FStar_Pprint.group uu____4947  in
            let uu____4958 = paren_if (ps || pb)  in uu____4958 uu____4946
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____4962 =
              let uu____4963 = str "quote"  in
              let uu____4964 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4963 uu____4964  in
            FStar_Pprint.group uu____4962
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____4966 =
              let uu____4967 = str "`"  in
              let uu____4968 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4967 uu____4968  in
            FStar_Pprint.group uu____4966
        | FStar_Parser_AST.VQuote e1 ->
            let uu____4970 =
              let uu____4971 = str "%`"  in
              let uu____4972 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____4971 uu____4972  in
            FStar_Pprint.group uu____4970
        | uu____4973 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___60_4974  ->
    match uu___60_4974 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4986 =
          let uu____4987 = str "[@"  in
          let uu____4988 =
            let uu____4989 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____4990 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4989 uu____4990  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4987 uu____4988  in
        FStar_Pprint.group uu____4986

and (p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4991  ->
    match uu____4991 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____5020 =
          let uu____5021 = p_attrs_opt a  in
          let uu____5022 =
            let uu____5023 =
              let uu____5024 = str "and "  in
              let uu____5025 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5024 uu____5025  in
            FStar_Pprint.group uu____5023  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5021 uu____5022  in
        let uu____5026 = p_term false false e  in
        prefix2 uu____5020 uu____5026

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
            let uu____5048 =
              let uu____5049 =
                let uu____5050 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5050 FStar_Pprint.space  in
              let uu____5051 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5049 uu____5051 FStar_Pprint.dot
               in
            let uu____5052 =
              let uu____5053 = p_trigger trigger  in
              let uu____5054 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5053 uu____5054  in
            prefix2 uu____5048 uu____5052
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5070 =
              let uu____5071 =
                let uu____5072 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5072 FStar_Pprint.space  in
              let uu____5073 = p_binders true bs  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5071 uu____5073 FStar_Pprint.dot
               in
            let uu____5074 =
              let uu____5075 = p_trigger trigger  in
              let uu____5076 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5075 uu____5076  in
            prefix2 uu____5070 uu____5074
        | uu____5077 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5079 -> str "forall"
    | FStar_Parser_AST.QExists uu____5092 -> str "exists"
    | uu____5105 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___61_5106  ->
    match uu___61_5106 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5118 =
          let uu____5119 =
            let uu____5120 = str "pattern"  in
            let uu____5121 =
              let uu____5122 =
                let uu____5123 = p_disjunctivePats pats  in jump2 uu____5123
                 in
              let uu____5124 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5122 uu____5124  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5120 uu____5121  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5119  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5118

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5130 = str "\\/"  in
    FStar_Pprint.separate_map uu____5130 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5136 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5136

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5146 =
              let uu____5147 =
                let uu____5148 = str "fun"  in
                let uu____5149 =
                  let uu____5150 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5150
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5148 uu____5149  in
              let uu____5151 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5147 uu____5151  in
            let uu____5152 = paren_if ps  in uu____5152 uu____5146
        | uu____5155 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5159  ->
      match uu____5159 with
      | (pat,when_opt,e) ->
          let uu____5175 =
            let uu____5176 =
              let uu____5177 =
                let uu____5178 =
                  let uu____5179 =
                    let uu____5180 = p_disjunctivePattern pat  in
                    let uu____5181 =
                      let uu____5182 = p_maybeWhen when_opt  in
                      FStar_Pprint.op_Hat_Hat uu____5182 FStar_Pprint.rarrow
                       in
                    op_Hat_Slash_Plus_Hat uu____5180 uu____5181  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5179  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5178  in
              FStar_Pprint.group uu____5177  in
            let uu____5183 = p_term false pb e  in
            op_Hat_Slash_Plus_Hat uu____5176 uu____5183  in
          FStar_Pprint.group uu____5175

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___62_5184  ->
    match uu___62_5184 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5188 = str "when"  in
        let uu____5189 =
          let uu____5190 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5190 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5188 uu____5189

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5192;_},e1::e2::[])
        ->
        let uu____5197 = str "<==>"  in
        let uu____5198 = p_tmImplies e1  in
        let uu____5199 = p_tmIff e2  in
        infix0 uu____5197 uu____5198 uu____5199
    | uu____5200 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5202;_},e1::e2::[])
        ->
        let uu____5207 = str "==>"  in
        let uu____5208 = p_tmArrow p_tmFormula e1  in
        let uu____5209 = p_tmImplies e2  in
        infix0 uu____5207 uu____5208 uu____5209
    | uu____5210 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5221 =
            let uu____5222 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5227 = p_binder false b  in
                   let uu____5228 =
                     let uu____5229 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5229
                      in
                   FStar_Pprint.op_Hat_Hat uu____5227 uu____5228) bs
               in
            let uu____5230 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5222 uu____5230  in
          FStar_Pprint.group uu____5221
      | uu____5231 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5233;_},e1::e2::[])
        ->
        let uu____5238 = str "\\/"  in
        let uu____5239 = p_tmFormula e1  in
        let uu____5240 = p_tmConjunction e2  in
        infix0 uu____5238 uu____5239 uu____5240
    | uu____5241 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5243;_},e1::e2::[])
        ->
        let uu____5248 = str "/\\"  in
        let uu____5249 = p_tmConjunction e1  in
        let uu____5250 = p_tmTuple e2  in
        infix0 uu____5248 uu____5249 uu____5250
    | uu____5251 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5268 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5268
          (fun uu____5276  ->
             match uu____5276 with | (e1,uu____5282) -> p_tmEq e1) args
    | uu____5283 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5288 =
             let uu____5289 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5289  in
           FStar_Pprint.group uu____5288)

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
            let uu____5352 = levels op1  in
            (match uu____5352 with
             | (left1,mine,right1) ->
                 let uu____5362 =
                   let uu____5363 = FStar_All.pipe_left str op1  in
                   let uu____5364 = p_tmEqWith' p_X left1 e1  in
                   let uu____5365 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5363 uu____5364 uu____5365  in
                 paren_if_gt curr mine uu____5362)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5366;_},e1::e2::[])
            ->
            let uu____5371 =
              let uu____5372 = p_tmEqWith p_X e1  in
              let uu____5373 =
                let uu____5374 =
                  let uu____5375 =
                    let uu____5376 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5376  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5375  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5374  in
              FStar_Pprint.op_Hat_Hat uu____5372 uu____5373  in
            FStar_Pprint.group uu____5371
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5377;_},e1::[])
            ->
            let uu____5381 = levels "-"  in
            (match uu____5381 with
             | (left1,mine,right1) ->
                 let uu____5391 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5391)
        | uu____5392 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5463)::(e2,uu____5465)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5485 = is_list e  in Prims.op_Negation uu____5485)
            ->
            let op = "::"  in
            let uu____5487 = levels op  in
            (match uu____5487 with
             | (left1,mine,right1) ->
                 let uu____5497 =
                   let uu____5498 = str op  in
                   let uu____5499 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5500 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5498 uu____5499 uu____5500  in
                 paren_if_gt curr mine uu____5497)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5508 = levels op  in
            (match uu____5508 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5522 = p_binder false b  in
                   let uu____5523 =
                     let uu____5524 =
                       let uu____5525 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5525 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5524
                      in
                   FStar_Pprint.op_Hat_Hat uu____5522 uu____5523  in
                 let uu____5526 =
                   let uu____5527 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5528 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5527 uu____5528  in
                 paren_if_gt curr mine uu____5526)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5535 = levels op1  in
            (match uu____5535 with
             | (left1,mine,right1) ->
                 let uu____5545 =
                   let uu____5546 = str op1  in
                   let uu____5547 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5548 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5546 uu____5547 uu____5548  in
                 paren_if_gt curr mine uu____5545)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5567 =
              let uu____5568 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5569 =
                let uu____5570 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5570 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5568 uu____5569  in
            braces_with_nesting uu____5567
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5575;_},e1::[])
            ->
            let uu____5579 =
              let uu____5580 = str "~"  in
              let uu____5581 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5580 uu____5581  in
            FStar_Pprint.group uu____5579
        | uu____5582 -> p_X e

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
        let uu____5589 =
          let uu____5590 = p_lidentOrUnderscore lid  in
          let uu____5591 =
            let uu____5592 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5592  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5590 uu____5591  in
        FStar_Pprint.group uu____5589
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5595 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5597 = p_appTerm e  in
    let uu____5598 =
      let uu____5599 =
        let uu____5600 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5600 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5599  in
    FStar_Pprint.op_Hat_Hat uu____5597 uu____5598

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5605 =
            let uu____5606 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5606 t phi  in
          soft_parens_with_nesting uu____5605
      | FStar_Parser_AST.TAnnotated uu____5607 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5612 ->
          let uu____5613 =
            let uu____5614 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5614
             in
          failwith uu____5613
      | FStar_Parser_AST.TVariable uu____5615 ->
          let uu____5616 =
            let uu____5617 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5617
             in
          failwith uu____5616
      | FStar_Parser_AST.NoName uu____5618 ->
          let uu____5619 =
            let uu____5620 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5620
             in
          failwith uu____5619

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5622  ->
      match uu____5622 with
      | (lid,e) ->
          let uu____5629 =
            let uu____5630 = p_qlident lid  in
            let uu____5631 =
              let uu____5632 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5632
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5630 uu____5631  in
          FStar_Pprint.group uu____5629

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5634 when is_general_application e ->
        let uu____5641 = head_and_args e  in
        (match uu____5641 with
         | (head1,args) ->
             let uu____5666 =
               let uu____5677 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5677
               then
                 let uu____5707 =
                   FStar_Util.take
                     (fun uu____5731  ->
                        match uu____5731 with
                        | (uu____5736,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5707 with
                 | (fs_typ_args,args1) ->
                     let uu____5774 =
                       let uu____5775 = p_indexingTerm head1  in
                       let uu____5776 =
                         let uu____5777 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5777 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5775 uu____5776  in
                     (uu____5774, args1)
               else
                 (let uu____5789 = p_indexingTerm head1  in
                  (uu____5789, args))
                in
             (match uu____5666 with
              | (head_doc,args1) ->
                  let uu____5810 =
                    let uu____5811 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5811 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5810))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5831 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5831)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5849 =
               let uu____5850 = p_quident lid  in
               let uu____5851 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5850 uu____5851  in
             FStar_Pprint.group uu____5849
         | hd1::tl1 ->
             let uu____5868 =
               let uu____5869 =
                 let uu____5870 =
                   let uu____5871 = p_quident lid  in
                   let uu____5872 = p_argTerm hd1  in
                   prefix2 uu____5871 uu____5872  in
                 FStar_Pprint.group uu____5870  in
               let uu____5873 =
                 let uu____5874 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5874  in
               FStar_Pprint.op_Hat_Hat uu____5869 uu____5873  in
             FStar_Pprint.group uu____5868)
    | uu____5879 -> p_indexingTerm e

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
         (let uu____5888 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5888 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5890 = str "#"  in
        let uu____5891 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5890 uu____5891
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5893  ->
    match uu____5893 with | (e,uu____5899) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5904;_},e1::e2::[])
          ->
          let uu____5909 =
            let uu____5910 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5911 =
              let uu____5912 =
                let uu____5913 = p_term false false e2  in
                soft_parens_with_nesting uu____5913  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5912  in
            FStar_Pprint.op_Hat_Hat uu____5910 uu____5911  in
          FStar_Pprint.group uu____5909
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5914;_},e1::e2::[])
          ->
          let uu____5919 =
            let uu____5920 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5921 =
              let uu____5922 =
                let uu____5923 = p_term false false e2  in
                soft_brackets_with_nesting uu____5923  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5922  in
            FStar_Pprint.op_Hat_Hat uu____5920 uu____5921  in
          FStar_Pprint.group uu____5919
      | uu____5924 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5929 = p_quident lid  in
        let uu____5930 =
          let uu____5931 =
            let uu____5932 = p_term false false e1  in
            soft_parens_with_nesting uu____5932  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5931  in
        FStar_Pprint.op_Hat_Hat uu____5929 uu____5930
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5938 = str (FStar_Ident.text_of_id op)  in
        let uu____5939 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5938 uu____5939
    | uu____5940 -> p_atomicTermNotQUident e

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
         | uu____5947 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5954 = str (FStar_Ident.text_of_id op)  in
        let uu____5955 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5954 uu____5955
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5959 =
          let uu____5960 =
            let uu____5961 = str (FStar_Ident.text_of_id op)  in
            let uu____5962 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5961 uu____5962  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5960  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5959
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5977 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5978 =
          let uu____5979 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5980 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5979 p_tmEq uu____5980  in
        let uu____5987 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5977 uu____5978 uu____5987
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5990 =
          let uu____5991 = p_atomicTermNotQUident e1  in
          let uu____5992 =
            let uu____5993 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5993  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5991 uu____5992
           in
        FStar_Pprint.group uu____5990
    | uu____5994 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5999 = p_quident constr_lid  in
        let uu____6000 =
          let uu____6001 =
            let uu____6002 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6002  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6001  in
        FStar_Pprint.op_Hat_Hat uu____5999 uu____6000
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6004 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6004 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6006 = p_term false false e1  in
        soft_parens_with_nesting uu____6006
    | uu____6007 when is_array e ->
        let es = extract_from_list e  in
        let uu____6011 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6012 =
          let uu____6013 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6013
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6016 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6011 uu____6012 uu____6016
    | uu____6017 when is_list e ->
        let uu____6018 =
          let uu____6019 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6020 = extract_from_list e  in
          separate_map_or_flow_last uu____6019
            (fun ps  -> p_noSeqTerm ps false) uu____6020
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6018 FStar_Pprint.rbracket
    | uu____6025 when is_lex_list e ->
        let uu____6026 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6027 =
          let uu____6028 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6029 = extract_from_list e  in
          separate_map_or_flow_last uu____6028
            (fun ps  -> p_noSeqTerm ps false) uu____6029
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6026 uu____6027 FStar_Pprint.rbracket
    | uu____6034 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6038 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6039 =
          let uu____6040 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6040 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6038 uu____6039 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6044 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6045 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6044 uu____6045
    | FStar_Parser_AST.Op (op,args) when
        let uu____6052 = handleable_op op args  in
        Prims.op_Negation uu____6052 ->
        let uu____6053 =
          let uu____6054 =
            let uu____6055 =
              let uu____6056 =
                let uu____6057 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6057
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6056  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6055  in
          Prims.strcat "Operation " uu____6054  in
        failwith uu____6053
    | FStar_Parser_AST.Uvar uu____6058 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6059 = p_term false false e  in
        soft_parens_with_nesting uu____6059
    | FStar_Parser_AST.Const uu____6060 ->
        let uu____6061 = p_term false false e  in
        soft_parens_with_nesting uu____6061
    | FStar_Parser_AST.Op uu____6062 ->
        let uu____6069 = p_term false false e  in
        soft_parens_with_nesting uu____6069
    | FStar_Parser_AST.Tvar uu____6070 ->
        let uu____6071 = p_term false false e  in
        soft_parens_with_nesting uu____6071
    | FStar_Parser_AST.Var uu____6072 ->
        let uu____6073 = p_term false false e  in
        soft_parens_with_nesting uu____6073
    | FStar_Parser_AST.Name uu____6074 ->
        let uu____6075 = p_term false false e  in
        soft_parens_with_nesting uu____6075
    | FStar_Parser_AST.Construct uu____6076 ->
        let uu____6087 = p_term false false e  in
        soft_parens_with_nesting uu____6087
    | FStar_Parser_AST.Abs uu____6088 ->
        let uu____6095 = p_term false false e  in
        soft_parens_with_nesting uu____6095
    | FStar_Parser_AST.App uu____6096 ->
        let uu____6103 = p_term false false e  in
        soft_parens_with_nesting uu____6103
    | FStar_Parser_AST.Let uu____6104 ->
        let uu____6125 = p_term false false e  in
        soft_parens_with_nesting uu____6125
    | FStar_Parser_AST.LetOpen uu____6126 ->
        let uu____6131 = p_term false false e  in
        soft_parens_with_nesting uu____6131
    | FStar_Parser_AST.Seq uu____6132 ->
        let uu____6137 = p_term false false e  in
        soft_parens_with_nesting uu____6137
    | FStar_Parser_AST.Bind uu____6138 ->
        let uu____6145 = p_term false false e  in
        soft_parens_with_nesting uu____6145
    | FStar_Parser_AST.If uu____6146 ->
        let uu____6153 = p_term false false e  in
        soft_parens_with_nesting uu____6153
    | FStar_Parser_AST.Match uu____6154 ->
        let uu____6169 = p_term false false e  in
        soft_parens_with_nesting uu____6169
    | FStar_Parser_AST.TryWith uu____6170 ->
        let uu____6185 = p_term false false e  in
        soft_parens_with_nesting uu____6185
    | FStar_Parser_AST.Ascribed uu____6186 ->
        let uu____6195 = p_term false false e  in
        soft_parens_with_nesting uu____6195
    | FStar_Parser_AST.Record uu____6196 ->
        let uu____6209 = p_term false false e  in
        soft_parens_with_nesting uu____6209
    | FStar_Parser_AST.Project uu____6210 ->
        let uu____6215 = p_term false false e  in
        soft_parens_with_nesting uu____6215
    | FStar_Parser_AST.Product uu____6216 ->
        let uu____6223 = p_term false false e  in
        soft_parens_with_nesting uu____6223
    | FStar_Parser_AST.Sum uu____6224 ->
        let uu____6231 = p_term false false e  in
        soft_parens_with_nesting uu____6231
    | FStar_Parser_AST.QForall uu____6232 ->
        let uu____6245 = p_term false false e  in
        soft_parens_with_nesting uu____6245
    | FStar_Parser_AST.QExists uu____6246 ->
        let uu____6259 = p_term false false e  in
        soft_parens_with_nesting uu____6259
    | FStar_Parser_AST.Refine uu____6260 ->
        let uu____6265 = p_term false false e  in
        soft_parens_with_nesting uu____6265
    | FStar_Parser_AST.NamedTyp uu____6266 ->
        let uu____6271 = p_term false false e  in
        soft_parens_with_nesting uu____6271
    | FStar_Parser_AST.Requires uu____6272 ->
        let uu____6279 = p_term false false e  in
        soft_parens_with_nesting uu____6279
    | FStar_Parser_AST.Ensures uu____6280 ->
        let uu____6287 = p_term false false e  in
        soft_parens_with_nesting uu____6287
    | FStar_Parser_AST.Attributes uu____6288 ->
        let uu____6291 = p_term false false e  in
        soft_parens_with_nesting uu____6291
    | FStar_Parser_AST.Quote uu____6292 ->
        let uu____6297 = p_term false false e  in
        soft_parens_with_nesting uu____6297
    | FStar_Parser_AST.VQuote uu____6298 ->
        let uu____6299 = p_term false false e  in
        soft_parens_with_nesting uu____6299

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___65_6300  ->
    match uu___65_6300 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6304 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6304
    | FStar_Const.Const_string (s,uu____6306) ->
        let uu____6307 = str s  in FStar_Pprint.dquotes uu____6307
    | FStar_Const.Const_bytearray (bytes,uu____6309) ->
        let uu____6314 =
          let uu____6315 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6315  in
        let uu____6316 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6314 uu____6316
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6334 =
          match uu___63_6334 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6338 =
          match uu___64_6338 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6349  ->
               match uu____6349 with
               | (s,w) ->
                   let uu____6356 = signedness s  in
                   let uu____6357 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6356 uu____6357)
            sign_width_opt
           in
        let uu____6358 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6358 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6360 = FStar_Range.string_of_range r  in str uu____6360
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6362 = p_quident lid  in
        let uu____6363 =
          let uu____6364 =
            let uu____6365 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6365  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6364  in
        FStar_Pprint.op_Hat_Hat uu____6362 uu____6363

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6367 = str "u#"  in
    let uu____6368 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6367 uu____6368

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6370;_},u1::u2::[])
        ->
        let uu____6375 =
          let uu____6376 = p_universeFrom u1  in
          let uu____6377 =
            let uu____6378 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6378  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6376 uu____6377  in
        FStar_Pprint.group uu____6375
    | FStar_Parser_AST.App uu____6379 ->
        let uu____6386 = head_and_args u  in
        (match uu____6386 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6412 =
                    let uu____6413 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6414 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6422  ->
                           match uu____6422 with
                           | (u1,uu____6428) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6413 uu____6414  in
                  FStar_Pprint.group uu____6412
              | uu____6429 ->
                  let uu____6430 =
                    let uu____6431 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6431
                     in
                  failwith uu____6430))
    | uu____6432 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6456 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6456
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6457;_},uu____6458::uu____6459::[])
        ->
        let uu____6462 = p_universeFrom u  in
        soft_parens_with_nesting uu____6462
    | FStar_Parser_AST.App uu____6463 ->
        let uu____6470 = p_universeFrom u  in
        soft_parens_with_nesting uu____6470
    | uu____6471 ->
        let uu____6472 =
          let uu____6473 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6473
           in
        failwith uu____6472

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
       | FStar_Parser_AST.Module (uu____6513,decls) ->
           let uu____6519 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6519
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6528,decls,uu____6530) ->
           let uu____6535 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6535
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6586  ->
         match uu____6586 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6626,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6632,decls,uu____6634) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6679 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6692;
                 FStar_Parser_AST.doc = uu____6693;
                 FStar_Parser_AST.quals = uu____6694;
                 FStar_Parser_AST.attrs = uu____6695;_}::uu____6696 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6702 =
                   let uu____6705 =
                     let uu____6708 = FStar_List.tl ds  in d :: uu____6708
                      in
                   d0 :: uu____6705  in
                 (uu____6702, (d0.FStar_Parser_AST.drange))
             | uu____6713 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6679 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6771 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6771 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6867 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6867, comments1))))))
  