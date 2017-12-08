open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____15 'Auu____16 .
    Prims.bool -> ('Auu____16 -> 'Auu____15) -> 'Auu____16 -> 'Auu____15
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let should_unparen : Prims.bool FStar_ST.ref = FStar_Util.mk_ref true 
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____194 =
      let uu____195 = FStar_ST.op_Bang should_unparen  in
      Prims.op_Negation uu____195  in
    if uu____194
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____246 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____255 'Auu____256 .
    'Auu____256 ->
      ('Auu____255 -> 'Auu____256) ->
        'Auu____255 FStar_Pervasives_Native.option -> 'Auu____256
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
      FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "1") prefix_
        body
  
let op_Hat_Slash_Plus_Hat :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document =
  fun prefix_  -> fun body  -> prefix2 prefix_ body 
let jump2 : FStar_Pprint.document -> FStar_Pprint.document =
  fun body  ->
    FStar_Pprint.jump (Prims.parse_int "2") (Prims.parse_int "1") body
  
let infix2 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "2") (Prims.parse_int "1") 
let infix0 :
  FStar_Pprint.document ->
    FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document
  = FStar_Pprint.infix (Prims.parse_int "0") (Prims.parse_int "1") 
let break1 : FStar_Pprint.document =
  FStar_Pprint.break_ (Prims.parse_int "1") 
let separate_break_map :
  'Auu____310 .
    FStar_Pprint.document ->
      ('Auu____310 -> FStar_Pprint.document) ->
        'Auu____310 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____332 =
          let uu____333 =
            let uu____334 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____334  in
          FStar_Pprint.separate_map uu____333 f l  in
        FStar_Pprint.group uu____332
  
let precede_break_separate_map :
  'Auu____340 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____340 -> FStar_Pprint.document) ->
          'Auu____340 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____366 =
            let uu____367 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____368 =
              let uu____369 = FStar_List.hd l  in
              FStar_All.pipe_right uu____369 f  in
            FStar_Pprint.precede uu____367 uu____368  in
          let uu____370 =
            let uu____371 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____377 =
                   let uu____378 =
                     let uu____379 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____379  in
                   FStar_Pprint.op_Hat_Hat sep uu____378  in
                 FStar_Pprint.op_Hat_Hat break1 uu____377) uu____371
             in
          FStar_Pprint.op_Hat_Hat uu____366 uu____370
  
let concat_break_map :
  'Auu____383 .
    ('Auu____383 -> FStar_Pprint.document) ->
      'Auu____383 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____401 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____405 = f x  in FStar_Pprint.op_Hat_Hat uu____405 break1)
          l
         in
      FStar_Pprint.group uu____401
  
let parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let soft_parens_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
      FStar_Pprint.lparen contents FStar_Pprint.rparen
  
let braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let soft_braces_with_nesting : FStar_Pprint.document -> FStar_Pprint.document
  =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbrace contents FStar_Pprint.rbrace
  
let brackets_with_nesting : FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let soft_brackets_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      FStar_Pprint.lbracket contents FStar_Pprint.rbracket
  
let soft_begin_end_with_nesting :
  FStar_Pprint.document -> FStar_Pprint.document =
  fun contents  ->
    let uu____427 = str "begin"  in
    let uu____428 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____427 contents uu____428
  
let separate_map_or_flow :
  'Auu____433 .
    FStar_Pprint.document ->
      ('Auu____433 -> FStar_Pprint.document) ->
        'Auu____433 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____465 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____465 -> FStar_Pprint.document) ->
                  'Auu____465 Prims.list -> FStar_Pprint.document
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
                    (let uu____510 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____510
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____520 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____520 -> FStar_Pprint.document) ->
                  'Auu____520 Prims.list -> FStar_Pprint.document
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
                    (let uu____565 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____565
                       closing)
  
let doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____578  ->
    match uu____578 with
    | (comment,keywords) ->
        let uu____603 =
          let uu____604 =
            let uu____607 = str comment  in
            let uu____608 =
              let uu____611 =
                let uu____614 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____623  ->
                       match uu____623 with
                       | (k,v1) ->
                           let uu____630 =
                             let uu____633 = str k  in
                             let uu____634 =
                               let uu____637 =
                                 let uu____640 = str v1  in [uu____640]  in
                               FStar_Pprint.rarrow :: uu____637  in
                             uu____633 :: uu____634  in
                           FStar_Pprint.concat uu____630) keywords
                   in
                [uu____614]  in
              FStar_Pprint.space :: uu____611  in
            uu____607 :: uu____608  in
          FStar_Pprint.concat uu____604  in
        FStar_Pprint.group uu____603
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____644 =
      let uu____645 = unparen e  in uu____645.FStar_Parser_AST.tm  in
    match uu____644 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____646 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____653 =
        let uu____654 = unparen t  in uu____654.FStar_Parser_AST.tm  in
      match uu____653 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____656 -> false
  
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
        let uu____673 =
          let uu____674 = unparen e  in uu____674.FStar_Parser_AST.tm  in
        match uu____673 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____687::(e2,uu____689)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____712 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____722 =
      let uu____723 = unparen e  in uu____723.FStar_Parser_AST.tm  in
    match uu____722 with
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
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____769 =
      let uu____770 = unparen e  in uu____770.FStar_Parser_AST.tm  in
    match uu____769 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____772;
           FStar_Parser_AST.level = uu____773;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____775 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____779 =
      let uu____780 = unparen e  in uu____780.FStar_Parser_AST.tm  in
    match uu____779 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____783;
           FStar_Parser_AST.level = uu____784;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____786;
                                                        FStar_Parser_AST.level
                                                          = uu____787;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____789;
                                                   FStar_Parser_AST.level =
                                                     uu____790;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____792;
                FStar_Parser_AST.level = uu____793;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____795;
           FStar_Parser_AST.level = uu____796;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____798 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____804 =
      let uu____805 = unparen e  in uu____805.FStar_Parser_AST.tm  in
    match uu____804 with
    | FStar_Parser_AST.Var uu____808 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____809;
           FStar_Parser_AST.range = uu____810;
           FStar_Parser_AST.level = uu____811;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____812;
                                                        FStar_Parser_AST.range
                                                          = uu____813;
                                                        FStar_Parser_AST.level
                                                          = uu____814;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____816;
                                                   FStar_Parser_AST.level =
                                                     uu____817;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____818;
                FStar_Parser_AST.range = uu____819;
                FStar_Parser_AST.level = uu____820;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____822;
           FStar_Parser_AST.level = uu____823;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____825 = extract_from_ref_set e1  in
        let uu____828 = extract_from_ref_set e2  in
        FStar_List.append uu____825 uu____828
    | uu____831 ->
        let uu____832 =
          let uu____833 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____833  in
        failwith uu____832
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____839 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____839
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____843 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____843
  
let is_general_prefix_op : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0")
       in
    ((op_starting_char = 33) || (op_starting_char = 63)) ||
      ((op_starting_char = 126) && ((FStar_Ident.text_of_id op) <> "~"))
  
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____893 =
        let uu____894 = unparen e1  in uu____894.FStar_Parser_AST.tm  in
      match uu____893 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____912 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____926 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____930 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____934 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___60_952  ->
    match uu___60_952 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___61_969  ->
      match uu___61_969 with
      | FStar_Util.Inl c ->
          let uu____978 = FStar_String.get s (Prims.parse_int "0")  in
          uu____978 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____986 .
    Prims.string ->
      ('Auu____986,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1005  ->
      match uu____1005 with
      | (assoc_levels,tokens) ->
          let uu____1033 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1033 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1059 .
    Prims.unit ->
      (associativity,('Auu____1059,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1070  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1086 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1086) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1098  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1133 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1133) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1145  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1173 .
    Prims.unit ->
      (associativity,('Auu____1173,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1184  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1200 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1200) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1212  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1240 .
    Prims.unit ->
      (associativity,('Auu____1240,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1251  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1267 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1267) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1279  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1300 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1300) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1312  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1347 .
    Prims.unit ->
      (associativity,('Auu____1347,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1358  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1374 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1374) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1386  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1407 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1407) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1419  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1440 .
    Prims.unit ->
      (associativity,('Auu____1440,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1451  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1467 .
    Prims.unit ->
      (associativity,('Auu____1467,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1478  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1494 .
    Prims.unit ->
      (associativity,('Auu____1494,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1505  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___62_1712 =
    match uu___62_1712 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1752  ->
         match uu____1752 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1832 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1832 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1882) ->
          assoc_levels
      | uu____1926 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1961 .
    ('Auu____1961,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2021 =
        FStar_List.tryFind
          (fun uu____2061  ->
             match uu____2061 with
             | (uu____2079,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2021 with
      | FStar_Pervasives_Native.Some ((uu____2121,l1,uu____2123),uu____2124)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2179 =
            let uu____2180 =
              let uu____2181 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2181  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2180
             in
          failwith uu____2179
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____2215 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2215) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2229  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2310 =
      let uu____2324 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2324 (operatorInfix0ad12 ())  in
    uu____2310 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2437 =
      let uu____2451 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2451 opinfix34  in
    uu____2437 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2517 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2517
    then (Prims.parse_int "1")
    else
      (let uu____2519 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2519
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2525 . FStar_Ident.ident -> 'Auu____2525 Prims.list -> Prims.bool =
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
      | uu____2538 -> false
  
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2568 .
    ('Auu____2568 -> FStar_Pprint.document) ->
      'Auu____2568 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2600 = FStar_ST.op_Bang comment_stack  in
          match uu____2600 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2688 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2688
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2754 =
                    let uu____2755 =
                      let uu____2756 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2756
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2755  in
                  comments_before_pos uu____2754 print_pos lookahead_pos))
              else
                (let uu____2758 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2758))
           in
        let uu____2759 =
          let uu____2764 =
            let uu____2765 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2765  in
          let uu____2766 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2764 uu____2766  in
        match uu____2759 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2772 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2772
              else comments  in
            let uu____2778 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2778
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2791 = FStar_ST.op_Bang comment_stack  in
          match uu____2791 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2933 =
                    let uu____2934 =
                      let uu____2935 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2935  in
                    uu____2934 - lbegin  in
                  max k uu____2933  in
                let doc2 =
                  let uu____2937 =
                    let uu____2938 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2939 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2938 uu____2939  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2937  in
                let uu____2940 =
                  let uu____2941 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2941  in
                place_comments_until_pos (Prims.parse_int "1") uu____2940
                  pos_end doc2))
          | uu____2942 ->
              let lnum =
                let uu____2950 =
                  let uu____2951 = FStar_Range.line_of_pos pos_end  in
                  uu____2951 - lbegin  in
                max (Prims.parse_int "1") uu____2950  in
              let uu____2952 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2952
  
let separate_map_with_comments :
  'Auu____2959 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2959 -> FStar_Pprint.document) ->
          'Auu____2959 Prims.list ->
            ('Auu____2959 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3007 x =
              match uu____3007 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3021 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3021 doc1
                     in
                  let uu____3022 =
                    let uu____3023 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3023  in
                  let uu____3024 =
                    let uu____3025 =
                      let uu____3026 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____3026  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3025  in
                  (uu____3022, uu____3024)
               in
            let uu____3027 =
              let uu____3034 = FStar_List.hd xs  in
              let uu____3035 = FStar_List.tl xs  in (uu____3034, uu____3035)
               in
            match uu____3027 with
            | (x,xs1) ->
                let init1 =
                  let uu____3051 =
                    let uu____3052 =
                      let uu____3053 = extract_range x  in
                      FStar_Range.end_of_range uu____3053  in
                    FStar_Range.line_of_pos uu____3052  in
                  let uu____3054 =
                    let uu____3055 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____3055  in
                  (uu____3051, uu____3054)  in
                let uu____3056 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3056
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3351 =
      let uu____3352 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3353 =
        let uu____3354 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3355 =
          let uu____3356 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3357 =
            let uu____3358 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3358
             in
          FStar_Pprint.op_Hat_Hat uu____3356 uu____3357  in
        FStar_Pprint.op_Hat_Hat uu____3354 uu____3355  in
      FStar_Pprint.op_Hat_Hat uu____3352 uu____3353  in
    FStar_Pprint.group uu____3351

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3361 =
      let uu____3362 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3362  in
    let uu____3363 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3361 FStar_Pprint.space uu____3363
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3364  ->
    match uu____3364 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3398 =
                match uu____3398 with
                | (kwd,arg) ->
                    let uu____3405 = str "@"  in
                    let uu____3406 =
                      let uu____3407 = str kwd  in
                      let uu____3408 =
                        let uu____3409 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3409
                         in
                      FStar_Pprint.op_Hat_Hat uu____3407 uu____3408  in
                    FStar_Pprint.op_Hat_Hat uu____3405 uu____3406
                 in
              let uu____3410 =
                let uu____3411 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3411 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3410
           in
        let uu____3416 =
          let uu____3417 =
            let uu____3418 =
              let uu____3419 =
                let uu____3420 = str doc1  in
                let uu____3421 =
                  let uu____3422 =
                    let uu____3423 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3423  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3422  in
                FStar_Pprint.op_Hat_Hat uu____3420 uu____3421  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3419  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3418  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3417  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3416

and p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3427 =
          let uu____3428 = str "val"  in
          let uu____3429 =
            let uu____3430 =
              let uu____3431 = p_lident lid  in
              let uu____3432 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3431 uu____3432  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3430  in
          FStar_Pprint.op_Hat_Hat uu____3428 uu____3429  in
        let uu____3433 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3427 uu____3433
    | FStar_Parser_AST.TopLevelLet (uu____3434,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3459 =
               let uu____3460 = str "let"  in
               let uu____3461 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3460 uu____3461  in
             FStar_Pprint.group uu____3459) lbs
    | uu____3462 -> FStar_Pprint.empty

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3465 =
          let uu____3466 = str "open"  in
          let uu____3467 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3466 uu____3467  in
        FStar_Pprint.group uu____3465
    | FStar_Parser_AST.Include uid ->
        let uu____3469 =
          let uu____3470 = str "include"  in
          let uu____3471 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3470 uu____3471  in
        FStar_Pprint.group uu____3469
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3474 =
          let uu____3475 = str "module"  in
          let uu____3476 =
            let uu____3477 =
              let uu____3478 = p_uident uid1  in
              let uu____3479 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3478 uu____3479  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3477  in
          FStar_Pprint.op_Hat_Hat uu____3475 uu____3476  in
        let uu____3480 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3474 uu____3480
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3482 =
          let uu____3483 = str "module"  in
          let uu____3484 =
            let uu____3485 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3485  in
          FStar_Pprint.op_Hat_Hat uu____3483 uu____3484  in
        FStar_Pprint.group uu____3482
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3518 = str "effect"  in
          let uu____3519 =
            let uu____3520 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3520  in
          FStar_Pprint.op_Hat_Hat uu____3518 uu____3519  in
        let uu____3521 =
          let uu____3522 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3522 FStar_Pprint.equals
           in
        let uu____3523 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3521 uu____3523
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3541 = str "type"  in
        let uu____3542 = str "and"  in
        precede_break_separate_map uu____3541 uu____3542 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3564 = str "let"  in
          let uu____3565 =
            let uu____3566 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3566 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3564 uu____3565  in
        let uu____3567 =
          let uu____3568 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3568 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3567 p_letbinding lbs
          (fun uu____3576  ->
             match uu____3576 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3585 =
          let uu____3586 = str "val"  in
          let uu____3587 =
            let uu____3588 =
              let uu____3589 = p_lident lid  in
              let uu____3590 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3589 uu____3590  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3588  in
          FStar_Pprint.op_Hat_Hat uu____3586 uu____3587  in
        let uu____3591 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3585 uu____3591
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3595 =
            let uu____3596 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3596 FStar_Util.is_upper  in
          if uu____3595
          then FStar_Pprint.empty
          else
            (let uu____3598 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3598 FStar_Pprint.space)
           in
        let uu____3599 =
          let uu____3600 =
            let uu____3601 = p_ident id1  in
            let uu____3602 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3601 uu____3602  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3600  in
        let uu____3603 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3599 uu____3603
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3610 = str "exception"  in
        let uu____3611 =
          let uu____3612 =
            let uu____3613 = p_uident uid  in
            let uu____3614 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3619 = str "of"  in
                   let uu____3620 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3619 uu____3620) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3613 uu____3614  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3612  in
        FStar_Pprint.op_Hat_Hat uu____3610 uu____3611
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3622 = str "new_effect"  in
        let uu____3623 =
          let uu____3624 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3624  in
        FStar_Pprint.op_Hat_Hat uu____3622 uu____3623
    | FStar_Parser_AST.SubEffect se ->
        let uu____3626 = str "sub_effect"  in
        let uu____3627 =
          let uu____3628 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3628  in
        FStar_Pprint.op_Hat_Hat uu____3626 uu____3627
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3631 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3631 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3632 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3633) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___63_3650  ->
    match uu___63_3650 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3652 = str "#set-options"  in
        let uu____3653 =
          let uu____3654 =
            let uu____3655 = str s  in FStar_Pprint.dquotes uu____3655  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3654  in
        FStar_Pprint.op_Hat_Hat uu____3652 uu____3653
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3659 = str "#reset-options"  in
        let uu____3660 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3664 =
                 let uu____3665 = str s  in FStar_Pprint.dquotes uu____3665
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3664) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3659 uu____3660
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
  fun uu____3718  ->
    match uu____3718 with
    | (typedecl,fsdoc_opt) ->
        let uu____3731 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3732 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3731 uu____3732

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___64_3733  ->
    match uu___64_3733 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3748 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3764 =
          let uu____3765 = p_typ t  in prefix2 FStar_Pprint.equals uu____3765
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3809 =
          match uu____3809 with
          | (lid1,t,doc_opt) ->
              let uu____3825 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3825
           in
        let p_fields uu____3839 =
          let uu____3840 =
            let uu____3841 =
              let uu____3842 =
                let uu____3843 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3843 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3842  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3841  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3840  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3907 =
          match uu____3907 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3933 =
                  let uu____3934 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3934  in
                FStar_Range.extend_to_end_of_line uu____3933  in
              let p_constructorBranch decl =
                let uu____3967 =
                  let uu____3968 =
                    let uu____3969 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3969  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3968  in
                FStar_Pprint.group uu____3967  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3989 =
          let uu____3990 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3990  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____4005  ->
             let uu____4006 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____4006)

and p_typeDeclPrefix :
  FStar_Ident.ident ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
        (Prims.unit -> FStar_Pprint.document) -> FStar_Pprint.document
  =
  fun lid  ->
    fun bs  ->
      fun typ_opt  ->
        fun cont  ->
          if (bs = []) && (typ_opt = FStar_Pervasives_Native.None)
          then
            let uu____4021 = p_ident lid  in
            let uu____4022 =
              let uu____4023 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4023  in
            FStar_Pprint.op_Hat_Hat uu____4021 uu____4022
          else
            (let binders_doc =
               let uu____4026 = p_typars bs  in
               let uu____4027 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____4031 =
                        let uu____4032 =
                          let uu____4033 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____4033
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4032
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____4031) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____4026 uu____4027  in
             let uu____4034 = p_ident lid  in
             let uu____4035 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____4034 binders_doc uu____4035)

and p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4036  ->
    match uu____4036 with
    | (lid,t,doc_opt) ->
        let uu____4052 =
          let uu____4053 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____4054 =
            let uu____4055 = p_lident lid  in
            let uu____4056 =
              let uu____4057 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4057  in
            FStar_Pprint.op_Hat_Hat uu____4055 uu____4056  in
          FStar_Pprint.op_Hat_Hat uu____4053 uu____4054  in
        FStar_Pprint.group uu____4052

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____4058  ->
    match uu____4058 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____4086 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4087 =
          let uu____4088 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____4089 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____4094 =
                   let uu____4095 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4095  in
                 let uu____4096 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____4094 uu____4096) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____4088 uu____4089  in
        FStar_Pprint.op_Hat_Hat uu____4086 uu____4087

and p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4097  ->
    match uu____4097 with
    | (pat,uu____4103) ->
        let uu____4104 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____4115 =
                let uu____4116 =
                  let uu____4117 =
                    let uu____4118 =
                      let uu____4119 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4119
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4118  in
                  FStar_Pprint.group uu____4117  in
                FStar_Pprint.op_Hat_Hat break1 uu____4116  in
              (pat1, uu____4115)
          | uu____4120 -> (pat, FStar_Pprint.empty)  in
        (match uu____4104 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4124);
                     FStar_Parser_AST.prange = uu____4125;_},pats)
                  ->
                  let uu____4135 =
                    let uu____4136 = p_lident x  in
                    let uu____4137 =
                      let uu____4138 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4138 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4136 uu____4137  in
                  FStar_Pprint.group uu____4135
              | uu____4139 ->
                  let uu____4140 =
                    let uu____4141 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4141 ascr_doc  in
                  FStar_Pprint.group uu____4140))

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4142  ->
    match uu____4142 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4150 =
          let uu____4151 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4151  in
        let uu____4152 = p_term e  in prefix2 uu____4150 uu____4152

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___65_4153  ->
    match uu___65_4153 with
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
        let uu____4178 = p_uident uid  in
        let uu____4179 = p_binders true bs  in
        let uu____4180 =
          let uu____4181 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____4181  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4178 uu____4179 uu____4180

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
          let uu____4190 =
            let uu____4191 =
              let uu____4192 =
                let uu____4193 = p_uident uid  in
                let uu____4194 = p_binders true bs  in
                let uu____4195 =
                  let uu____4196 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____4196  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4193 uu____4194 uu____4195
                 in
              FStar_Pprint.group uu____4192  in
            let uu____4197 =
              let uu____4198 = str "with"  in
              let uu____4199 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____4198 uu____4199  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4191 uu____4197  in
          braces_with_nesting uu____4190

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4229 =
          let uu____4230 = p_lident lid  in
          let uu____4231 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____4230 uu____4231  in
        let uu____4232 = p_simpleTerm e  in prefix2 uu____4229 uu____4232
    | uu____4233 ->
        let uu____4234 =
          let uu____4235 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4235
           in
        failwith uu____4234

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____4290 =
        match uu____4290 with
        | (kwd,t) ->
            let uu____4297 =
              let uu____4298 = str kwd  in
              let uu____4299 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4298 uu____4299  in
            let uu____4300 = p_simpleTerm t  in prefix2 uu____4297 uu____4300
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____4305 =
      let uu____4306 =
        let uu____4307 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4308 =
          let uu____4309 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4309  in
        FStar_Pprint.op_Hat_Hat uu____4307 uu____4308  in
      let uu____4310 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4306 uu____4310  in
    let uu____4311 =
      let uu____4312 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4312  in
    FStar_Pprint.op_Hat_Hat uu____4305 uu____4311

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___66_4313  ->
    match uu___66_4313 with
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
    let uu____4315 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4315

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___67_4316  ->
    match uu___67_4316 with
    | FStar_Parser_AST.Rec  ->
        let uu____4317 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4317
    | FStar_Parser_AST.Mutable  ->
        let uu____4318 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4318
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___68_4319  ->
    match uu___68_4319 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4324 =
          let uu____4325 =
            let uu____4326 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4326  in
          FStar_Pprint.separate_map uu____4325 p_tuplePattern pats  in
        FStar_Pprint.group uu____4324
    | uu____4327 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4334 =
          let uu____4335 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4335 p_constructorPattern pats  in
        FStar_Pprint.group uu____4334
    | uu____4336 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4339;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4344 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4345 = p_constructorPattern hd1  in
        let uu____4346 = p_constructorPattern tl1  in
        infix0 uu____4344 uu____4345 uu____4346
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4348;_},pats)
        ->
        let uu____4354 = p_quident uid  in
        let uu____4355 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4354 uu____4355
    | uu____4356 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4360 =
          let uu____4365 =
            let uu____4366 = unparen t  in uu____4366.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____4365)  in
        (match uu____4360 with
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
                   let uu____4397 = p_typ t  in
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

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
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
            let uu____4491 =
              let uu____4492 = unparen t  in uu____4492.FStar_Parser_AST.tm
               in
            match uu____4491 with
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
          let uu____4517 =
            let uu____4518 = unparen t  in uu____4518.FStar_Parser_AST.tm  in
          (match uu____4517 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4520;
                  FStar_Parser_AST.blevel = uu____4521;
                  FStar_Parser_AST.aqual = uu____4522;_},phi)
               ->
               if is_atomic
               then
                 let uu____4524 =
                   let uu____4525 =
                     let uu____4526 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4526 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4525  in
                 FStar_Pprint.group uu____4524
               else
                 (let uu____4528 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4528)
           | uu____4529 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4537 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4538 =
            let uu____4539 =
              let uu____4540 =
                let uu____4541 = p_appTerm t  in
                let uu____4542 =
                  let uu____4543 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____4543  in
                FStar_Pprint.op_Hat_Hat uu____4541 uu____4542  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4540  in
            FStar_Pprint.op_Hat_Hat binder uu____4539  in
          FStar_Pprint.op_Hat_Hat uu____4537 uu____4538

and p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> separate_map_or_flow break1 (p_binder is_atomic) bs

and p_qlident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and p_quident : FStar_Ident.lid -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_lid lid)

and p_ident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_lident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_uident : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_tvar : FStar_Ident.ident -> FStar_Pprint.document =
  fun lid  -> str (FStar_Ident.text_of_id lid)

and p_lidentOrUnderscore : FStar_Ident.ident -> FStar_Pprint.document =
  fun id1  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id1.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id1

and p_term : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4557 =
      let uu____4558 = unparen e  in uu____4558.FStar_Parser_AST.tm  in
    match uu____4557 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4561 =
          let uu____4562 =
            let uu____4563 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4563 FStar_Pprint.semi  in
          FStar_Pprint.group uu____4562  in
        let uu____4564 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4561 uu____4564
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4568 =
          let uu____4569 =
            let uu____4570 =
              let uu____4571 = p_lident x  in
              let uu____4572 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____4571 uu____4572  in
            let uu____4573 =
              let uu____4574 = p_noSeqTerm e1  in
              let uu____4575 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____4574 uu____4575  in
            op_Hat_Slash_Plus_Hat uu____4570 uu____4573  in
          FStar_Pprint.group uu____4569  in
        let uu____4576 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4568 uu____4576
    | uu____4577 ->
        let uu____4578 = p_noSeqTerm e  in FStar_Pprint.group uu____4578

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4581 =
      let uu____4582 = unparen e  in uu____4582.FStar_Parser_AST.tm  in
    match uu____4581 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4587 =
          let uu____4588 = p_tmIff e1  in
          let uu____4589 =
            let uu____4590 =
              let uu____4591 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4591  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4590  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4588 uu____4589  in
        FStar_Pprint.group uu____4587
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4597 =
          let uu____4598 = p_tmIff e1  in
          let uu____4599 =
            let uu____4600 =
              let uu____4601 =
                let uu____4602 = p_typ t  in
                let uu____4603 =
                  let uu____4604 = str "by"  in
                  let uu____4605 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4604 uu____4605  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4602 uu____4603  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4601  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4600  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4598 uu____4599  in
        FStar_Pprint.group uu____4597
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4606;_},e1::e2::e3::[])
        ->
        let uu____4612 =
          let uu____4613 =
            let uu____4614 =
              let uu____4615 = p_atomicTermNotQUident e1  in
              let uu____4616 =
                let uu____4617 =
                  let uu____4618 =
                    let uu____4619 = p_term e2  in
                    soft_parens_with_nesting uu____4619  in
                  let uu____4620 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4618 uu____4620  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4617  in
              FStar_Pprint.op_Hat_Hat uu____4615 uu____4616  in
            FStar_Pprint.group uu____4614  in
          let uu____4621 =
            let uu____4622 = p_noSeqTerm e3  in jump2 uu____4622  in
          FStar_Pprint.op_Hat_Hat uu____4613 uu____4621  in
        FStar_Pprint.group uu____4612
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4623;_},e1::e2::e3::[])
        ->
        let uu____4629 =
          let uu____4630 =
            let uu____4631 =
              let uu____4632 = p_atomicTermNotQUident e1  in
              let uu____4633 =
                let uu____4634 =
                  let uu____4635 =
                    let uu____4636 = p_term e2  in
                    soft_brackets_with_nesting uu____4636  in
                  let uu____4637 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4635 uu____4637  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4634  in
              FStar_Pprint.op_Hat_Hat uu____4632 uu____4633  in
            FStar_Pprint.group uu____4631  in
          let uu____4638 =
            let uu____4639 = p_noSeqTerm e3  in jump2 uu____4639  in
          FStar_Pprint.op_Hat_Hat uu____4630 uu____4638  in
        FStar_Pprint.group uu____4629
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4649 =
          let uu____4650 = str "requires"  in
          let uu____4651 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4650 uu____4651  in
        FStar_Pprint.group uu____4649
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4661 =
          let uu____4662 = str "ensures"  in
          let uu____4663 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4662 uu____4663  in
        FStar_Pprint.group uu____4661
    | FStar_Parser_AST.Attributes es ->
        let uu____4667 =
          let uu____4668 = str "attributes"  in
          let uu____4669 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4668 uu____4669  in
        FStar_Pprint.group uu____4667
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4673 = is_unit e3  in
        if uu____4673
        then
          let uu____4674 =
            let uu____4675 =
              let uu____4676 = str "if"  in
              let uu____4677 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4676 uu____4677  in
            let uu____4678 =
              let uu____4679 = str "then"  in
              let uu____4680 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4679 uu____4680  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4675 uu____4678  in
          FStar_Pprint.group uu____4674
        else
          (let e2_doc =
             let uu____4683 =
               let uu____4684 = unparen e2  in uu____4684.FStar_Parser_AST.tm
                in
             match uu____4683 with
             | FStar_Parser_AST.If (uu____4685,uu____4686,e31) when
                 is_unit e31 ->
                 let uu____4688 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4688
             | uu____4689 -> p_noSeqTerm e2  in
           let uu____4690 =
             let uu____4691 =
               let uu____4692 = str "if"  in
               let uu____4693 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4692 uu____4693  in
             let uu____4694 =
               let uu____4695 =
                 let uu____4696 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4696 e2_doc  in
               let uu____4697 =
                 let uu____4698 = str "else"  in
                 let uu____4699 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4698 uu____4699  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4695 uu____4697  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4691 uu____4694  in
           FStar_Pprint.group uu____4690)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4722 =
          let uu____4723 =
            let uu____4724 = str "try"  in
            let uu____4725 = p_noSeqTerm e1  in prefix2 uu____4724 uu____4725
             in
          let uu____4726 =
            let uu____4727 = str "with"  in
            let uu____4728 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4727 uu____4728  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4723 uu____4726  in
        FStar_Pprint.group uu____4722
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4759 =
          let uu____4760 =
            let uu____4761 = str "match"  in
            let uu____4762 = p_noSeqTerm e1  in
            let uu____4763 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4761 uu____4762 uu____4763
             in
          let uu____4764 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4760 uu____4764  in
        FStar_Pprint.group uu____4759
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4775 =
          let uu____4776 =
            let uu____4777 = str "let open"  in
            let uu____4778 = p_quident uid  in
            let uu____4779 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4777 uu____4778 uu____4779
             in
          let uu____4780 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4776 uu____4780  in
        FStar_Pprint.group uu____4775
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4797 = str "let"  in
          let uu____4798 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4797 uu____4798  in
        let uu____4799 =
          let uu____4800 =
            let uu____4801 =
              let uu____4802 = str "and"  in
              precede_break_separate_map let_doc uu____4802 p_letbinding lbs
               in
            let uu____4807 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4801 uu____4807  in
          FStar_Pprint.group uu____4800  in
        let uu____4808 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4799 uu____4808
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4811;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4814;
                                                         FStar_Parser_AST.level
                                                           = uu____4815;_})
        when matches_var maybe_x x ->
        let uu____4842 =
          let uu____4843 = str "function"  in
          let uu____4844 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4843 uu____4844  in
        FStar_Pprint.group uu____4842
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4855 =
          let uu____4856 = p_lident id1  in
          let uu____4857 =
            let uu____4858 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4858  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4856 uu____4857  in
        FStar_Pprint.group uu____4855
    | uu____4859 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4862 =
      let uu____4863 = unparen e  in uu____4863.FStar_Parser_AST.tm  in
    match uu____4862 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4879 =
          let uu____4880 =
            let uu____4881 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4881 FStar_Pprint.space  in
          let uu____4882 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4880 uu____4882 FStar_Pprint.dot
           in
        let uu____4883 =
          let uu____4884 = p_trigger trigger  in
          let uu____4885 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4884 uu____4885  in
        prefix2 uu____4879 uu____4883
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4901 =
          let uu____4902 =
            let uu____4903 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4903 FStar_Pprint.space  in
          let uu____4904 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4902 uu____4904 FStar_Pprint.dot
           in
        let uu____4905 =
          let uu____4906 = p_trigger trigger  in
          let uu____4907 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4906 uu____4907  in
        prefix2 uu____4901 uu____4905
    | uu____4908 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4910 =
      let uu____4911 = unparen e  in uu____4911.FStar_Parser_AST.tm  in
    match uu____4910 with
    | FStar_Parser_AST.QForall uu____4912 -> str "forall"
    | FStar_Parser_AST.QExists uu____4925 -> str "exists"
    | uu____4938 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___69_4939  ->
    match uu___69_4939 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4951 =
          let uu____4952 =
            let uu____4953 = str "pattern"  in
            let uu____4954 =
              let uu____4955 =
                let uu____4956 = p_disjunctivePats pats  in jump2 uu____4956
                 in
              let uu____4957 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4955 uu____4957  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4953 uu____4954  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4952  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4951

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4963 = str "\\/"  in
    FStar_Pprint.separate_map uu____4963 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4969 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4969

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4971 =
      let uu____4972 = unparen e  in uu____4972.FStar_Parser_AST.tm  in
    match uu____4971 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4979 =
          let uu____4980 = str "fun"  in
          let uu____4981 =
            let uu____4982 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4982 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4980 uu____4981  in
        let uu____4983 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4979 uu____4983
    | uu____4984 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4987  ->
    match uu____4987 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____5006 =
            let uu____5007 = unparen e  in uu____5007.FStar_Parser_AST.tm  in
          match uu____5006 with
          | FStar_Parser_AST.Match uu____5010 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____5025 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____5041);
                 FStar_Parser_AST.prange = uu____5042;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____5044);
                                                               FStar_Parser_AST.range
                                                                 = uu____5045;
                                                               FStar_Parser_AST.level
                                                                 = uu____5046;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____5073 -> (fun x  -> x)  in
        let uu____5075 =
          let uu____5076 =
            let uu____5077 =
              let uu____5078 =
                let uu____5079 =
                  let uu____5080 = p_disjunctivePattern pat  in
                  let uu____5081 =
                    let uu____5082 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____5082 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____5080 uu____5081  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5079  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5078  in
            FStar_Pprint.group uu____5077  in
          let uu____5083 =
            let uu____5084 = p_term e  in maybe_paren uu____5084  in
          op_Hat_Slash_Plus_Hat uu____5076 uu____5083  in
        FStar_Pprint.group uu____5075

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___70_5085  ->
    match uu___70_5085 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____5089 = str "when"  in
        let uu____5090 =
          let uu____5091 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5091 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____5089 uu____5090

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5093 =
      let uu____5094 = unparen e  in uu____5094.FStar_Parser_AST.tm  in
    match uu____5093 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5095;_},e1::e2::[])
        ->
        let uu____5100 = str "<==>"  in
        let uu____5101 = p_tmImplies e1  in
        let uu____5102 = p_tmIff e2  in
        infix0 uu____5100 uu____5101 uu____5102
    | uu____5103 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5105 =
      let uu____5106 = unparen e  in uu____5106.FStar_Parser_AST.tm  in
    match uu____5105 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5107;_},e1::e2::[])
        ->
        let uu____5112 = str "==>"  in
        let uu____5113 = p_tmArrow p_tmFormula e1  in
        let uu____5114 = p_tmImplies e2  in
        infix0 uu____5112 uu____5113 uu____5114
    | uu____5115 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____5120 =
        let uu____5121 = unparen e  in uu____5121.FStar_Parser_AST.tm  in
      match uu____5120 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5128 =
            let uu____5129 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5134 = p_binder false b  in
                   let uu____5135 =
                     let uu____5136 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5136
                      in
                   FStar_Pprint.op_Hat_Hat uu____5134 uu____5135) bs
               in
            let uu____5137 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5129 uu____5137  in
          FStar_Pprint.group uu____5128
      | uu____5138 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5140 =
      let uu____5141 = unparen e  in uu____5141.FStar_Parser_AST.tm  in
    match uu____5140 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5142;_},e1::e2::[])
        ->
        let uu____5147 = str "\\/"  in
        let uu____5148 = p_tmFormula e1  in
        let uu____5149 = p_tmConjunction e2  in
        infix0 uu____5147 uu____5148 uu____5149
    | uu____5150 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5152 =
      let uu____5153 = unparen e  in uu____5153.FStar_Parser_AST.tm  in
    match uu____5152 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5154;_},e1::e2::[])
        ->
        let uu____5159 = str "/\\"  in
        let uu____5160 = p_tmConjunction e1  in
        let uu____5161 = p_tmTuple e2  in
        infix0 uu____5159 uu____5160 uu____5161
    | uu____5162 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5165 =
      let uu____5166 = unparen e  in uu____5166.FStar_Parser_AST.tm  in
    match uu____5165 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5181 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5181
          (fun uu____5189  ->
             match uu____5189 with | (e1,uu____5195) -> p_tmEq e1) args
    | uu____5196 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5201 =
             let uu____5202 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5202  in
           FStar_Pprint.group uu____5201)

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append [colon_equals (); pipe_right ()]
           (operatorInfix0ad12 ()))
       in
    p_tmEq' n1 e

and p_tmEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5253 =
        let uu____5254 = unparen e  in uu____5254.FStar_Parser_AST.tm  in
      match uu____5253 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5261 = levels op1  in
          (match uu____5261 with
           | (left1,mine,right1) ->
               let uu____5271 =
                 let uu____5272 = FStar_All.pipe_left str op1  in
                 let uu____5273 = p_tmEq' left1 e1  in
                 let uu____5274 = p_tmEq' right1 e2  in
                 infix0 uu____5272 uu____5273 uu____5274  in
               paren_if curr mine uu____5271)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5275;_},e1::e2::[])
          ->
          let uu____5280 =
            let uu____5281 = p_tmEq e1  in
            let uu____5282 =
              let uu____5283 =
                let uu____5284 =
                  let uu____5285 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5285  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5284  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5283  in
            FStar_Pprint.op_Hat_Hat uu____5281 uu____5282  in
          FStar_Pprint.group uu____5280
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5286;_},e1::[])
          ->
          let uu____5290 = levels "-"  in
          (match uu____5290 with
           | (left1,mine,right1) ->
               let uu____5300 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5300)
      | uu____5301 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5364 =
        let uu____5365 = unparen e  in uu____5365.FStar_Parser_AST.tm  in
      match uu____5364 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5368)::(e2,uu____5370)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5390 = is_list e  in Prims.op_Negation uu____5390)
          ->
          let op = "::"  in
          let uu____5392 = levels op  in
          (match uu____5392 with
           | (left1,mine,right1) ->
               let uu____5402 =
                 let uu____5403 = str op  in
                 let uu____5404 = p_tmNoEq' left1 e1  in
                 let uu____5405 = p_tmNoEq' right1 e2  in
                 infix0 uu____5403 uu____5404 uu____5405  in
               paren_if curr mine uu____5402)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5413 = levels op  in
          (match uu____5413 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5427 = p_binder false b  in
                 let uu____5428 =
                   let uu____5429 =
                     let uu____5430 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5430 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5429  in
                 FStar_Pprint.op_Hat_Hat uu____5427 uu____5428  in
               let uu____5431 =
                 let uu____5432 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5433 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5432 uu____5433  in
               paren_if curr mine uu____5431)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5440 = levels op1  in
          (match uu____5440 with
           | (left1,mine,right1) ->
               let uu____5450 =
                 let uu____5451 = str op1  in
                 let uu____5452 = p_tmNoEq' left1 e1  in
                 let uu____5453 = p_tmNoEq' right1 e2  in
                 infix0 uu____5451 uu____5452 uu____5453  in
               paren_if curr mine uu____5450)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5456 =
            let uu____5457 = p_lidentOrUnderscore lid  in
            let uu____5458 =
              let uu____5459 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5459  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5457 uu____5458  in
          FStar_Pprint.group uu____5456
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5480 =
            let uu____5481 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5482 =
              let uu____5483 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____5483 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____5481 uu____5482  in
          braces_with_nesting uu____5480
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5488;_},e1::[])
          ->
          let uu____5492 =
            let uu____5493 = str "~"  in
            let uu____5494 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5493 uu____5494  in
          FStar_Pprint.group uu____5492
      | uu____5495 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5497 = p_appTerm e  in
    let uu____5498 =
      let uu____5499 =
        let uu____5500 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5500 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5499  in
    FStar_Pprint.op_Hat_Hat uu____5497 uu____5498

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5505 =
            let uu____5506 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5506 t phi  in
          soft_parens_with_nesting uu____5505
      | FStar_Parser_AST.TAnnotated uu____5507 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5512 ->
          let uu____5513 =
            let uu____5514 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5514
             in
          failwith uu____5513
      | FStar_Parser_AST.TVariable uu____5515 ->
          let uu____5516 =
            let uu____5517 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5517
             in
          failwith uu____5516
      | FStar_Parser_AST.NoName uu____5518 ->
          let uu____5519 =
            let uu____5520 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5520
             in
          failwith uu____5519

and p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5521  ->
    match uu____5521 with
    | (lid,e) ->
        let uu____5528 =
          let uu____5529 = p_qlident lid  in
          let uu____5530 =
            let uu____5531 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5531  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5529 uu____5530  in
        FStar_Pprint.group uu____5528

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5533 =
      let uu____5534 = unparen e  in uu____5534.FStar_Parser_AST.tm  in
    match uu____5533 with
    | FStar_Parser_AST.App uu____5535 when is_general_application e ->
        let uu____5542 = head_and_args e  in
        (match uu____5542 with
         | (head1,args) ->
             let uu____5567 =
               let uu____5578 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5578
               then
                 let uu____5637 =
                   FStar_Util.take
                     (fun uu____5661  ->
                        match uu____5661 with
                        | (uu____5666,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5637 with
                 | (fs_typ_args,args1) ->
                     let uu____5704 =
                       let uu____5705 = p_indexingTerm head1  in
                       let uu____5706 =
                         let uu____5707 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5707 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5705 uu____5706  in
                     (uu____5704, args1)
               else
                 (let uu____5719 = p_indexingTerm head1  in
                  (uu____5719, args))
                in
             (match uu____5567 with
              | (head_doc,args1) ->
                  let uu____5740 =
                    let uu____5741 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5741 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5740))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5761 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5761)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5779 =
               let uu____5780 = p_quident lid  in
               let uu____5781 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5780 uu____5781  in
             FStar_Pprint.group uu____5779
         | hd1::tl1 ->
             let uu____5798 =
               let uu____5799 =
                 let uu____5800 =
                   let uu____5801 = p_quident lid  in
                   let uu____5802 = p_argTerm hd1  in
                   prefix2 uu____5801 uu____5802  in
                 FStar_Pprint.group uu____5800  in
               let uu____5803 =
                 let uu____5804 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5804  in
               FStar_Pprint.op_Hat_Hat uu____5799 uu____5803  in
             FStar_Pprint.group uu____5798)
    | uu____5809 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Util.print_warning
           "Unexpected FsTypApp, output might not be formatted correctly.\n";
         (let uu____5818 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5818 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5820 = str "#"  in
        let uu____5821 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5820 uu____5821
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5823  ->
    match uu____5823 with | (e,uu____5829) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5834 =
        let uu____5835 = unparen e  in uu____5835.FStar_Parser_AST.tm  in
      match uu____5834 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5836;_},e1::e2::[])
          ->
          let uu____5841 =
            let uu____5842 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5843 =
              let uu____5844 =
                let uu____5845 = p_term e2  in
                soft_parens_with_nesting uu____5845  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5844  in
            FStar_Pprint.op_Hat_Hat uu____5842 uu____5843  in
          FStar_Pprint.group uu____5841
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5846;_},e1::e2::[])
          ->
          let uu____5851 =
            let uu____5852 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5853 =
              let uu____5854 =
                let uu____5855 = p_term e2  in
                soft_brackets_with_nesting uu____5855  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5854  in
            FStar_Pprint.op_Hat_Hat uu____5852 uu____5853  in
          FStar_Pprint.group uu____5851
      | uu____5856 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5859 =
      let uu____5860 = unparen e  in uu____5860.FStar_Parser_AST.tm  in
    match uu____5859 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5863 = p_quident lid  in
        let uu____5864 =
          let uu____5865 =
            let uu____5866 = p_term e1  in
            soft_parens_with_nesting uu____5866  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5865  in
        FStar_Pprint.op_Hat_Hat uu____5863 uu____5864
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5872 = str (FStar_Ident.text_of_id op)  in
        let uu____5873 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5872 uu____5873
    | uu____5874 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5876 =
      let uu____5877 = unparen e  in uu____5877.FStar_Parser_AST.tm  in
    match uu____5876 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5883 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5890 = str (FStar_Ident.text_of_id op)  in
        let uu____5891 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5890 uu____5891
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5895 =
          let uu____5896 =
            let uu____5897 = str (FStar_Ident.text_of_id op)  in
            let uu____5898 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5897 uu____5898  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5896  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5895
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5913 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5914 =
          let uu____5915 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5916 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5915 p_tmEq uu____5916  in
        let uu____5923 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5913 uu____5914 uu____5923
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5926 =
          let uu____5927 = p_atomicTermNotQUident e1  in
          let uu____5928 =
            let uu____5929 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5929  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5927 uu____5928
           in
        FStar_Pprint.group uu____5926
    | uu____5930 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5932 =
      let uu____5933 = unparen e  in uu____5933.FStar_Parser_AST.tm  in
    match uu____5932 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5937 = p_quident constr_lid  in
        let uu____5938 =
          let uu____5939 =
            let uu____5940 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5940  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5939  in
        FStar_Pprint.op_Hat_Hat uu____5937 uu____5938
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5942 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5942 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5944 = p_term e1  in soft_parens_with_nesting uu____5944
    | uu____5945 when is_array e ->
        let es = extract_from_list e  in
        let uu____5949 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5950 =
          let uu____5951 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5951 p_noSeqTerm es  in
        let uu____5952 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5949 uu____5950 uu____5952
    | uu____5953 when is_list e ->
        let uu____5954 =
          let uu____5955 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5956 = extract_from_list e  in
          separate_map_or_flow uu____5955 p_noSeqTerm uu____5956  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5954 FStar_Pprint.rbracket
    | uu____5959 when is_lex_list e ->
        let uu____5960 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5961 =
          let uu____5962 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5963 = extract_from_list e  in
          separate_map_or_flow uu____5962 p_noSeqTerm uu____5963  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5960 uu____5961 FStar_Pprint.rbracket
    | uu____5966 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5970 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5971 =
          let uu____5972 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5972 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5970 uu____5971 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5976 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5977 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5976 uu____5977
    | FStar_Parser_AST.Op (op,args) when
        let uu____5984 = handleable_op op args  in
        Prims.op_Negation uu____5984 ->
        let uu____5985 =
          let uu____5986 =
            let uu____5987 =
              let uu____5988 =
                let uu____5989 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5989
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5988  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5987  in
          Prims.strcat "Operation " uu____5986  in
        failwith uu____5985
    | FStar_Parser_AST.Uvar uu____5990 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5991 = p_term e  in soft_parens_with_nesting uu____5991
    | FStar_Parser_AST.Const uu____5992 ->
        let uu____5993 = p_term e  in soft_parens_with_nesting uu____5993
    | FStar_Parser_AST.Op uu____5994 ->
        let uu____6001 = p_term e  in soft_parens_with_nesting uu____6001
    | FStar_Parser_AST.Tvar uu____6002 ->
        let uu____6003 = p_term e  in soft_parens_with_nesting uu____6003
    | FStar_Parser_AST.Var uu____6004 ->
        let uu____6005 = p_term e  in soft_parens_with_nesting uu____6005
    | FStar_Parser_AST.Name uu____6006 ->
        let uu____6007 = p_term e  in soft_parens_with_nesting uu____6007
    | FStar_Parser_AST.Construct uu____6008 ->
        let uu____6019 = p_term e  in soft_parens_with_nesting uu____6019
    | FStar_Parser_AST.Abs uu____6020 ->
        let uu____6027 = p_term e  in soft_parens_with_nesting uu____6027
    | FStar_Parser_AST.App uu____6028 ->
        let uu____6035 = p_term e  in soft_parens_with_nesting uu____6035
    | FStar_Parser_AST.Let uu____6036 ->
        let uu____6049 = p_term e  in soft_parens_with_nesting uu____6049
    | FStar_Parser_AST.LetOpen uu____6050 ->
        let uu____6055 = p_term e  in soft_parens_with_nesting uu____6055
    | FStar_Parser_AST.Seq uu____6056 ->
        let uu____6061 = p_term e  in soft_parens_with_nesting uu____6061
    | FStar_Parser_AST.Bind uu____6062 ->
        let uu____6069 = p_term e  in soft_parens_with_nesting uu____6069
    | FStar_Parser_AST.If uu____6070 ->
        let uu____6077 = p_term e  in soft_parens_with_nesting uu____6077
    | FStar_Parser_AST.Match uu____6078 ->
        let uu____6093 = p_term e  in soft_parens_with_nesting uu____6093
    | FStar_Parser_AST.TryWith uu____6094 ->
        let uu____6109 = p_term e  in soft_parens_with_nesting uu____6109
    | FStar_Parser_AST.Ascribed uu____6110 ->
        let uu____6119 = p_term e  in soft_parens_with_nesting uu____6119
    | FStar_Parser_AST.Record uu____6120 ->
        let uu____6133 = p_term e  in soft_parens_with_nesting uu____6133
    | FStar_Parser_AST.Project uu____6134 ->
        let uu____6139 = p_term e  in soft_parens_with_nesting uu____6139
    | FStar_Parser_AST.Product uu____6140 ->
        let uu____6147 = p_term e  in soft_parens_with_nesting uu____6147
    | FStar_Parser_AST.Sum uu____6148 ->
        let uu____6155 = p_term e  in soft_parens_with_nesting uu____6155
    | FStar_Parser_AST.QForall uu____6156 ->
        let uu____6169 = p_term e  in soft_parens_with_nesting uu____6169
    | FStar_Parser_AST.QExists uu____6170 ->
        let uu____6183 = p_term e  in soft_parens_with_nesting uu____6183
    | FStar_Parser_AST.Refine uu____6184 ->
        let uu____6189 = p_term e  in soft_parens_with_nesting uu____6189
    | FStar_Parser_AST.NamedTyp uu____6190 ->
        let uu____6195 = p_term e  in soft_parens_with_nesting uu____6195
    | FStar_Parser_AST.Requires uu____6196 ->
        let uu____6203 = p_term e  in soft_parens_with_nesting uu____6203
    | FStar_Parser_AST.Ensures uu____6204 ->
        let uu____6211 = p_term e  in soft_parens_with_nesting uu____6211
    | FStar_Parser_AST.Assign uu____6212 ->
        let uu____6217 = p_term e  in soft_parens_with_nesting uu____6217
    | FStar_Parser_AST.Attributes uu____6218 ->
        let uu____6221 = p_term e  in soft_parens_with_nesting uu____6221

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___73_6222  ->
    match uu___73_6222 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6226 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6226
    | FStar_Const.Const_string (s,uu____6228) ->
        let uu____6229 = str s  in FStar_Pprint.dquotes uu____6229
    | FStar_Const.Const_bytearray (bytes,uu____6231) ->
        let uu____6236 =
          let uu____6237 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6237  in
        let uu____6238 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6236 uu____6238
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___71_6256 =
          match uu___71_6256 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___72_6260 =
          match uu___72_6260 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6271  ->
               match uu____6271 with
               | (s,w) ->
                   let uu____6278 = signedness s  in
                   let uu____6279 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6278 uu____6279)
            sign_width_opt
           in
        let uu____6280 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6280 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6282 = FStar_Range.string_of_range r  in str uu____6282
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6284 = p_quident lid  in
        let uu____6285 =
          let uu____6286 =
            let uu____6287 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6287  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6286  in
        FStar_Pprint.op_Hat_Hat uu____6284 uu____6285

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6289 = str "u#"  in
    let uu____6290 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6289 uu____6290

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6292 =
      let uu____6293 = unparen u  in uu____6293.FStar_Parser_AST.tm  in
    match uu____6292 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6294;_},u1::u2::[])
        ->
        let uu____6299 =
          let uu____6300 = p_universeFrom u1  in
          let uu____6301 =
            let uu____6302 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6302  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6300 uu____6301  in
        FStar_Pprint.group uu____6299
    | FStar_Parser_AST.App uu____6303 ->
        let uu____6310 = head_and_args u  in
        (match uu____6310 with
         | (head1,args) ->
             let uu____6335 =
               let uu____6336 = unparen head1  in
               uu____6336.FStar_Parser_AST.tm  in
             (match uu____6335 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6338 =
                    let uu____6339 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6340 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6348  ->
                           match uu____6348 with
                           | (u1,uu____6354) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6339 uu____6340  in
                  FStar_Pprint.group uu____6338
              | uu____6355 ->
                  let uu____6356 =
                    let uu____6357 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6357
                     in
                  failwith uu____6356))
    | uu____6358 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6360 =
      let uu____6361 = unparen u  in uu____6361.FStar_Parser_AST.tm  in
    match uu____6360 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6384 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6384
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6385;_},uu____6386::uu____6387::[])
        ->
        let uu____6390 = p_universeFrom u  in
        soft_parens_with_nesting uu____6390
    | FStar_Parser_AST.App uu____6391 ->
        let uu____6398 = p_universeFrom u  in
        soft_parens_with_nesting uu____6398
    | uu____6399 ->
        let uu____6400 =
          let uu____6401 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6401
           in
        failwith uu____6400

let term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e 
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
       | FStar_Parser_AST.Module (uu____6470,decls) ->
           let uu____6476 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6476
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6485,decls,uu____6487) ->
           let uu____6492 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6492
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6572  ->
         match uu____6572 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6612,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6618,decls,uu____6620) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6694 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6707;
                 FStar_Parser_AST.doc = uu____6708;
                 FStar_Parser_AST.quals = uu____6709;
                 FStar_Parser_AST.attrs = uu____6710;_}::uu____6711 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6717 =
                   let uu____6720 =
                     let uu____6723 = FStar_List.tl ds  in d :: uu____6723
                      in
                   d0 :: uu____6720  in
                 (uu____6717, (d0.FStar_Parser_AST.drange))
             | uu____6728 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6694 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6815 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6815 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6998 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6998, comments1))))))
  