open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
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
  
let should_unparen : Prims.bool FStar_ST.ref = FStar_Util.mk_ref true 
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____115 =
      let uu____116 = FStar_ST.op_Bang should_unparen  in
      Prims.op_Negation uu____116  in
    if uu____115
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____138 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____147 'Auu____148 .
    'Auu____148 ->
      ('Auu____147 -> 'Auu____148) ->
        'Auu____147 FStar_Pervasives_Native.option -> 'Auu____148
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
  'Auu____202 .
    FStar_Pprint.document ->
      ('Auu____202 -> FStar_Pprint.document) ->
        'Auu____202 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____224 =
          let uu____225 =
            let uu____226 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____226  in
          FStar_Pprint.separate_map uu____225 f l  in
        FStar_Pprint.group uu____224
  
let precede_break_separate_map :
  'Auu____232 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____232 -> FStar_Pprint.document) ->
          'Auu____232 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____258 =
            let uu____259 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____260 =
              let uu____261 = FStar_List.hd l  in
              FStar_All.pipe_right uu____261 f  in
            FStar_Pprint.precede uu____259 uu____260  in
          let uu____262 =
            let uu____263 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____269 =
                   let uu____270 =
                     let uu____271 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____271  in
                   FStar_Pprint.op_Hat_Hat sep uu____270  in
                 FStar_Pprint.op_Hat_Hat break1 uu____269) uu____263
             in
          FStar_Pprint.op_Hat_Hat uu____258 uu____262
  
let concat_break_map :
  'Auu____275 .
    ('Auu____275 -> FStar_Pprint.document) ->
      'Auu____275 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____293 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____297 = f x  in FStar_Pprint.op_Hat_Hat uu____297 break1)
          l
         in
      FStar_Pprint.group uu____293
  
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
    let uu____319 = str "begin"  in
    let uu____320 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____319 contents uu____320
  
let separate_map_or_flow :
  'Auu____325 .
    FStar_Pprint.document ->
      ('Auu____325 -> FStar_Pprint.document) ->
        'Auu____325 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____357 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____357 -> FStar_Pprint.document) ->
                  'Auu____357 Prims.list -> FStar_Pprint.document
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
                    (let uu____402 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____402
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____412 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____412 -> FStar_Pprint.document) ->
                  'Auu____412 Prims.list -> FStar_Pprint.document
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
                    (let uu____457 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____457
                       closing)
  
let doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____470  ->
    match uu____470 with
    | (comment,keywords) ->
        let uu____495 =
          let uu____496 =
            let uu____499 = str comment  in
            let uu____500 =
              let uu____503 =
                let uu____506 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____515  ->
                       match uu____515 with
                       | (k,v1) ->
                           let uu____522 =
                             let uu____525 = str k  in
                             let uu____526 =
                               let uu____529 =
                                 let uu____532 = str v1  in [uu____532]  in
                               FStar_Pprint.rarrow :: uu____529  in
                             uu____525 :: uu____526  in
                           FStar_Pprint.concat uu____522) keywords
                   in
                [uu____506]  in
              FStar_Pprint.space :: uu____503  in
            uu____499 :: uu____500  in
          FStar_Pprint.concat uu____496  in
        FStar_Pprint.group uu____495
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____536 =
      let uu____537 = unparen e  in uu____537.FStar_Parser_AST.tm  in
    match uu____536 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____538 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____545 =
        let uu____546 = unparen t  in uu____546.FStar_Parser_AST.tm  in
      match uu____545 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____548 -> false
  
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
        let uu____565 =
          let uu____566 = unparen e  in uu____566.FStar_Parser_AST.tm  in
        match uu____565 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____579::(e2,uu____581)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____604 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____614 =
      let uu____615 = unparen e  in uu____615.FStar_Parser_AST.tm  in
    match uu____614 with
    | FStar_Parser_AST.Construct (uu____618,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____629,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____650 = extract_from_list e2  in e1 :: uu____650
    | uu____653 ->
        let uu____654 =
          let uu____655 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____655  in
        failwith uu____654
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____661 =
      let uu____662 = unparen e  in uu____662.FStar_Parser_AST.tm  in
    match uu____661 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____664;
           FStar_Parser_AST.level = uu____665;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____667 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____671 =
      let uu____672 = unparen e  in uu____672.FStar_Parser_AST.tm  in
    match uu____671 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____675;
           FStar_Parser_AST.level = uu____676;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____678;
                                                        FStar_Parser_AST.level
                                                          = uu____679;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____681;
                                                   FStar_Parser_AST.level =
                                                     uu____682;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____684;
                FStar_Parser_AST.level = uu____685;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____687;
           FStar_Parser_AST.level = uu____688;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____690 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____696 =
      let uu____697 = unparen e  in uu____697.FStar_Parser_AST.tm  in
    match uu____696 with
    | FStar_Parser_AST.Var uu____700 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____701;
           FStar_Parser_AST.range = uu____702;
           FStar_Parser_AST.level = uu____703;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____704;
                                                        FStar_Parser_AST.range
                                                          = uu____705;
                                                        FStar_Parser_AST.level
                                                          = uu____706;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____708;
                                                   FStar_Parser_AST.level =
                                                     uu____709;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____710;
                FStar_Parser_AST.range = uu____711;
                FStar_Parser_AST.level = uu____712;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____714;
           FStar_Parser_AST.level = uu____715;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____717 = extract_from_ref_set e1  in
        let uu____720 = extract_from_ref_set e2  in
        FStar_List.append uu____717 uu____720
    | uu____723 ->
        let uu____724 =
          let uu____725 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____725  in
        failwith uu____724
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____731 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____731
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____735 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____735
  
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
      let uu____785 =
        let uu____786 = unparen e1  in uu____786.FStar_Parser_AST.tm  in
      match uu____785 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____804 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____818 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____822 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____826 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___51_844  ->
    match uu___51_844 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___52_861  ->
      match uu___52_861 with
      | FStar_Util.Inl c ->
          let uu____870 = FStar_String.get s (Prims.parse_int "0")  in
          uu____870 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____878 .
    Prims.string ->
      ('Auu____878,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____897  ->
      match uu____897 with
      | (assoc_levels,tokens) ->
          let uu____925 = FStar_List.tryFind (matches_token s) tokens  in
          uu____925 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____951 .
    Prims.unit ->
      (associativity,('Auu____951,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____962  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____978 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____978) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____990  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1025 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1025) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1037  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1065 .
    Prims.unit ->
      (associativity,('Auu____1065,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1076  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1092 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1092) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1104  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1132 .
    Prims.unit ->
      (associativity,('Auu____1132,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1143  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1159 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1159) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1171  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1192 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1192) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1204  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1239 .
    Prims.unit ->
      (associativity,('Auu____1239,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1250  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1266 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1266) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1278  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1299 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1299) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1311  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1332 .
    Prims.unit ->
      (associativity,('Auu____1332,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1343  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1359 .
    Prims.unit ->
      (associativity,('Auu____1359,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1370  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1386 .
    Prims.unit ->
      (associativity,('Auu____1386,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1397  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___53_1604 =
    match uu___53_1604 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1644  ->
         match uu____1644 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1724 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1724 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1774) ->
          assoc_levels
      | uu____1818 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1853 .
    ('Auu____1853,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1913 =
        FStar_List.tryFind
          (fun uu____1953  ->
             match uu____1953 with
             | (uu____1971,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1913 with
      | FStar_Pervasives_Native.Some ((uu____2013,l1,uu____2015),uu____2016)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2071 =
            let uu____2072 =
              let uu____2073 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2073  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2072
             in
          failwith uu____2071
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____2107 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2107) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2121  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2202 =
      let uu____2216 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2216 (operatorInfix0ad12 ())  in
    uu____2202 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2329 =
      let uu____2343 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2343 opinfix34  in
    uu____2329 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2409 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2409
    then (Prims.parse_int "1")
    else
      (let uu____2411 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2411
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2417 . FStar_Ident.ident -> 'Auu____2417 Prims.list -> Prims.bool =
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
      | uu____2430 -> false
  
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2464 .
    ('Auu____2464 -> FStar_Pprint.document) ->
      'Auu____2464 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2496 = FStar_ST.op_Bang comment_stack  in
          match uu____2496 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2555 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2555
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2592 =
                    let uu____2593 =
                      let uu____2594 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2594
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2593  in
                  comments_before_pos uu____2592 print_pos lookahead_pos))
              else
                (let uu____2596 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2596))
           in
        let uu____2597 =
          let uu____2602 =
            let uu____2603 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2603  in
          let uu____2604 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2602 uu____2604  in
        match uu____2597 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2610 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2610
              else comments  in
            let uu____2616 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2616
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2629 = FStar_ST.op_Bang comment_stack  in
          match uu____2629 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2713 =
                    let uu____2714 =
                      let uu____2715 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2715  in
                    uu____2714 - lbegin  in
                  max k uu____2713  in
                let doc2 =
                  let uu____2717 =
                    let uu____2718 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2719 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2718 uu____2719  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2717  in
                let uu____2720 =
                  let uu____2721 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2721  in
                place_comments_until_pos (Prims.parse_int "1") uu____2720
                  pos_end doc2))
          | uu____2722 ->
              let lnum =
                let uu____2730 =
                  let uu____2731 = FStar_Range.line_of_pos pos_end  in
                  uu____2731 - lbegin  in
                max (Prims.parse_int "1") uu____2730  in
              let uu____2732 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2732
  
let separate_map_with_comments :
  'Auu____2739 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2739 -> FStar_Pprint.document) ->
          'Auu____2739 Prims.list ->
            ('Auu____2739 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2787 x =
              match uu____2787 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2801 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2801 doc1
                     in
                  let uu____2802 =
                    let uu____2803 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2803  in
                  let uu____2804 =
                    let uu____2805 =
                      let uu____2806 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2806  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2805  in
                  (uu____2802, uu____2804)
               in
            let uu____2807 =
              let uu____2814 = FStar_List.hd xs  in
              let uu____2815 = FStar_List.tl xs  in (uu____2814, uu____2815)
               in
            match uu____2807 with
            | (x,xs1) ->
                let init1 =
                  let uu____2831 =
                    let uu____2832 =
                      let uu____2833 = extract_range x  in
                      FStar_Range.end_of_range uu____2833  in
                    FStar_Range.line_of_pos uu____2832  in
                  let uu____2834 =
                    let uu____2835 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2835  in
                  (uu____2831, uu____2834)  in
                let uu____2836 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2836
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3151 =
      let uu____3152 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3153 =
        let uu____3154 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3155 =
          let uu____3156 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3157 =
            let uu____3158 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3158
             in
          FStar_Pprint.op_Hat_Hat uu____3156 uu____3157  in
        FStar_Pprint.op_Hat_Hat uu____3154 uu____3155  in
      FStar_Pprint.op_Hat_Hat uu____3152 uu____3153  in
    FStar_Pprint.group uu____3151

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3161 =
      let uu____3162 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3162  in
    let uu____3163 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3161 FStar_Pprint.space uu____3163
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3164  ->
    match uu____3164 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3198 =
                match uu____3198 with
                | (kwd,arg) ->
                    let uu____3205 = str "@"  in
                    let uu____3206 =
                      let uu____3207 = str kwd  in
                      let uu____3208 =
                        let uu____3209 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3209
                         in
                      FStar_Pprint.op_Hat_Hat uu____3207 uu____3208  in
                    FStar_Pprint.op_Hat_Hat uu____3205 uu____3206
                 in
              let uu____3210 =
                let uu____3211 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3211 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3210
           in
        let uu____3216 =
          let uu____3217 =
            let uu____3218 =
              let uu____3219 =
                let uu____3220 = str doc1  in
                let uu____3221 =
                  let uu____3222 =
                    let uu____3223 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3223  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3222  in
                FStar_Pprint.op_Hat_Hat uu____3220 uu____3221  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3219  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3218  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3217  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3216

and p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3227 =
          let uu____3228 = str "val"  in
          let uu____3229 =
            let uu____3230 =
              let uu____3231 = p_lident lid  in
              let uu____3232 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3231 uu____3232  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3230  in
          FStar_Pprint.op_Hat_Hat uu____3228 uu____3229  in
        let uu____3233 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3227 uu____3233
    | FStar_Parser_AST.TopLevelLet (uu____3234,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3259 =
               let uu____3260 = str "let"  in
               let uu____3261 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3260 uu____3261  in
             FStar_Pprint.group uu____3259) lbs
    | uu____3262 -> FStar_Pprint.empty

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3265 =
          let uu____3266 = str "open"  in
          let uu____3267 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3266 uu____3267  in
        FStar_Pprint.group uu____3265
    | FStar_Parser_AST.Include uid ->
        let uu____3269 =
          let uu____3270 = str "include"  in
          let uu____3271 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3270 uu____3271  in
        FStar_Pprint.group uu____3269
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3274 =
          let uu____3275 = str "module"  in
          let uu____3276 =
            let uu____3277 =
              let uu____3278 = p_uident uid1  in
              let uu____3279 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3278 uu____3279  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3277  in
          FStar_Pprint.op_Hat_Hat uu____3275 uu____3276  in
        let uu____3280 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3274 uu____3280
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3282 =
          let uu____3283 = str "module"  in
          let uu____3284 =
            let uu____3285 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3285  in
          FStar_Pprint.op_Hat_Hat uu____3283 uu____3284  in
        FStar_Pprint.group uu____3282
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3318 = str "effect"  in
          let uu____3319 =
            let uu____3320 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3320  in
          FStar_Pprint.op_Hat_Hat uu____3318 uu____3319  in
        let uu____3321 =
          let uu____3322 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3322 FStar_Pprint.equals
           in
        let uu____3323 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3321 uu____3323
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3341 = str "type"  in
        let uu____3342 = str "and"  in
        precede_break_separate_map uu____3341 uu____3342 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3364 = str "let"  in
          let uu____3365 =
            let uu____3366 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3366 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3364 uu____3365  in
        let uu____3367 =
          let uu____3368 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3368 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3367 p_letbinding lbs
          (fun uu____3376  ->
             match uu____3376 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3385 =
          let uu____3386 = str "val"  in
          let uu____3387 =
            let uu____3388 =
              let uu____3389 = p_lident lid  in
              let uu____3390 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3389 uu____3390  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3388  in
          FStar_Pprint.op_Hat_Hat uu____3386 uu____3387  in
        let uu____3391 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3385 uu____3391
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3395 =
            let uu____3396 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3396 FStar_Util.is_upper  in
          if uu____3395
          then FStar_Pprint.empty
          else
            (let uu____3398 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3398 FStar_Pprint.space)
           in
        let uu____3399 =
          let uu____3400 =
            let uu____3401 = p_ident id1  in
            let uu____3402 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3401 uu____3402  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3400  in
        let uu____3403 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3399 uu____3403
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3410 = str "exception"  in
        let uu____3411 =
          let uu____3412 =
            let uu____3413 = p_uident uid  in
            let uu____3414 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3419 = str "of"  in
                   let uu____3420 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3419 uu____3420) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3413 uu____3414  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3412  in
        FStar_Pprint.op_Hat_Hat uu____3410 uu____3411
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3422 = str "new_effect"  in
        let uu____3423 =
          let uu____3424 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3424  in
        FStar_Pprint.op_Hat_Hat uu____3422 uu____3423
    | FStar_Parser_AST.SubEffect se ->
        let uu____3426 = str "sub_effect"  in
        let uu____3427 =
          let uu____3428 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3428  in
        FStar_Pprint.op_Hat_Hat uu____3426 uu____3427
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3431 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3431 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3432 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3433) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___54_3450  ->
    match uu___54_3450 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3452 = str "#set-options"  in
        let uu____3453 =
          let uu____3454 =
            let uu____3455 = str s  in FStar_Pprint.dquotes uu____3455  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3454  in
        FStar_Pprint.op_Hat_Hat uu____3452 uu____3453
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3459 = str "#reset-options"  in
        let uu____3460 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3464 =
                 let uu____3465 = str s  in FStar_Pprint.dquotes uu____3465
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3464) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3459 uu____3460
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
  fun uu____3489  ->
    match uu____3489 with
    | (typedecl,fsdoc_opt) ->
        let uu____3502 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3503 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3502 uu____3503

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___55_3504  ->
    match uu___55_3504 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3519 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3535 =
          let uu____3536 = p_typ t  in prefix2 FStar_Pprint.equals uu____3536
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3580 =
          match uu____3580 with
          | (lid1,t,doc_opt) ->
              let uu____3596 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3596
           in
        let p_fields uu____3610 =
          let uu____3611 =
            let uu____3612 =
              let uu____3613 =
                let uu____3614 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3614 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3613  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3612  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3611  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3678 =
          match uu____3678 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3704 =
                  let uu____3705 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3705  in
                FStar_Range.extend_to_end_of_line uu____3704  in
              let p_constructorBranch decl =
                let uu____3738 =
                  let uu____3739 =
                    let uu____3740 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3740  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3739  in
                FStar_Pprint.group uu____3738  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3760 =
          let uu____3761 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3761  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3776  ->
             let uu____3777 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3777)

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
            let uu____3792 = p_ident lid  in
            let uu____3793 =
              let uu____3794 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3794  in
            FStar_Pprint.op_Hat_Hat uu____3792 uu____3793
          else
            (let binders_doc =
               let uu____3797 = p_typars bs  in
               let uu____3798 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3802 =
                        let uu____3803 =
                          let uu____3804 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3804
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3803
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3802) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3797 uu____3798  in
             let uu____3805 = p_ident lid  in
             let uu____3806 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3805 binders_doc uu____3806)

and p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3807  ->
    match uu____3807 with
    | (lid,t,doc_opt) ->
        let uu____3823 =
          let uu____3824 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____3825 =
            let uu____3826 = p_lident lid  in
            let uu____3827 =
              let uu____3828 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3828  in
            FStar_Pprint.op_Hat_Hat uu____3826 uu____3827  in
          FStar_Pprint.op_Hat_Hat uu____3824 uu____3825  in
        FStar_Pprint.group uu____3823

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3829  ->
    match uu____3829 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3857 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3858 =
          let uu____3859 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3860 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3865 =
                   let uu____3866 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3866  in
                 let uu____3867 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____3865 uu____3867) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3859 uu____3860  in
        FStar_Pprint.op_Hat_Hat uu____3857 uu____3858

and p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3868  ->
    match uu____3868 with
    | (pat,uu____3874) ->
        let uu____3875 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3886 =
                let uu____3887 =
                  let uu____3888 =
                    let uu____3889 =
                      let uu____3890 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3890
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3889  in
                  FStar_Pprint.group uu____3888  in
                FStar_Pprint.op_Hat_Hat break1 uu____3887  in
              (pat1, uu____3886)
          | uu____3891 -> (pat, FStar_Pprint.empty)  in
        (match uu____3875 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3895);
                     FStar_Parser_AST.prange = uu____3896;_},pats)
                  ->
                  let uu____3906 =
                    let uu____3907 = p_lident x  in
                    let uu____3908 =
                      let uu____3909 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____3909 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3907 uu____3908  in
                  FStar_Pprint.group uu____3906
              | uu____3910 ->
                  let uu____3911 =
                    let uu____3912 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____3912 ascr_doc  in
                  FStar_Pprint.group uu____3911))

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3913  ->
    match uu____3913 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____3921 =
          let uu____3922 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____3922  in
        let uu____3923 = p_term e  in prefix2 uu____3921 uu____3923

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___56_3924  ->
    match uu___56_3924 with
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
        let uu____3949 = p_uident uid  in
        let uu____3950 = p_binders true bs  in
        let uu____3951 =
          let uu____3952 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____3952  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3949 uu____3950 uu____3951

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
          let uu____3961 =
            let uu____3962 =
              let uu____3963 =
                let uu____3964 = p_uident uid  in
                let uu____3965 = p_binders true bs  in
                let uu____3966 =
                  let uu____3967 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____3967  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3964 uu____3965 uu____3966
                 in
              FStar_Pprint.group uu____3963  in
            let uu____3968 =
              let uu____3969 = str "with"  in
              let uu____3970 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____3969 uu____3970  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3962 uu____3968  in
          braces_with_nesting uu____3961

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4000 =
          let uu____4001 = p_lident lid  in
          let uu____4002 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____4001 uu____4002  in
        let uu____4003 = p_simpleTerm e  in prefix2 uu____4000 uu____4003
    | uu____4004 ->
        let uu____4005 =
          let uu____4006 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4006
           in
        failwith uu____4005

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____4061 =
        match uu____4061 with
        | (kwd,t) ->
            let uu____4068 =
              let uu____4069 = str kwd  in
              let uu____4070 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4069 uu____4070  in
            let uu____4071 = p_simpleTerm t  in prefix2 uu____4068 uu____4071
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____4076 =
      let uu____4077 =
        let uu____4078 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4079 =
          let uu____4080 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4080  in
        FStar_Pprint.op_Hat_Hat uu____4078 uu____4079  in
      let uu____4081 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4077 uu____4081  in
    let uu____4082 =
      let uu____4083 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4083  in
    FStar_Pprint.op_Hat_Hat uu____4076 uu____4082

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___57_4084  ->
    match uu___57_4084 with
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
    let uu____4086 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4086

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___58_4087  ->
    match uu___58_4087 with
    | FStar_Parser_AST.Rec  ->
        let uu____4088 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4088
    | FStar_Parser_AST.Mutable  ->
        let uu____4089 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4089
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___59_4090  ->
    match uu___59_4090 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4095 =
          let uu____4096 =
            let uu____4097 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4097  in
          FStar_Pprint.separate_map uu____4096 p_tuplePattern pats  in
        FStar_Pprint.group uu____4095
    | uu____4098 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4105 =
          let uu____4106 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4106 p_constructorPattern pats  in
        FStar_Pprint.group uu____4105
    | uu____4107 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4110;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4115 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4116 = p_constructorPattern hd1  in
        let uu____4117 = p_constructorPattern tl1  in
        infix0 uu____4115 uu____4116 uu____4117
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4119;_},pats)
        ->
        let uu____4125 = p_quident uid  in
        let uu____4126 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4125 uu____4126
    | uu____4127 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4131 =
          let uu____4136 =
            let uu____4137 = unparen t  in uu____4137.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____4136)  in
        (match uu____4131 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4142;
               FStar_Parser_AST.blevel = uu____4143;
               FStar_Parser_AST.aqual = uu____4144;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4150 =
               let uu____4151 = p_ident lid  in
               p_refinement aqual uu____4151 t1 phi  in
             soft_parens_with_nesting uu____4150
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4153;
               FStar_Parser_AST.blevel = uu____4154;
               FStar_Parser_AST.aqual = uu____4155;_},phi))
             ->
             let uu____4157 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4157
         | uu____4158 ->
             let uu____4163 =
               let uu____4164 = p_tuplePattern pat  in
               let uu____4165 =
                 let uu____4166 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4167 =
                   let uu____4168 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4168  in
                 FStar_Pprint.op_Hat_Hat uu____4166 uu____4167  in
               FStar_Pprint.op_Hat_Hat uu____4164 uu____4165  in
             soft_parens_with_nesting uu____4163)
    | FStar_Parser_AST.PatList pats ->
        let uu____4172 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4172 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4187 =
          match uu____4187 with
          | (lid,pat) ->
              let uu____4194 = p_qlident lid  in
              let uu____4195 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4194 uu____4195
           in
        let uu____4196 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4196
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4206 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4207 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4208 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4206 uu____4207 uu____4208
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4219 =
          let uu____4220 =
            let uu____4221 = str (FStar_Ident.text_of_id op)  in
            let uu____4222 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4221 uu____4222  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4220  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4219
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4230 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4231 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4230 uu____4231
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4233 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4236;
           FStar_Parser_AST.prange = uu____4237;_},uu____4238)
        ->
        let uu____4243 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4243
    | FStar_Parser_AST.PatTuple (uu____4244,false ) ->
        let uu____4249 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4249
    | uu____4250 ->
        let uu____4251 =
          let uu____4252 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4252  in
        failwith uu____4251

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4256 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4257 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4256 uu____4257
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4262 =
              let uu____4263 = unparen t  in uu____4263.FStar_Parser_AST.tm
               in
            match uu____4262 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4266;
                   FStar_Parser_AST.blevel = uu____4267;
                   FStar_Parser_AST.aqual = uu____4268;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4270 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4270 t1 phi
            | uu____4271 ->
                let uu____4272 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4273 =
                  let uu____4274 = p_lident lid  in
                  let uu____4275 =
                    let uu____4276 =
                      let uu____4277 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4278 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4277 uu____4278  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4276  in
                  FStar_Pprint.op_Hat_Hat uu____4274 uu____4275  in
                FStar_Pprint.op_Hat_Hat uu____4272 uu____4273
             in
          if is_atomic
          then
            let uu____4279 =
              let uu____4280 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4280  in
            FStar_Pprint.group uu____4279
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4282 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4288 =
            let uu____4289 = unparen t  in uu____4289.FStar_Parser_AST.tm  in
          (match uu____4288 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4291;
                  FStar_Parser_AST.blevel = uu____4292;
                  FStar_Parser_AST.aqual = uu____4293;_},phi)
               ->
               if is_atomic
               then
                 let uu____4295 =
                   let uu____4296 =
                     let uu____4297 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4297 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4296  in
                 FStar_Pprint.group uu____4295
               else
                 (let uu____4299 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4299)
           | uu____4300 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4308 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4309 =
            let uu____4310 =
              let uu____4311 =
                let uu____4312 = p_appTerm t  in
                let uu____4313 =
                  let uu____4314 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____4314  in
                FStar_Pprint.op_Hat_Hat uu____4312 uu____4313  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4311  in
            FStar_Pprint.op_Hat_Hat binder uu____4310  in
          FStar_Pprint.op_Hat_Hat uu____4308 uu____4309

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
    let uu____4328 =
      let uu____4329 = unparen e  in uu____4329.FStar_Parser_AST.tm  in
    match uu____4328 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4332 =
          let uu____4333 =
            let uu____4334 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4334 FStar_Pprint.semi  in
          FStar_Pprint.group uu____4333  in
        let uu____4335 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4332 uu____4335
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4339 =
          let uu____4340 =
            let uu____4341 =
              let uu____4342 = p_lident x  in
              let uu____4343 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____4342 uu____4343  in
            let uu____4344 =
              let uu____4345 = p_noSeqTerm e1  in
              let uu____4346 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____4345 uu____4346  in
            op_Hat_Slash_Plus_Hat uu____4341 uu____4344  in
          FStar_Pprint.group uu____4340  in
        let uu____4347 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4339 uu____4347
    | uu____4348 ->
        let uu____4349 = p_noSeqTerm e  in FStar_Pprint.group uu____4349

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4352 =
      let uu____4353 = unparen e  in uu____4353.FStar_Parser_AST.tm  in
    match uu____4352 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4358 =
          let uu____4359 = p_tmIff e1  in
          let uu____4360 =
            let uu____4361 =
              let uu____4362 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4362  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4361  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4359 uu____4360  in
        FStar_Pprint.group uu____4358
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4368 =
          let uu____4369 = p_tmIff e1  in
          let uu____4370 =
            let uu____4371 =
              let uu____4372 =
                let uu____4373 = p_typ t  in
                let uu____4374 =
                  let uu____4375 = str "by"  in
                  let uu____4376 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4375 uu____4376  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4373 uu____4374  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4372  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4371  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4369 uu____4370  in
        FStar_Pprint.group uu____4368
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4377;_},e1::e2::e3::[])
        ->
        let uu____4383 =
          let uu____4384 =
            let uu____4385 =
              let uu____4386 = p_atomicTermNotQUident e1  in
              let uu____4387 =
                let uu____4388 =
                  let uu____4389 =
                    let uu____4390 = p_term e2  in
                    soft_parens_with_nesting uu____4390  in
                  let uu____4391 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4389 uu____4391  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4388  in
              FStar_Pprint.op_Hat_Hat uu____4386 uu____4387  in
            FStar_Pprint.group uu____4385  in
          let uu____4392 =
            let uu____4393 = p_noSeqTerm e3  in jump2 uu____4393  in
          FStar_Pprint.op_Hat_Hat uu____4384 uu____4392  in
        FStar_Pprint.group uu____4383
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4394;_},e1::e2::e3::[])
        ->
        let uu____4400 =
          let uu____4401 =
            let uu____4402 =
              let uu____4403 = p_atomicTermNotQUident e1  in
              let uu____4404 =
                let uu____4405 =
                  let uu____4406 =
                    let uu____4407 = p_term e2  in
                    soft_brackets_with_nesting uu____4407  in
                  let uu____4408 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4406 uu____4408  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4405  in
              FStar_Pprint.op_Hat_Hat uu____4403 uu____4404  in
            FStar_Pprint.group uu____4402  in
          let uu____4409 =
            let uu____4410 = p_noSeqTerm e3  in jump2 uu____4410  in
          FStar_Pprint.op_Hat_Hat uu____4401 uu____4409  in
        FStar_Pprint.group uu____4400
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4420 =
          let uu____4421 = str "requires"  in
          let uu____4422 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4421 uu____4422  in
        FStar_Pprint.group uu____4420
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4432 =
          let uu____4433 = str "ensures"  in
          let uu____4434 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4433 uu____4434  in
        FStar_Pprint.group uu____4432
    | FStar_Parser_AST.Attributes es ->
        let uu____4438 =
          let uu____4439 = str "attributes"  in
          let uu____4440 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4439 uu____4440  in
        FStar_Pprint.group uu____4438
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4444 = is_unit e3  in
        if uu____4444
        then
          let uu____4445 =
            let uu____4446 =
              let uu____4447 = str "if"  in
              let uu____4448 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4447 uu____4448  in
            let uu____4449 =
              let uu____4450 = str "then"  in
              let uu____4451 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4450 uu____4451  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4446 uu____4449  in
          FStar_Pprint.group uu____4445
        else
          (let e2_doc =
             let uu____4454 =
               let uu____4455 = unparen e2  in uu____4455.FStar_Parser_AST.tm
                in
             match uu____4454 with
             | FStar_Parser_AST.If (uu____4456,uu____4457,e31) when
                 is_unit e31 ->
                 let uu____4459 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4459
             | uu____4460 -> p_noSeqTerm e2  in
           let uu____4461 =
             let uu____4462 =
               let uu____4463 = str "if"  in
               let uu____4464 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4463 uu____4464  in
             let uu____4465 =
               let uu____4466 =
                 let uu____4467 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4467 e2_doc  in
               let uu____4468 =
                 let uu____4469 = str "else"  in
                 let uu____4470 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4469 uu____4470  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4466 uu____4468  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4462 uu____4465  in
           FStar_Pprint.group uu____4461)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4493 =
          let uu____4494 =
            let uu____4495 = str "try"  in
            let uu____4496 = p_noSeqTerm e1  in prefix2 uu____4495 uu____4496
             in
          let uu____4497 =
            let uu____4498 = str "with"  in
            let uu____4499 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4498 uu____4499  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4494 uu____4497  in
        FStar_Pprint.group uu____4493
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4530 =
          let uu____4531 =
            let uu____4532 = str "match"  in
            let uu____4533 = p_noSeqTerm e1  in
            let uu____4534 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4532 uu____4533 uu____4534
             in
          let uu____4535 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4531 uu____4535  in
        FStar_Pprint.group uu____4530
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4546 =
          let uu____4547 =
            let uu____4548 = str "let open"  in
            let uu____4549 = p_quident uid  in
            let uu____4550 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4548 uu____4549 uu____4550
             in
          let uu____4551 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4547 uu____4551  in
        FStar_Pprint.group uu____4546
    | FStar_Parser_AST.Let (q,(a0,lb0)::attr_letbindings,e1) ->
        let let_first =
          let uu____4614 = p_attrs_opt a0  in
          let uu____4615 =
            let uu____4616 =
              let uu____4617 = str "let"  in
              let uu____4618 =
                let uu____4619 = p_letqualifier q  in
                let uu____4620 = p_letbinding lb0  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4619 uu____4620  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4617 uu____4618  in
            FStar_Pprint.group uu____4616  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4614 uu____4615  in
        let let_rest =
          match attr_letbindings with
          | [] -> FStar_Pprint.empty
          | uu____4634 ->
              let uu____4649 =
                precede_break_separate_map FStar_Pprint.empty
                  FStar_Pprint.empty p_attr_letbinding attr_letbindings
                 in
              FStar_Pprint.group uu____4649
           in
        let uu____4662 =
          let uu____4663 =
            let uu____4664 = str "in"  in
            let uu____4665 = p_term e1  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4664 uu____4665  in
          FStar_Pprint.op_Hat_Slash_Hat let_rest uu____4663  in
        FStar_Pprint.op_Hat_Slash_Hat let_first uu____4662
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4668;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4671;
                                                         FStar_Parser_AST.level
                                                           = uu____4672;_})
        when matches_var maybe_x x ->
        let uu____4699 =
          let uu____4700 = str "function"  in
          let uu____4701 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4700 uu____4701  in
        FStar_Pprint.group uu____4699
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4712 =
          let uu____4713 = p_lident id1  in
          let uu____4714 =
            let uu____4715 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4715  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4713 uu____4714  in
        FStar_Pprint.group uu____4712
    | uu____4716 -> p_typ e

and p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___60_4717  ->
    match uu___60_4717 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____4729 =
          let uu____4730 = str "[@"  in
          let uu____4731 =
            let uu____4732 =
              FStar_Pprint.separate_map FStar_Pprint.semi p_term terms  in
            let uu____4733 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4732 uu____4733  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4730 uu____4731  in
        FStar_Pprint.group uu____4729

and p_attr_letbinding :
  (FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option,(FStar_Parser_AST.pattern,
                                                                    FStar_Parser_AST.term)
                                                                    FStar_Pervasives_Native.tuple2)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____4734  ->
    match uu____4734 with
    | (a,(pat,e)) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4763 =
          let uu____4764 = p_attrs_opt a  in
          let uu____4765 =
            let uu____4766 =
              let uu____4767 = str "and "  in
              let uu____4768 =
                FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4767 uu____4768  in
            FStar_Pprint.group uu____4766  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4764 uu____4765  in
        let uu____4769 = p_term e  in prefix2 uu____4763 uu____4769

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4772 =
      let uu____4773 = unparen e  in uu____4773.FStar_Parser_AST.tm  in
    match uu____4772 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4789 =
          let uu____4790 =
            let uu____4791 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4791 FStar_Pprint.space  in
          let uu____4792 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4790 uu____4792 FStar_Pprint.dot
           in
        let uu____4793 =
          let uu____4794 = p_trigger trigger  in
          let uu____4795 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4794 uu____4795  in
        prefix2 uu____4789 uu____4793
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4811 =
          let uu____4812 =
            let uu____4813 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4813 FStar_Pprint.space  in
          let uu____4814 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4812 uu____4814 FStar_Pprint.dot
           in
        let uu____4815 =
          let uu____4816 = p_trigger trigger  in
          let uu____4817 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4816 uu____4817  in
        prefix2 uu____4811 uu____4815
    | uu____4818 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4820 =
      let uu____4821 = unparen e  in uu____4821.FStar_Parser_AST.tm  in
    match uu____4820 with
    | FStar_Parser_AST.QForall uu____4822 -> str "forall"
    | FStar_Parser_AST.QExists uu____4835 -> str "exists"
    | uu____4848 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___61_4849  ->
    match uu___61_4849 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4861 =
          let uu____4862 =
            let uu____4863 = str "pattern"  in
            let uu____4864 =
              let uu____4865 =
                let uu____4866 = p_disjunctivePats pats  in jump2 uu____4866
                 in
              let uu____4867 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4865 uu____4867  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4863 uu____4864  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4862  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4861

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4873 = str "\\/"  in
    FStar_Pprint.separate_map uu____4873 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4879 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4879

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4881 =
      let uu____4882 = unparen e  in uu____4882.FStar_Parser_AST.tm  in
    match uu____4881 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4889 =
          let uu____4890 = str "fun"  in
          let uu____4891 =
            let uu____4892 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4892 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4890 uu____4891  in
        let uu____4893 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4889 uu____4893
    | uu____4894 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4897  ->
    match uu____4897 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4916 =
            let uu____4917 = unparen e  in uu____4917.FStar_Parser_AST.tm  in
          match uu____4916 with
          | FStar_Parser_AST.Match uu____4920 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4935 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4951);
                 FStar_Parser_AST.prange = uu____4952;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4954);
                                                               FStar_Parser_AST.range
                                                                 = uu____4955;
                                                               FStar_Parser_AST.level
                                                                 = uu____4956;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4983 -> (fun x  -> x)  in
        let uu____4985 =
          let uu____4986 =
            let uu____4987 =
              let uu____4988 =
                let uu____4989 =
                  let uu____4990 = p_disjunctivePattern pat  in
                  let uu____4991 =
                    let uu____4992 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____4992 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____4990 uu____4991  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4989  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4988  in
            FStar_Pprint.group uu____4987  in
          let uu____4993 =
            let uu____4994 = p_term e  in maybe_paren uu____4994  in
          op_Hat_Slash_Plus_Hat uu____4986 uu____4993  in
        FStar_Pprint.group uu____4985

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___62_4995  ->
    match uu___62_4995 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4999 = str "when"  in
        let uu____5000 =
          let uu____5001 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____5001 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____4999 uu____5000

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5003 =
      let uu____5004 = unparen e  in uu____5004.FStar_Parser_AST.tm  in
    match uu____5003 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5005;_},e1::e2::[])
        ->
        let uu____5010 = str "<==>"  in
        let uu____5011 = p_tmImplies e1  in
        let uu____5012 = p_tmIff e2  in
        infix0 uu____5010 uu____5011 uu____5012
    | uu____5013 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5015 =
      let uu____5016 = unparen e  in uu____5016.FStar_Parser_AST.tm  in
    match uu____5015 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5017;_},e1::e2::[])
        ->
        let uu____5022 = str "==>"  in
        let uu____5023 = p_tmArrow p_tmFormula e1  in
        let uu____5024 = p_tmImplies e2  in
        infix0 uu____5022 uu____5023 uu____5024
    | uu____5025 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____5030 =
        let uu____5031 = unparen e  in uu____5031.FStar_Parser_AST.tm  in
      match uu____5030 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5038 =
            let uu____5039 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5044 = p_binder false b  in
                   let uu____5045 =
                     let uu____5046 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5046
                      in
                   FStar_Pprint.op_Hat_Hat uu____5044 uu____5045) bs
               in
            let uu____5047 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5039 uu____5047  in
          FStar_Pprint.group uu____5038
      | uu____5048 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5050 =
      let uu____5051 = unparen e  in uu____5051.FStar_Parser_AST.tm  in
    match uu____5050 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5052;_},e1::e2::[])
        ->
        let uu____5057 = str "\\/"  in
        let uu____5058 = p_tmFormula e1  in
        let uu____5059 = p_tmConjunction e2  in
        infix0 uu____5057 uu____5058 uu____5059
    | uu____5060 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5062 =
      let uu____5063 = unparen e  in uu____5063.FStar_Parser_AST.tm  in
    match uu____5062 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5064;_},e1::e2::[])
        ->
        let uu____5069 = str "/\\"  in
        let uu____5070 = p_tmConjunction e1  in
        let uu____5071 = p_tmTuple e2  in
        infix0 uu____5069 uu____5070 uu____5071
    | uu____5072 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5075 =
      let uu____5076 = unparen e  in uu____5076.FStar_Parser_AST.tm  in
    match uu____5075 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5091 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5091
          (fun uu____5099  ->
             match uu____5099 with | (e1,uu____5105) -> p_tmEq e1) args
    | uu____5106 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5111 =
             let uu____5112 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5112  in
           FStar_Pprint.group uu____5111)

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
      let uu____5163 =
        let uu____5164 = unparen e  in uu____5164.FStar_Parser_AST.tm  in
      match uu____5163 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5171 = levels op1  in
          (match uu____5171 with
           | (left1,mine,right1) ->
               let uu____5181 =
                 let uu____5182 = FStar_All.pipe_left str op1  in
                 let uu____5183 = p_tmEq' left1 e1  in
                 let uu____5184 = p_tmEq' right1 e2  in
                 infix0 uu____5182 uu____5183 uu____5184  in
               paren_if curr mine uu____5181)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5185;_},e1::e2::[])
          ->
          let uu____5190 =
            let uu____5191 = p_tmEq e1  in
            let uu____5192 =
              let uu____5193 =
                let uu____5194 =
                  let uu____5195 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5195  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5194  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5193  in
            FStar_Pprint.op_Hat_Hat uu____5191 uu____5192  in
          FStar_Pprint.group uu____5190
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5196;_},e1::[])
          ->
          let uu____5200 = levels "-"  in
          (match uu____5200 with
           | (left1,mine,right1) ->
               let uu____5210 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5210)
      | uu____5211 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____5274 =
        let uu____5275 = unparen e  in uu____5275.FStar_Parser_AST.tm  in
      match uu____5274 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5278)::(e2,uu____5280)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5300 = is_list e  in Prims.op_Negation uu____5300)
          ->
          let op = "::"  in
          let uu____5302 = levels op  in
          (match uu____5302 with
           | (left1,mine,right1) ->
               let uu____5312 =
                 let uu____5313 = str op  in
                 let uu____5314 = p_tmNoEq' left1 e1  in
                 let uu____5315 = p_tmNoEq' right1 e2  in
                 infix0 uu____5313 uu____5314 uu____5315  in
               paren_if curr mine uu____5312)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5323 = levels op  in
          (match uu____5323 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5337 = p_binder false b  in
                 let uu____5338 =
                   let uu____5339 =
                     let uu____5340 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5340 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5339  in
                 FStar_Pprint.op_Hat_Hat uu____5337 uu____5338  in
               let uu____5341 =
                 let uu____5342 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5343 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5342 uu____5343  in
               paren_if curr mine uu____5341)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5350 = levels op1  in
          (match uu____5350 with
           | (left1,mine,right1) ->
               let uu____5360 =
                 let uu____5361 = str op1  in
                 let uu____5362 = p_tmNoEq' left1 e1  in
                 let uu____5363 = p_tmNoEq' right1 e2  in
                 infix0 uu____5361 uu____5362 uu____5363  in
               paren_if curr mine uu____5360)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5366 =
            let uu____5367 = p_lidentOrUnderscore lid  in
            let uu____5368 =
              let uu____5369 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5369  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5367 uu____5368  in
          FStar_Pprint.group uu____5366
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5390 =
            let uu____5391 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5392 =
              let uu____5393 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____5393 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____5391 uu____5392  in
          braces_with_nesting uu____5390
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5398;_},e1::[])
          ->
          let uu____5402 =
            let uu____5403 = str "~"  in
            let uu____5404 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5403 uu____5404  in
          FStar_Pprint.group uu____5402
      | uu____5405 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5407 = p_appTerm e  in
    let uu____5408 =
      let uu____5409 =
        let uu____5410 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5410 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5409  in
    FStar_Pprint.op_Hat_Hat uu____5407 uu____5408

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5415 =
            let uu____5416 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5416 t phi  in
          soft_parens_with_nesting uu____5415
      | FStar_Parser_AST.TAnnotated uu____5417 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5422 ->
          let uu____5423 =
            let uu____5424 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5424
             in
          failwith uu____5423
      | FStar_Parser_AST.TVariable uu____5425 ->
          let uu____5426 =
            let uu____5427 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5427
             in
          failwith uu____5426
      | FStar_Parser_AST.NoName uu____5428 ->
          let uu____5429 =
            let uu____5430 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5430
             in
          failwith uu____5429

and p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5431  ->
    match uu____5431 with
    | (lid,e) ->
        let uu____5438 =
          let uu____5439 = p_qlident lid  in
          let uu____5440 =
            let uu____5441 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5441  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5439 uu____5440  in
        FStar_Pprint.group uu____5438

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5443 =
      let uu____5444 = unparen e  in uu____5444.FStar_Parser_AST.tm  in
    match uu____5443 with
    | FStar_Parser_AST.App uu____5445 when is_general_application e ->
        let uu____5452 = head_and_args e  in
        (match uu____5452 with
         | (head1,args) ->
             let uu____5477 =
               let uu____5488 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5488
               then
                 let uu____5518 =
                   FStar_Util.take
                     (fun uu____5542  ->
                        match uu____5542 with
                        | (uu____5547,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5518 with
                 | (fs_typ_args,args1) ->
                     let uu____5585 =
                       let uu____5586 = p_indexingTerm head1  in
                       let uu____5587 =
                         let uu____5588 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5588 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5586 uu____5587  in
                     (uu____5585, args1)
               else
                 (let uu____5600 = p_indexingTerm head1  in
                  (uu____5600, args))
                in
             (match uu____5477 with
              | (head_doc,args1) ->
                  let uu____5621 =
                    let uu____5622 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5622 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5621))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5642 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5642)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5660 =
               let uu____5661 = p_quident lid  in
               let uu____5662 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5661 uu____5662  in
             FStar_Pprint.group uu____5660
         | hd1::tl1 ->
             let uu____5679 =
               let uu____5680 =
                 let uu____5681 =
                   let uu____5682 = p_quident lid  in
                   let uu____5683 = p_argTerm hd1  in
                   prefix2 uu____5682 uu____5683  in
                 FStar_Pprint.group uu____5681  in
               let uu____5684 =
                 let uu____5685 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5685  in
               FStar_Pprint.op_Hat_Hat uu____5680 uu____5684  in
             FStar_Pprint.group uu____5679)
    | uu____5690 -> p_indexingTerm e

and p_argTerm :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun arg_imp  ->
    match arg_imp with
    | (u,FStar_Parser_AST.UnivApp ) -> p_universe u
    | (e,FStar_Parser_AST.FsTypApp ) ->
        (FStar_Errors.log_issue e.FStar_Parser_AST.range
           (FStar_Errors.Warning_UnexpectedFsTypApp,
             "Unexpected FsTypApp, output might not be formatted correctly.");
         (let uu____5699 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5699 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5701 = str "#"  in
        let uu____5702 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5701 uu____5702
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5704  ->
    match uu____5704 with | (e,uu____5710) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5715 =
        let uu____5716 = unparen e  in uu____5716.FStar_Parser_AST.tm  in
      match uu____5715 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5717;_},e1::e2::[])
          ->
          let uu____5722 =
            let uu____5723 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5724 =
              let uu____5725 =
                let uu____5726 = p_term e2  in
                soft_parens_with_nesting uu____5726  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5725  in
            FStar_Pprint.op_Hat_Hat uu____5723 uu____5724  in
          FStar_Pprint.group uu____5722
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5727;_},e1::e2::[])
          ->
          let uu____5732 =
            let uu____5733 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5734 =
              let uu____5735 =
                let uu____5736 = p_term e2  in
                soft_brackets_with_nesting uu____5736  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5735  in
            FStar_Pprint.op_Hat_Hat uu____5733 uu____5734  in
          FStar_Pprint.group uu____5732
      | uu____5737 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5740 =
      let uu____5741 = unparen e  in uu____5741.FStar_Parser_AST.tm  in
    match uu____5740 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5744 = p_quident lid  in
        let uu____5745 =
          let uu____5746 =
            let uu____5747 = p_term e1  in
            soft_parens_with_nesting uu____5747  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5746  in
        FStar_Pprint.op_Hat_Hat uu____5744 uu____5745
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5753 = str (FStar_Ident.text_of_id op)  in
        let uu____5754 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5753 uu____5754
    | uu____5755 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5757 =
      let uu____5758 = unparen e  in uu____5758.FStar_Parser_AST.tm  in
    match uu____5757 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5764 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5771 = str (FStar_Ident.text_of_id op)  in
        let uu____5772 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5771 uu____5772
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5776 =
          let uu____5777 =
            let uu____5778 = str (FStar_Ident.text_of_id op)  in
            let uu____5779 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5778 uu____5779  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5777  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5776
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5794 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5795 =
          let uu____5796 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5797 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5796 p_tmEq uu____5797  in
        let uu____5804 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5794 uu____5795 uu____5804
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5807 =
          let uu____5808 = p_atomicTermNotQUident e1  in
          let uu____5809 =
            let uu____5810 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5810  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5808 uu____5809
           in
        FStar_Pprint.group uu____5807
    | uu____5811 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5813 =
      let uu____5814 = unparen e  in uu____5814.FStar_Parser_AST.tm  in
    match uu____5813 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5818 = p_quident constr_lid  in
        let uu____5819 =
          let uu____5820 =
            let uu____5821 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5821  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5820  in
        FStar_Pprint.op_Hat_Hat uu____5818 uu____5819
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5823 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5823 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5825 = p_term e1  in soft_parens_with_nesting uu____5825
    | uu____5826 when is_array e ->
        let es = extract_from_list e  in
        let uu____5830 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5831 =
          let uu____5832 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5832 p_noSeqTerm es  in
        let uu____5833 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5830 uu____5831 uu____5833
    | uu____5834 when is_list e ->
        let uu____5835 =
          let uu____5836 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5837 = extract_from_list e  in
          separate_map_or_flow uu____5836 p_noSeqTerm uu____5837  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5835 FStar_Pprint.rbracket
    | uu____5840 when is_lex_list e ->
        let uu____5841 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5842 =
          let uu____5843 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5844 = extract_from_list e  in
          separate_map_or_flow uu____5843 p_noSeqTerm uu____5844  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5841 uu____5842 FStar_Pprint.rbracket
    | uu____5847 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5851 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5852 =
          let uu____5853 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5853 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5851 uu____5852 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5857 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5858 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5857 uu____5858
    | FStar_Parser_AST.Op (op,args) when
        let uu____5865 = handleable_op op args  in
        Prims.op_Negation uu____5865 ->
        let uu____5866 =
          let uu____5867 =
            let uu____5868 =
              let uu____5869 =
                let uu____5870 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5870
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5869  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5868  in
          Prims.strcat "Operation " uu____5867  in
        failwith uu____5866
    | FStar_Parser_AST.Uvar uu____5871 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5872 = p_term e  in soft_parens_with_nesting uu____5872
    | FStar_Parser_AST.Const uu____5873 ->
        let uu____5874 = p_term e  in soft_parens_with_nesting uu____5874
    | FStar_Parser_AST.Op uu____5875 ->
        let uu____5882 = p_term e  in soft_parens_with_nesting uu____5882
    | FStar_Parser_AST.Tvar uu____5883 ->
        let uu____5884 = p_term e  in soft_parens_with_nesting uu____5884
    | FStar_Parser_AST.Var uu____5885 ->
        let uu____5886 = p_term e  in soft_parens_with_nesting uu____5886
    | FStar_Parser_AST.Name uu____5887 ->
        let uu____5888 = p_term e  in soft_parens_with_nesting uu____5888
    | FStar_Parser_AST.Construct uu____5889 ->
        let uu____5900 = p_term e  in soft_parens_with_nesting uu____5900
    | FStar_Parser_AST.Abs uu____5901 ->
        let uu____5908 = p_term e  in soft_parens_with_nesting uu____5908
    | FStar_Parser_AST.App uu____5909 ->
        let uu____5916 = p_term e  in soft_parens_with_nesting uu____5916
    | FStar_Parser_AST.Let uu____5917 ->
        let uu____5938 = p_term e  in soft_parens_with_nesting uu____5938
    | FStar_Parser_AST.LetOpen uu____5939 ->
        let uu____5944 = p_term e  in soft_parens_with_nesting uu____5944
    | FStar_Parser_AST.Seq uu____5945 ->
        let uu____5950 = p_term e  in soft_parens_with_nesting uu____5950
    | FStar_Parser_AST.Bind uu____5951 ->
        let uu____5958 = p_term e  in soft_parens_with_nesting uu____5958
    | FStar_Parser_AST.If uu____5959 ->
        let uu____5966 = p_term e  in soft_parens_with_nesting uu____5966
    | FStar_Parser_AST.Match uu____5967 ->
        let uu____5982 = p_term e  in soft_parens_with_nesting uu____5982
    | FStar_Parser_AST.TryWith uu____5983 ->
        let uu____5998 = p_term e  in soft_parens_with_nesting uu____5998
    | FStar_Parser_AST.Ascribed uu____5999 ->
        let uu____6008 = p_term e  in soft_parens_with_nesting uu____6008
    | FStar_Parser_AST.Record uu____6009 ->
        let uu____6022 = p_term e  in soft_parens_with_nesting uu____6022
    | FStar_Parser_AST.Project uu____6023 ->
        let uu____6028 = p_term e  in soft_parens_with_nesting uu____6028
    | FStar_Parser_AST.Product uu____6029 ->
        let uu____6036 = p_term e  in soft_parens_with_nesting uu____6036
    | FStar_Parser_AST.Sum uu____6037 ->
        let uu____6044 = p_term e  in soft_parens_with_nesting uu____6044
    | FStar_Parser_AST.QForall uu____6045 ->
        let uu____6058 = p_term e  in soft_parens_with_nesting uu____6058
    | FStar_Parser_AST.QExists uu____6059 ->
        let uu____6072 = p_term e  in soft_parens_with_nesting uu____6072
    | FStar_Parser_AST.Refine uu____6073 ->
        let uu____6078 = p_term e  in soft_parens_with_nesting uu____6078
    | FStar_Parser_AST.NamedTyp uu____6079 ->
        let uu____6084 = p_term e  in soft_parens_with_nesting uu____6084
    | FStar_Parser_AST.Requires uu____6085 ->
        let uu____6092 = p_term e  in soft_parens_with_nesting uu____6092
    | FStar_Parser_AST.Ensures uu____6093 ->
        let uu____6100 = p_term e  in soft_parens_with_nesting uu____6100
    | FStar_Parser_AST.Assign uu____6101 ->
        let uu____6106 = p_term e  in soft_parens_with_nesting uu____6106
    | FStar_Parser_AST.Attributes uu____6107 ->
        let uu____6110 = p_term e  in soft_parens_with_nesting uu____6110

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___65_6111  ->
    match uu___65_6111 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6115 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6115
    | FStar_Const.Const_string (s,uu____6117) ->
        let uu____6118 = str s  in FStar_Pprint.dquotes uu____6118
    | FStar_Const.Const_bytearray (bytes,uu____6120) ->
        let uu____6125 =
          let uu____6126 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6126  in
        let uu____6127 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6125 uu____6127
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___63_6145 =
          match uu___63_6145 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___64_6149 =
          match uu___64_6149 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6160  ->
               match uu____6160 with
               | (s,w) ->
                   let uu____6167 = signedness s  in
                   let uu____6168 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6167 uu____6168)
            sign_width_opt
           in
        let uu____6169 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6169 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6171 = FStar_Range.string_of_range r  in str uu____6171
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6173 = p_quident lid  in
        let uu____6174 =
          let uu____6175 =
            let uu____6176 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6176  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6175  in
        FStar_Pprint.op_Hat_Hat uu____6173 uu____6174

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6178 = str "u#"  in
    let uu____6179 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6178 uu____6179

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6181 =
      let uu____6182 = unparen u  in uu____6182.FStar_Parser_AST.tm  in
    match uu____6181 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6183;_},u1::u2::[])
        ->
        let uu____6188 =
          let uu____6189 = p_universeFrom u1  in
          let uu____6190 =
            let uu____6191 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6191  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6189 uu____6190  in
        FStar_Pprint.group uu____6188
    | FStar_Parser_AST.App uu____6192 ->
        let uu____6199 = head_and_args u  in
        (match uu____6199 with
         | (head1,args) ->
             let uu____6224 =
               let uu____6225 = unparen head1  in
               uu____6225.FStar_Parser_AST.tm  in
             (match uu____6224 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6227 =
                    let uu____6228 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6229 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6237  ->
                           match uu____6237 with
                           | (u1,uu____6243) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6228 uu____6229  in
                  FStar_Pprint.group uu____6227
              | uu____6244 ->
                  let uu____6245 =
                    let uu____6246 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6246
                     in
                  failwith uu____6245))
    | uu____6247 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____6249 =
      let uu____6250 = unparen u  in uu____6250.FStar_Parser_AST.tm  in
    match uu____6249 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6273 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6273
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6274;_},uu____6275::uu____6276::[])
        ->
        let uu____6279 = p_universeFrom u  in
        soft_parens_with_nesting uu____6279
    | FStar_Parser_AST.App uu____6280 ->
        let uu____6287 = p_universeFrom u  in
        soft_parens_with_nesting uu____6287
    | uu____6288 ->
        let uu____6289 =
          let uu____6290 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6290
           in
        failwith uu____6289

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
       | FStar_Parser_AST.Module (uu____6330,decls) ->
           let uu____6336 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6336
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6345,decls,uu____6347) ->
           let uu____6352 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6352
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6403  ->
         match uu____6403 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6443,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6449,decls,uu____6451) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6496 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6509;
                 FStar_Parser_AST.doc = uu____6510;
                 FStar_Parser_AST.quals = uu____6511;
                 FStar_Parser_AST.attrs = uu____6512;_}::uu____6513 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6519 =
                   let uu____6522 =
                     let uu____6525 = FStar_List.tl ds  in d :: uu____6525
                      in
                   d0 :: uu____6522  in
                 (uu____6519, (d0.FStar_Parser_AST.drange))
             | uu____6530 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6496 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6588 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6588 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6684 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6684, comments1))))))
  