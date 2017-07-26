open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____20 'Auu____21 .
    Prims.bool -> ('Auu____21 -> 'Auu____20) -> 'Auu____21 -> 'Auu____20
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
    let uu____86 =
      let uu____87 = FStar_ST.op_Bang should_unparen  in
      Prims.op_Negation uu____87  in
    if uu____86
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____100 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____115 'Auu____116 .
    'Auu____116 ->
      ('Auu____115 -> 'Auu____116) ->
        'Auu____115 FStar_Pervasives_Native.option -> 'Auu____116
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
  'Auu____185 .
    FStar_Pprint.document ->
      ('Auu____185 -> FStar_Pprint.document) ->
        'Auu____185 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____207 =
          let uu____208 =
            let uu____209 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____209  in
          FStar_Pprint.separate_map uu____208 f l  in
        FStar_Pprint.group uu____207
  
let precede_break_separate_map :
  'Auu____220 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____220 -> FStar_Pprint.document) ->
          'Auu____220 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____246 =
            let uu____247 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____248 =
              let uu____249 = FStar_List.hd l  in
              FStar_All.pipe_right uu____249 f  in
            FStar_Pprint.precede uu____247 uu____248  in
          let uu____250 =
            let uu____251 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____257 =
                   let uu____258 =
                     let uu____259 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____259  in
                   FStar_Pprint.op_Hat_Hat sep uu____258  in
                 FStar_Pprint.op_Hat_Hat break1 uu____257) uu____251
             in
          FStar_Pprint.op_Hat_Hat uu____246 uu____250
  
let concat_break_map :
  'Auu____266 .
    ('Auu____266 -> FStar_Pprint.document) ->
      'Auu____266 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____284 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____288 = f x  in FStar_Pprint.op_Hat_Hat uu____288 break1)
          l
         in
      FStar_Pprint.group uu____284
  
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
    let uu____317 = str "begin"  in
    let uu____318 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____317 contents uu____318
  
let separate_map_or_flow :
  'Auu____327 .
    FStar_Pprint.document ->
      ('Auu____327 -> FStar_Pprint.document) ->
        'Auu____327 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____368 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____368 -> FStar_Pprint.document) ->
                  'Auu____368 Prims.list -> FStar_Pprint.document
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
                    (let uu____413 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____413
                       closing)
  
let doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____427  ->
    match uu____427 with
    | (comment,keywords) ->
        let uu____452 =
          let uu____453 =
            let uu____456 = str comment  in
            let uu____457 =
              let uu____460 =
                let uu____463 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____472  ->
                       match uu____472 with
                       | (k,v1) ->
                           let uu____479 =
                             let uu____482 = str k  in
                             let uu____483 =
                               let uu____486 =
                                 let uu____489 = str v1  in [uu____489]  in
                               FStar_Pprint.rarrow :: uu____486  in
                             uu____482 :: uu____483  in
                           FStar_Pprint.concat uu____479) keywords
                   in
                [uu____463]  in
              FStar_Pprint.space :: uu____460  in
            uu____456 :: uu____457  in
          FStar_Pprint.concat uu____453  in
        FStar_Pprint.group uu____452
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____494 =
      let uu____495 = unparen e  in uu____495.FStar_Parser_AST.tm  in
    match uu____494 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____496 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____505 =
        let uu____506 = unparen t  in uu____506.FStar_Parser_AST.tm  in
      match uu____505 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____508 -> false
  
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
        let uu____530 =
          let uu____531 = unparen e  in uu____531.FStar_Parser_AST.tm  in
        match uu____530 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____544::(e2,uu____546)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____569 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____582 =
      let uu____583 = unparen e  in uu____583.FStar_Parser_AST.tm  in
    match uu____582 with
    | FStar_Parser_AST.Construct (uu____586,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____597,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____618 = extract_from_list e2  in e1 :: uu____618
    | uu____621 ->
        let uu____622 =
          let uu____623 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____623  in
        failwith uu____622
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____630 =
      let uu____631 = unparen e  in uu____631.FStar_Parser_AST.tm  in
    match uu____630 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____633;
           FStar_Parser_AST.level = uu____634;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____636 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____641 =
      let uu____642 = unparen e  in uu____642.FStar_Parser_AST.tm  in
    match uu____641 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____645;
           FStar_Parser_AST.level = uu____646;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____648;
                                                        FStar_Parser_AST.level
                                                          = uu____649;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____651;
                                                   FStar_Parser_AST.level =
                                                     uu____652;_},FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals maybe_singleton_lid
           FStar_Parser_Const.tset_singleton)
          &&
          (FStar_Ident.lid_equals maybe_ref_lid FStar_Parser_Const.heap_ref)
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_union_lid;
                FStar_Parser_AST.range = uu____654;
                FStar_Parser_AST.level = uu____655;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____657;
           FStar_Parser_AST.level = uu____658;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____660 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____667 =
      let uu____668 = unparen e  in uu____668.FStar_Parser_AST.tm  in
    match uu____667 with
    | FStar_Parser_AST.Var uu____671 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____672;
           FStar_Parser_AST.range = uu____673;
           FStar_Parser_AST.level = uu____674;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____675;
                                                        FStar_Parser_AST.range
                                                          = uu____676;
                                                        FStar_Parser_AST.level
                                                          = uu____677;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____679;
                                                   FStar_Parser_AST.level =
                                                     uu____680;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____681;
                FStar_Parser_AST.range = uu____682;
                FStar_Parser_AST.level = uu____683;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____685;
           FStar_Parser_AST.level = uu____686;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____688 = extract_from_ref_set e1  in
        let uu____691 = extract_from_ref_set e2  in
        FStar_List.append uu____688 uu____691
    | uu____694 ->
        let uu____695 =
          let uu____696 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____696  in
        failwith uu____695
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____703 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____703
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____708 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____708
  
let is_general_prefix_op : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let op_starting_char =
      FStar_Util.char_at (FStar_Ident.text_of_id op) (Prims.parse_int "0")
       in
    ((op_starting_char = '!') || (op_starting_char = '?')) ||
      ((op_starting_char = '~') && ((FStar_Ident.text_of_id op) <> "~"))
  
let head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term,(FStar_Parser_AST.term,FStar_Parser_AST.imp)
                             FStar_Pervasives_Native.tuple2 Prims.list)
      FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    let rec aux e1 acc =
      let uu____757 =
        let uu____758 = unparen e1  in uu____758.FStar_Parser_AST.tm  in
      match uu____757 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____776 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____791 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____796 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____801 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___93_819  ->
    match uu___93_819 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___94_837  ->
      match uu___94_837 with
      | FStar_Util.Inl c ->
          let uu____843 = FStar_String.get s (Prims.parse_int "0")  in
          uu____843 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____851 .
    Prims.string ->
      ('Auu____851,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____869  ->
      match uu____869 with
      | (assoc_levels,tokens) ->
          let uu____894 = FStar_List.tryFind (matches_token s) tokens  in
          uu____894 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____917 .
    Prims.unit ->
      (associativity,('Auu____917,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____928  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____945 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____945) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____956  ->
    (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
  
let opinfix2 :
  'Auu____981 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____981) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____992  -> (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-']) 
let minus_lvl :
  'Auu____1013 .
    Prims.unit ->
      (associativity,('Auu____1013,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1024  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1041 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1041) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1052  -> (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^']) 
let pipe_right :
  'Auu____1073 .
    Prims.unit ->
      (associativity,('Auu____1073,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1084  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1101 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1101) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1112  -> (Left, [FStar_Util.Inl '$']) 
let opinfix0c :
  'Auu____1129 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1129) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1140  ->
    (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
  
let equal :
  'Auu____1165 .
    Prims.unit ->
      (associativity,('Auu____1165,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1176  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1193 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1193) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1204  -> (Left, [FStar_Util.Inl '&']) 
let opinfix0a :
  'Auu____1221 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1221) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1232  -> (Left, [FStar_Util.Inl '|']) 
let colon_equals :
  'Auu____1249 .
    Prims.unit ->
      (associativity,('Auu____1249,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1260  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1277 .
    Prims.unit ->
      (associativity,('Auu____1277,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1288  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1305 .
    Prims.unit ->
      (associativity,('Auu____1305,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1316  -> (Right, [FStar_Util.Inr "::"]) 
let level_associativity_spec :
  (associativity,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  [Obj.magic (opinfix4 ());
  Obj.magic (opinfix3 ());
  Obj.magic (opinfix2 ());
  Obj.magic (opinfix1 ());
  Obj.magic (pipe_right ());
  Obj.magic (opinfix0d ());
  Obj.magic (opinfix0c ());
  Obj.magic (opinfix0b ());
  Obj.magic (opinfix0a ());
  Obj.magic (colon_equals ());
  Obj.magic (amp ());
  Obj.magic (colon_colon ())] 
let level_table :
  ((Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3,(FStar_Char.char,
                                                                    Prims.string)
                                                                    FStar_Util.either
                                                                    Prims.list)
    FStar_Pervasives_Native.tuple2 Prims.list
  =
  let levels_from_associativity l uu___95_1503 =
    match uu___95_1503 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1541  ->
         match uu____1541 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1618 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1618 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1666) ->
          assoc_levels
      | uu____1707 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1745 .
    ('Auu____1745,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1801 =
        FStar_List.tryFind
          (fun uu____1839  ->
             match uu____1839 with
             | (uu____1856,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1801 with
      | FStar_Pervasives_Native.Some ((uu____1894,l1,uu____1896),uu____1897)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1948 =
            let uu____1949 =
              let uu____1950 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1950  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1949
             in
          failwith uu____1948
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____1984 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1984) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1997  ->
    [Obj.magic (opinfix0a ());
    Obj.magic (opinfix0b ());
    Obj.magic (opinfix0c ());
    Obj.magic (opinfix0d ());
    Obj.magic (opinfix1 ());
    Obj.magic (opinfix2 ())]
  
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2072 =
      let uu____2085 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2085 (Obj.magic (operatorInfix0ad12 ()))  in
    uu____2072 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [Obj.magic (opinfix3 ()); Obj.magic (opinfix4 ())]  in
  fun op  ->
    let uu____2189 =
      let uu____2202 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2202 opinfix34  in
    uu____2189 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2264 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2264
    then (Prims.parse_int "1")
    else
      (let uu____2266 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2266
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2275 . FStar_Ident.ident -> 'Auu____2275 Prims.list -> Prims.bool =
  fun op  ->
    fun args  ->
      match FStar_List.length args with
      | _0_26 when _0_26 = (Prims.parse_int "0") -> true
      | _0_27 when _0_27 = (Prims.parse_int "1") ->
          (is_general_prefix_op op) ||
            (FStar_List.mem (FStar_Ident.text_of_id op) ["-"; "~"])
      | _0_28 when _0_28 = (Prims.parse_int "2") ->
          ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
            (FStar_List.mem (FStar_Ident.text_of_id op)
               ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
      | _0_29 when _0_29 = (Prims.parse_int "3") ->
          FStar_List.mem (FStar_Ident.text_of_id op) [".()<-"; ".[]<-"]
      | uu____2288 -> false
  
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2322 .
    ('Auu____2322 -> FStar_Pprint.document) ->
      'Auu____2322 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2354 = FStar_ST.op_Bang comment_stack  in
          match uu____2354 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2416 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2416
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2456 =
                    let uu____2457 =
                      let uu____2458 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2458
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2457  in
                  comments_before_pos uu____2456 print_pos lookahead_pos))
              else
                (let uu____2460 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2460))
           in
        let uu____2461 =
          let uu____2466 =
            let uu____2467 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2467  in
          let uu____2468 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2466 uu____2468  in
        match uu____2461 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2474 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2474
              else comments  in
            let uu____2480 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2480
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2497 = FStar_ST.op_Bang comment_stack  in
          match uu____2497 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2587 =
                    let uu____2588 =
                      let uu____2589 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2589  in
                    uu____2588 - lbegin  in
                  max k uu____2587  in
                let doc2 =
                  let uu____2591 =
                    let uu____2592 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2593 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2592 uu____2593  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2591  in
                let uu____2594 =
                  let uu____2595 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2595  in
                place_comments_until_pos (Prims.parse_int "1") uu____2594
                  pos_end doc2))
          | uu____2596 ->
              let lnum =
                let uu____2604 =
                  let uu____2605 = FStar_Range.line_of_pos pos_end  in
                  uu____2605 - lbegin  in
                max (Prims.parse_int "1") uu____2604  in
              let uu____2606 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2606
  
let separate_map_with_comments :
  'Auu____2619 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2619 -> FStar_Pprint.document) ->
          'Auu____2619 Prims.list ->
            ('Auu____2619 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2667 x =
              match uu____2667 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2681 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2681 doc1
                     in
                  let uu____2682 =
                    let uu____2683 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2683  in
                  let uu____2684 =
                    let uu____2685 =
                      let uu____2686 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2686  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2685  in
                  (uu____2682, uu____2684)
               in
            let uu____2687 =
              let uu____2694 = FStar_List.hd xs  in
              let uu____2695 = FStar_List.tl xs  in (uu____2694, uu____2695)
               in
            match uu____2687 with
            | (x,xs1) ->
                let init1 =
                  let uu____2711 =
                    let uu____2712 =
                      let uu____2713 = extract_range x  in
                      FStar_Range.end_of_range uu____2713  in
                    FStar_Range.line_of_pos uu____2712  in
                  let uu____2714 =
                    let uu____2715 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2715  in
                  (uu____2711, uu____2714)  in
                let uu____2716 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2716
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____3003 =
      let uu____3004 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3005 =
        let uu____3006 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3007 =
          let uu____3008 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3009 =
            let uu____3010 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3010
             in
          FStar_Pprint.op_Hat_Hat uu____3008 uu____3009  in
        FStar_Pprint.op_Hat_Hat uu____3006 uu____3007  in
      FStar_Pprint.op_Hat_Hat uu____3004 uu____3005  in
    FStar_Pprint.group uu____3003

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____3013 =
      let uu____3014 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3014  in
    let uu____3015 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3013 FStar_Pprint.space uu____3015
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____3016  ->
    match uu____3016 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3050 =
                match uu____3050 with
                | (kwd,arg) ->
                    let uu____3057 = str "@"  in
                    let uu____3058 =
                      let uu____3059 = str kwd  in
                      let uu____3060 =
                        let uu____3061 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3061
                         in
                      FStar_Pprint.op_Hat_Hat uu____3059 uu____3060  in
                    FStar_Pprint.op_Hat_Hat uu____3057 uu____3058
                 in
              let uu____3062 =
                let uu____3063 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3063 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3062
           in
        let uu____3068 =
          let uu____3069 =
            let uu____3070 =
              let uu____3071 =
                let uu____3072 = str doc1  in
                let uu____3073 =
                  let uu____3074 =
                    let uu____3075 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3075  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3074  in
                FStar_Pprint.op_Hat_Hat uu____3072 uu____3073  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3071  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3070  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3069  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3068

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3078 =
          let uu____3079 = str "open"  in
          let uu____3080 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3079 uu____3080  in
        FStar_Pprint.group uu____3078
    | FStar_Parser_AST.Include uid ->
        let uu____3082 =
          let uu____3083 = str "include"  in
          let uu____3084 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3083 uu____3084  in
        FStar_Pprint.group uu____3082
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3087 =
          let uu____3088 = str "module"  in
          let uu____3089 =
            let uu____3090 =
              let uu____3091 = p_uident uid1  in
              let uu____3092 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3091 uu____3092  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3090  in
          FStar_Pprint.op_Hat_Hat uu____3088 uu____3089  in
        let uu____3093 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3087 uu____3093
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3095 =
          let uu____3096 = str "module"  in
          let uu____3097 =
            let uu____3098 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3098  in
          FStar_Pprint.op_Hat_Hat uu____3096 uu____3097  in
        FStar_Pprint.group uu____3095
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3131 = str "effect"  in
          let uu____3132 =
            let uu____3133 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3133  in
          FStar_Pprint.op_Hat_Hat uu____3131 uu____3132  in
        let uu____3134 =
          let uu____3135 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3135 FStar_Pprint.equals
           in
        let uu____3136 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3134 uu____3136
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3154 = str "type"  in
        let uu____3155 = str "and"  in
        precede_break_separate_map uu____3154 uu____3155 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3177 = str "let"  in
          let uu____3178 =
            let uu____3179 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3179 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3177 uu____3178  in
        let uu____3180 =
          let uu____3181 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3181 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3180 p_letbinding lbs
          (fun uu____3189  ->
             match uu____3189 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3198 =
          let uu____3199 = str "val"  in
          let uu____3200 =
            let uu____3201 =
              let uu____3202 = p_lident lid  in
              let uu____3203 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3202 uu____3203  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3201  in
          FStar_Pprint.op_Hat_Hat uu____3199 uu____3200  in
        let uu____3204 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3198 uu____3204
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3208 =
            let uu____3209 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3209 FStar_Util.is_upper  in
          if uu____3208
          then FStar_Pprint.empty
          else
            (let uu____3211 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3211 FStar_Pprint.space)
           in
        let uu____3212 =
          let uu____3213 =
            let uu____3214 = p_ident id  in
            let uu____3215 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3214 uu____3215  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3213  in
        let uu____3216 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3212 uu____3216
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3223 = str "exception"  in
        let uu____3224 =
          let uu____3225 =
            let uu____3226 = p_uident uid  in
            let uu____3227 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3232 = str "of"  in
                   let uu____3233 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3232 uu____3233) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3226 uu____3227  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3225  in
        FStar_Pprint.op_Hat_Hat uu____3223 uu____3224
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3235 = str "new_effect"  in
        let uu____3236 =
          let uu____3237 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3237  in
        FStar_Pprint.op_Hat_Hat uu____3235 uu____3236
    | FStar_Parser_AST.SubEffect se ->
        let uu____3239 = str "sub_effect"  in
        let uu____3240 =
          let uu____3241 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3241  in
        FStar_Pprint.op_Hat_Hat uu____3239 uu____3240
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3244 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3244 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3245 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3246) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___96_3263  ->
    match uu___96_3263 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3265 = str "#set-options"  in
        let uu____3266 =
          let uu____3267 =
            let uu____3268 = str s  in FStar_Pprint.dquotes uu____3268  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3267  in
        FStar_Pprint.op_Hat_Hat uu____3265 uu____3266
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3272 = str "#reset-options"  in
        let uu____3273 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3277 =
                 let uu____3278 = str s  in FStar_Pprint.dquotes uu____3278
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3277) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3272 uu____3273
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
  fun uu____3293  ->
    match uu____3293 with
    | (typedecl,fsdoc_opt) ->
        let uu____3306 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3307 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3306 uu____3307

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___97_3308  ->
    match uu___97_3308 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3323 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3339 =
          let uu____3340 = p_typ t  in prefix2 FStar_Pprint.equals uu____3340
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3384 =
          match uu____3384 with
          | (lid1,t,doc_opt) ->
              let uu____3400 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3400
           in
        let p_fields uu____3414 =
          let uu____3415 =
            let uu____3416 =
              let uu____3417 =
                let uu____3418 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3418 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3417  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3416  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3415  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3482 =
          match uu____3482 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3508 =
                  let uu____3509 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3509  in
                FStar_Range.extend_to_end_of_line uu____3508  in
              let p_constructorBranch decl =
                let uu____3542 =
                  let uu____3543 =
                    let uu____3544 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3544  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3543  in
                FStar_Pprint.group uu____3542  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3564 =
          let uu____3565 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3565  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3580  ->
             let uu____3581 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3581)

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
            let uu____3596 = p_ident lid  in
            let uu____3597 =
              let uu____3598 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3598  in
            FStar_Pprint.op_Hat_Hat uu____3596 uu____3597
          else
            (let binders_doc =
               let uu____3601 = p_typars bs  in
               let uu____3602 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3606 =
                        let uu____3607 =
                          let uu____3608 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3608
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3607
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3606) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3601 uu____3602  in
             let uu____3609 = p_ident lid  in
             let uu____3610 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3609 binders_doc uu____3610)

and p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3611  ->
    match uu____3611 with
    | (lid,t,doc_opt) ->
        let uu____3627 =
          let uu____3628 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____3629 =
            let uu____3630 = p_lident lid  in
            let uu____3631 =
              let uu____3632 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3632  in
            FStar_Pprint.op_Hat_Hat uu____3630 uu____3631  in
          FStar_Pprint.op_Hat_Hat uu____3628 uu____3629  in
        FStar_Pprint.group uu____3627

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3633  ->
    match uu____3633 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3661 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3662 =
          let uu____3663 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3664 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3669 =
                   let uu____3670 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3670  in
                 let uu____3671 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____3669 uu____3671) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3663 uu____3664  in
        FStar_Pprint.op_Hat_Hat uu____3661 uu____3662

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3672  ->
    match uu____3672 with
    | (pat,e) ->
        let pat_doc =
          let uu____3680 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____3691 =
                  let uu____3692 =
                    let uu____3693 =
                      let uu____3694 =
                        let uu____3695 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3695
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3694
                       in
                    FStar_Pprint.group uu____3693  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3692  in
                (pat1, uu____3691)
            | uu____3696 -> (pat, FStar_Pprint.empty)  in
          match uu____3680 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____3700);
                      FStar_Parser_AST.prange = uu____3701;_},pats)
                   ->
                   let uu____3711 = p_lident x  in
                   let uu____3712 =
                     let uu____3713 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____3713 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____3711 uu____3712
                     FStar_Pprint.equals
               | uu____3714 ->
                   let uu____3715 =
                     let uu____3716 = p_tuplePattern pat1  in
                     let uu____3717 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____3716 uu____3717  in
                   FStar_Pprint.group uu____3715)
           in
        let uu____3718 = p_term e  in prefix2 pat_doc uu____3718

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___98_3719  ->
    match uu___98_3719 with
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
        let uu____3744 = p_uident uid  in
        let uu____3745 = p_binders true bs  in
        let uu____3746 =
          let uu____3747 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____3747  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3744 uu____3745 uu____3746

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
          let uu____3756 =
            let uu____3757 =
              let uu____3758 =
                let uu____3759 = p_uident uid  in
                let uu____3760 = p_binders true bs  in
                let uu____3761 =
                  let uu____3762 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____3762  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3759 uu____3760 uu____3761
                 in
              FStar_Pprint.group uu____3758  in
            let uu____3763 =
              let uu____3764 = str "with"  in
              let uu____3765 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____3764 uu____3765  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3757 uu____3763  in
          braces_with_nesting uu____3756

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3795 =
          let uu____3796 = p_lident lid  in
          let uu____3797 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____3796 uu____3797  in
        let uu____3798 = p_simpleTerm e  in prefix2 uu____3795 uu____3798
    | uu____3799 ->
        let uu____3800 =
          let uu____3801 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3801
           in
        failwith uu____3800

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____3856 =
        match uu____3856 with
        | (kwd,t) ->
            let uu____3863 =
              let uu____3864 = str kwd  in
              let uu____3865 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3864 uu____3865  in
            let uu____3866 = p_simpleTerm t  in prefix2 uu____3863 uu____3866
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____3871 =
      let uu____3872 =
        let uu____3873 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____3874 =
          let uu____3875 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3875  in
        FStar_Pprint.op_Hat_Hat uu____3873 uu____3874  in
      let uu____3876 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____3872 uu____3876  in
    let uu____3877 =
      let uu____3878 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3878  in
    FStar_Pprint.op_Hat_Hat uu____3871 uu____3877

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___99_3879  ->
    match uu___99_3879 with
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
    let uu____3881 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____3881

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___100_3882  ->
    match uu___100_3882 with
    | FStar_Parser_AST.Rec  ->
        let uu____3883 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3883
    | FStar_Parser_AST.Mutable  ->
        let uu____3884 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3884
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___101_3885  ->
    match uu___101_3885 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____3890 =
          let uu____3891 =
            let uu____3892 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____3892  in
          FStar_Pprint.separate_map uu____3891 p_tuplePattern pats  in
        FStar_Pprint.group uu____3890
    | uu____3893 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____3900 =
          let uu____3901 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____3901 p_constructorPattern pats  in
        FStar_Pprint.group uu____3900
    | uu____3902 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____3905;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____3910 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____3911 = p_constructorPattern hd1  in
        let uu____3912 = p_constructorPattern tl1  in
        infix0 uu____3910 uu____3911 uu____3912
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____3914;_},pats)
        ->
        let uu____3920 = p_quident uid  in
        let uu____3921 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____3920 uu____3921
    | uu____3922 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____3926 =
          let uu____3931 =
            let uu____3932 = unparen t  in uu____3932.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____3931)  in
        (match uu____3926 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____3937;
               FStar_Parser_AST.blevel = uu____3938;
               FStar_Parser_AST.aqual = uu____3939;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____3945 =
               let uu____3946 = p_ident lid  in
               p_refinement aqual uu____3946 t1 phi  in
             soft_parens_with_nesting uu____3945
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____3948;
               FStar_Parser_AST.blevel = uu____3949;
               FStar_Parser_AST.aqual = uu____3950;_},phi))
             ->
             let uu____3952 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____3952
         | uu____3953 ->
             let uu____3958 =
               let uu____3959 = p_tuplePattern pat  in
               let uu____3960 =
                 let uu____3961 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____3962 =
                   let uu____3963 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3963  in
                 FStar_Pprint.op_Hat_Hat uu____3961 uu____3962  in
               FStar_Pprint.op_Hat_Hat uu____3959 uu____3960  in
             soft_parens_with_nesting uu____3958)
    | FStar_Parser_AST.PatList pats ->
        let uu____3967 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3967 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____3982 =
          match uu____3982 with
          | (lid,pat) ->
              let uu____3989 = p_qlident lid  in
              let uu____3990 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____3989 uu____3990
           in
        let uu____3991 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____3991
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4001 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4002 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4003 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4001 uu____4002 uu____4003
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4014 =
          let uu____4015 =
            let uu____4016 = str (FStar_Ident.text_of_id op)  in
            let uu____4017 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4016 uu____4017  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4015  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4014
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4025 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4026 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4025 uu____4026
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4028 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4031;
           FStar_Parser_AST.prange = uu____4032;_},uu____4033)
        ->
        let uu____4038 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4038
    | FStar_Parser_AST.PatTuple (uu____4039,false ) ->
        let uu____4044 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4044
    | uu____4045 ->
        let uu____4046 =
          let uu____4047 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4047  in
        failwith uu____4046

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4051 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4052 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4051 uu____4052
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4057 =
              let uu____4058 = unparen t  in uu____4058.FStar_Parser_AST.tm
               in
            match uu____4057 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4061;
                   FStar_Parser_AST.blevel = uu____4062;
                   FStar_Parser_AST.aqual = uu____4063;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4065 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4065 t1 phi
            | uu____4066 ->
                let uu____4067 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4068 =
                  let uu____4069 = p_lident lid  in
                  let uu____4070 =
                    let uu____4071 =
                      let uu____4072 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4073 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4072 uu____4073  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4071  in
                  FStar_Pprint.op_Hat_Hat uu____4069 uu____4070  in
                FStar_Pprint.op_Hat_Hat uu____4067 uu____4068
             in
          if is_atomic
          then
            let uu____4074 =
              let uu____4075 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4075  in
            FStar_Pprint.group uu____4074
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4077 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4083 =
            let uu____4084 = unparen t  in uu____4084.FStar_Parser_AST.tm  in
          (match uu____4083 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4086;
                  FStar_Parser_AST.blevel = uu____4087;
                  FStar_Parser_AST.aqual = uu____4088;_},phi)
               ->
               if is_atomic
               then
                 let uu____4090 =
                   let uu____4091 =
                     let uu____4092 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4092 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4091  in
                 FStar_Pprint.group uu____4090
               else
                 (let uu____4094 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4094)
           | uu____4095 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4103 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4104 =
            let uu____4105 =
              let uu____4106 =
                let uu____4107 = p_appTerm t  in
                let uu____4108 =
                  let uu____4109 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____4109  in
                FStar_Pprint.op_Hat_Hat uu____4107 uu____4108  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4106  in
            FStar_Pprint.op_Hat_Hat binder uu____4105  in
          FStar_Pprint.op_Hat_Hat uu____4103 uu____4104

and p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun is_atomic  ->
    fun bs  -> FStar_Pprint.separate_map break1 (p_binder is_atomic) bs

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
  fun id  ->
    if
      FStar_Util.starts_with FStar_Ident.reserved_prefix
        id.FStar_Ident.idText
    then FStar_Pprint.underscore
    else p_lident id

and p_term : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4123 =
      let uu____4124 = unparen e  in uu____4124.FStar_Parser_AST.tm  in
    match uu____4123 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4127 =
          let uu____4128 =
            let uu____4129 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4129 FStar_Pprint.semi  in
          FStar_Pprint.group uu____4128  in
        let uu____4130 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4127 uu____4130
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4134 =
          let uu____4135 =
            let uu____4136 =
              let uu____4137 = p_lident x  in
              let uu____4138 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____4137 uu____4138  in
            let uu____4139 =
              let uu____4140 = p_noSeqTerm e1  in
              let uu____4141 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____4140 uu____4141  in
            op_Hat_Slash_Plus_Hat uu____4136 uu____4139  in
          FStar_Pprint.group uu____4135  in
        let uu____4142 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4134 uu____4142
    | uu____4143 ->
        let uu____4144 = p_noSeqTerm e  in FStar_Pprint.group uu____4144

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4147 =
      let uu____4148 = unparen e  in uu____4148.FStar_Parser_AST.tm  in
    match uu____4147 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4153 =
          let uu____4154 = p_tmIff e1  in
          let uu____4155 =
            let uu____4156 =
              let uu____4157 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4157  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4156  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4154 uu____4155  in
        FStar_Pprint.group uu____4153
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4163 =
          let uu____4164 = p_tmIff e1  in
          let uu____4165 =
            let uu____4166 =
              let uu____4167 =
                let uu____4168 = p_typ t  in
                let uu____4169 =
                  let uu____4170 = str "by"  in
                  let uu____4171 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4170 uu____4171  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4168 uu____4169  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4167  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4166  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4164 uu____4165  in
        FStar_Pprint.group uu____4163
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4172;_},e1::e2::e3::[])
        ->
        let uu____4178 =
          let uu____4179 =
            let uu____4180 =
              let uu____4181 = p_atomicTermNotQUident e1  in
              let uu____4182 =
                let uu____4183 =
                  let uu____4184 =
                    let uu____4185 = p_term e2  in
                    soft_parens_with_nesting uu____4185  in
                  let uu____4186 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4184 uu____4186  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4183  in
              FStar_Pprint.op_Hat_Hat uu____4181 uu____4182  in
            FStar_Pprint.group uu____4180  in
          let uu____4187 =
            let uu____4188 = p_noSeqTerm e3  in jump2 uu____4188  in
          FStar_Pprint.op_Hat_Hat uu____4179 uu____4187  in
        FStar_Pprint.group uu____4178
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4189;_},e1::e2::e3::[])
        ->
        let uu____4195 =
          let uu____4196 =
            let uu____4197 =
              let uu____4198 = p_atomicTermNotQUident e1  in
              let uu____4199 =
                let uu____4200 =
                  let uu____4201 =
                    let uu____4202 = p_term e2  in
                    soft_brackets_with_nesting uu____4202  in
                  let uu____4203 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4201 uu____4203  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4200  in
              FStar_Pprint.op_Hat_Hat uu____4198 uu____4199  in
            FStar_Pprint.group uu____4197  in
          let uu____4204 =
            let uu____4205 = p_noSeqTerm e3  in jump2 uu____4205  in
          FStar_Pprint.op_Hat_Hat uu____4196 uu____4204  in
        FStar_Pprint.group uu____4195
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4215 =
          let uu____4216 = str "requires"  in
          let uu____4217 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4216 uu____4217  in
        FStar_Pprint.group uu____4215
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4227 =
          let uu____4228 = str "ensures"  in
          let uu____4229 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4228 uu____4229  in
        FStar_Pprint.group uu____4227
    | FStar_Parser_AST.Attributes es ->
        let uu____4233 =
          let uu____4234 = str "attributes"  in
          let uu____4235 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4234 uu____4235  in
        FStar_Pprint.group uu____4233
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4239 = is_unit e3  in
        if uu____4239
        then
          let uu____4240 =
            let uu____4241 =
              let uu____4242 = str "if"  in
              let uu____4243 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4242 uu____4243  in
            let uu____4244 =
              let uu____4245 = str "then"  in
              let uu____4246 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4245 uu____4246  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4241 uu____4244  in
          FStar_Pprint.group uu____4240
        else
          (let e2_doc =
             let uu____4249 =
               let uu____4250 = unparen e2  in uu____4250.FStar_Parser_AST.tm
                in
             match uu____4249 with
             | FStar_Parser_AST.If (uu____4251,uu____4252,e31) when
                 is_unit e31 ->
                 let uu____4254 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4254
             | uu____4255 -> p_noSeqTerm e2  in
           let uu____4256 =
             let uu____4257 =
               let uu____4258 = str "if"  in
               let uu____4259 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4258 uu____4259  in
             let uu____4260 =
               let uu____4261 =
                 let uu____4262 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4262 e2_doc  in
               let uu____4263 =
                 let uu____4264 = str "else"  in
                 let uu____4265 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4264 uu____4265  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4261 uu____4263  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4257 uu____4260  in
           FStar_Pprint.group uu____4256)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4288 =
          let uu____4289 =
            let uu____4290 = str "try"  in
            let uu____4291 = p_noSeqTerm e1  in prefix2 uu____4290 uu____4291
             in
          let uu____4292 =
            let uu____4293 = str "with"  in
            let uu____4294 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4293 uu____4294  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4289 uu____4292  in
        FStar_Pprint.group uu____4288
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4325 =
          let uu____4326 =
            let uu____4327 = str "match"  in
            let uu____4328 = p_noSeqTerm e1  in
            let uu____4329 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4327 uu____4328 uu____4329
             in
          let uu____4330 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4326 uu____4330  in
        FStar_Pprint.group uu____4325
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4341 =
          let uu____4342 =
            let uu____4343 = str "let open"  in
            let uu____4344 = p_quident uid  in
            let uu____4345 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4343 uu____4344 uu____4345
             in
          let uu____4346 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4342 uu____4346  in
        FStar_Pprint.group uu____4341
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4363 = str "let"  in
          let uu____4364 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4363 uu____4364  in
        let uu____4365 =
          let uu____4366 =
            let uu____4367 =
              let uu____4368 = str "and"  in
              precede_break_separate_map let_doc uu____4368 p_letbinding lbs
               in
            let uu____4373 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4367 uu____4373  in
          FStar_Pprint.group uu____4366  in
        let uu____4374 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4365 uu____4374
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4377;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4380;
                                                         FStar_Parser_AST.level
                                                           = uu____4381;_})
        when matches_var maybe_x x ->
        let uu____4408 =
          let uu____4409 = str "function"  in
          let uu____4410 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4409 uu____4410  in
        FStar_Pprint.group uu____4408
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4421 =
          let uu____4422 = p_lident id  in
          let uu____4423 =
            let uu____4424 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4424  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4422 uu____4423  in
        FStar_Pprint.group uu____4421
    | uu____4425 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4428 =
      let uu____4429 = unparen e  in uu____4429.FStar_Parser_AST.tm  in
    match uu____4428 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4445 =
          let uu____4446 =
            let uu____4447 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4447 FStar_Pprint.space  in
          let uu____4448 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4446 uu____4448 FStar_Pprint.dot
           in
        let uu____4449 =
          let uu____4450 = p_trigger trigger  in
          let uu____4451 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4450 uu____4451  in
        prefix2 uu____4445 uu____4449
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4467 =
          let uu____4468 =
            let uu____4469 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4469 FStar_Pprint.space  in
          let uu____4470 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4468 uu____4470 FStar_Pprint.dot
           in
        let uu____4471 =
          let uu____4472 = p_trigger trigger  in
          let uu____4473 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4472 uu____4473  in
        prefix2 uu____4467 uu____4471
    | uu____4474 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4476 =
      let uu____4477 = unparen e  in uu____4477.FStar_Parser_AST.tm  in
    match uu____4476 with
    | FStar_Parser_AST.QForall uu____4478 -> str "forall"
    | FStar_Parser_AST.QExists uu____4491 -> str "exists"
    | uu____4504 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___102_4505  ->
    match uu___102_4505 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4517 =
          let uu____4518 =
            let uu____4519 = str "pattern"  in
            let uu____4520 =
              let uu____4521 =
                let uu____4522 = p_disjunctivePats pats  in jump2 uu____4522
                 in
              let uu____4523 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4521 uu____4523  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4519 uu____4520  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4518  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4517

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4529 = str "\\/"  in
    FStar_Pprint.separate_map uu____4529 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4535 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4535

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4537 =
      let uu____4538 = unparen e  in uu____4538.FStar_Parser_AST.tm  in
    match uu____4537 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4545 =
          let uu____4546 = str "fun"  in
          let uu____4547 =
            let uu____4548 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4548 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4546 uu____4547  in
        let uu____4549 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4545 uu____4549
    | uu____4550 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4553  ->
    match uu____4553 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4572 =
            let uu____4573 = unparen e  in uu____4573.FStar_Parser_AST.tm  in
          match uu____4572 with
          | FStar_Parser_AST.Match uu____4576 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4591 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4607);
                 FStar_Parser_AST.prange = uu____4608;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4610);
                                                               FStar_Parser_AST.range
                                                                 = uu____4611;
                                                               FStar_Parser_AST.level
                                                                 = uu____4612;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4639 -> (fun x  -> x)  in
        let uu____4641 =
          let uu____4642 =
            let uu____4643 =
              let uu____4644 =
                let uu____4645 =
                  let uu____4646 = p_disjunctivePattern pat  in
                  let uu____4647 =
                    let uu____4648 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____4648 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____4646 uu____4647  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4645  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4644  in
            FStar_Pprint.group uu____4643  in
          let uu____4649 =
            let uu____4650 = p_term e  in maybe_paren uu____4650  in
          op_Hat_Slash_Plus_Hat uu____4642 uu____4649  in
        FStar_Pprint.group uu____4641

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___103_4651  ->
    match uu___103_4651 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4655 = str "when"  in
        let uu____4656 =
          let uu____4657 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____4657 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____4655 uu____4656

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4659 =
      let uu____4660 = unparen e  in uu____4660.FStar_Parser_AST.tm  in
    match uu____4659 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4661;_},e1::e2::[])
        ->
        let uu____4666 = str "<==>"  in
        let uu____4667 = p_tmImplies e1  in
        let uu____4668 = p_tmIff e2  in
        infix0 uu____4666 uu____4667 uu____4668
    | uu____4669 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4671 =
      let uu____4672 = unparen e  in uu____4672.FStar_Parser_AST.tm  in
    match uu____4671 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4673;_},e1::e2::[])
        ->
        let uu____4678 = str "==>"  in
        let uu____4679 = p_tmArrow p_tmFormula e1  in
        let uu____4680 = p_tmImplies e2  in
        infix0 uu____4678 uu____4679 uu____4680
    | uu____4681 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4686 =
        let uu____4687 = unparen e  in uu____4687.FStar_Parser_AST.tm  in
      match uu____4686 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4694 =
            let uu____4695 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____4700 = p_binder false b  in
                   let uu____4701 =
                     let uu____4702 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4702
                      in
                   FStar_Pprint.op_Hat_Hat uu____4700 uu____4701) bs
               in
            let uu____4703 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____4695 uu____4703  in
          FStar_Pprint.group uu____4694
      | uu____4704 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4706 =
      let uu____4707 = unparen e  in uu____4707.FStar_Parser_AST.tm  in
    match uu____4706 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4708;_},e1::e2::[])
        ->
        let uu____4713 = str "\\/"  in
        let uu____4714 = p_tmFormula e1  in
        let uu____4715 = p_tmConjunction e2  in
        infix0 uu____4713 uu____4714 uu____4715
    | uu____4716 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4718 =
      let uu____4719 = unparen e  in uu____4719.FStar_Parser_AST.tm  in
    match uu____4718 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4720;_},e1::e2::[])
        ->
        let uu____4725 = str "/\\"  in
        let uu____4726 = p_tmConjunction e1  in
        let uu____4727 = p_tmTuple e2  in
        infix0 uu____4725 uu____4726 uu____4727
    | uu____4728 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4731 =
      let uu____4732 = unparen e  in uu____4732.FStar_Parser_AST.tm  in
    match uu____4731 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4747 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____4747
          (fun uu____4755  ->
             match uu____4755 with | (e1,uu____4761) -> p_tmEq e1) args
    | uu____4762 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4767 =
             let uu____4768 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4768  in
           FStar_Pprint.group uu____4767)

and p_tmEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        (FStar_List.append
           [Obj.magic (colon_equals ()); Obj.magic (pipe_right ())]
           (Obj.magic (operatorInfix0ad12 ())))
       in
    p_tmEq' n1 e

and p_tmEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____4813 =
        let uu____4814 = unparen e  in uu____4814.FStar_Parser_AST.tm  in
      match uu____4813 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____4821 = levels op1  in
          (match uu____4821 with
           | (left1,mine,right1) ->
               let uu____4831 =
                 let uu____4832 = FStar_All.pipe_left str op1  in
                 let uu____4833 = p_tmEq' left1 e1  in
                 let uu____4834 = p_tmEq' right1 e2  in
                 infix0 uu____4832 uu____4833 uu____4834  in
               paren_if curr mine uu____4831)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4835;_},e1::e2::[])
          ->
          let uu____4840 =
            let uu____4841 = p_tmEq e1  in
            let uu____4842 =
              let uu____4843 =
                let uu____4844 =
                  let uu____4845 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4845  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4844  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4843  in
            FStar_Pprint.op_Hat_Hat uu____4841 uu____4842  in
          FStar_Pprint.group uu____4840
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4846;_},e1::[])
          ->
          let uu____4850 = levels "-"  in
          (match uu____4850 with
           | (left1,mine,right1) ->
               let uu____4860 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4860)
      | uu____4861 -> p_tmNoEq e

and p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let n1 =
      max_level
        [Obj.magic (colon_colon ());
        Obj.magic (amp ());
        Obj.magic (opinfix3 ());
        Obj.magic (opinfix4 ())]
       in
    p_tmNoEq' n1 e

and p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun curr  ->
    fun e  ->
      let uu____4916 =
        let uu____4917 = unparen e  in uu____4917.FStar_Parser_AST.tm  in
      match uu____4916 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____4920)::(e2,uu____4922)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____4942 = is_list e  in Prims.op_Negation uu____4942)
          ->
          let op = "::"  in
          let uu____4944 = levels op  in
          (match uu____4944 with
           | (left1,mine,right1) ->
               let uu____4954 =
                 let uu____4955 = str op  in
                 let uu____4956 = p_tmNoEq' left1 e1  in
                 let uu____4957 = p_tmNoEq' right1 e2  in
                 infix0 uu____4955 uu____4956 uu____4957  in
               paren_if curr mine uu____4954)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____4965 = levels op  in
          (match uu____4965 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____4979 = p_binder false b  in
                 let uu____4980 =
                   let uu____4981 =
                     let uu____4982 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____4982 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4981  in
                 FStar_Pprint.op_Hat_Hat uu____4979 uu____4980  in
               let uu____4983 =
                 let uu____4984 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____4985 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____4984 uu____4985  in
               paren_if curr mine uu____4983)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____4992 = levels op1  in
          (match uu____4992 with
           | (left1,mine,right1) ->
               let uu____5002 =
                 let uu____5003 = str op1  in
                 let uu____5004 = p_tmNoEq' left1 e1  in
                 let uu____5005 = p_tmNoEq' right1 e2  in
                 infix0 uu____5003 uu____5004 uu____5005  in
               paren_if curr mine uu____5002)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5008 =
            let uu____5009 = p_lidentOrUnderscore lid  in
            let uu____5010 =
              let uu____5011 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5011  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5009 uu____5010  in
          FStar_Pprint.group uu____5008
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5032 =
            let uu____5033 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5034 =
              let uu____5035 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____5035 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____5033 uu____5034  in
          braces_with_nesting uu____5032
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5040;_},e1::[])
          ->
          let uu____5044 =
            let uu____5045 = str "~"  in
            let uu____5046 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5045 uu____5046  in
          FStar_Pprint.group uu____5044
      | uu____5047 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5049 = p_appTerm e  in
    let uu____5050 =
      let uu____5051 =
        let uu____5052 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5052 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5051  in
    FStar_Pprint.op_Hat_Hat uu____5049 uu____5050

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5057 =
            let uu____5058 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5058 t phi  in
          soft_parens_with_nesting uu____5057
      | FStar_Parser_AST.TAnnotated uu____5059 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5064 ->
          let uu____5065 =
            let uu____5066 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5066
             in
          failwith uu____5065
      | FStar_Parser_AST.TVariable uu____5067 ->
          let uu____5068 =
            let uu____5069 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5069
             in
          failwith uu____5068
      | FStar_Parser_AST.NoName uu____5070 ->
          let uu____5071 =
            let uu____5072 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5072
             in
          failwith uu____5071

and p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____5073  ->
    match uu____5073 with
    | (lid,e) ->
        let uu____5080 =
          let uu____5081 = p_qlident lid  in
          let uu____5082 =
            let uu____5083 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5083  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5081 uu____5082  in
        FStar_Pprint.group uu____5080

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5085 =
      let uu____5086 = unparen e  in uu____5086.FStar_Parser_AST.tm  in
    match uu____5085 with
    | FStar_Parser_AST.App uu____5087 when is_general_application e ->
        let uu____5094 = head_and_args e  in
        (match uu____5094 with
         | (head1,args) ->
             let uu____5119 =
               let uu____5130 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5130
               then
                 let uu____5151 =
                   FStar_Util.take
                     (fun uu____5175  ->
                        match uu____5175 with
                        | (uu____5180,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5151 with
                 | (fs_typ_args,args1) ->
                     let uu____5218 =
                       let uu____5219 = p_indexingTerm head1  in
                       let uu____5220 =
                         let uu____5221 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5221 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5219 uu____5220  in
                     (uu____5218, args1)
               else
                 (let uu____5233 = p_indexingTerm head1  in
                  (uu____5233, args))
                in
             (match uu____5119 with
              | (head_doc,args1) ->
                  let uu____5254 =
                    let uu____5255 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5255 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5254))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5275 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5275)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5293 =
               let uu____5294 = p_quident lid  in
               let uu____5295 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5294 uu____5295  in
             FStar_Pprint.group uu____5293
         | hd1::tl1 ->
             let uu____5312 =
               let uu____5313 =
                 let uu____5314 =
                   let uu____5315 = p_quident lid  in
                   let uu____5316 = p_argTerm hd1  in
                   prefix2 uu____5315 uu____5316  in
                 FStar_Pprint.group uu____5314  in
               let uu____5317 =
                 let uu____5318 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5318  in
               FStar_Pprint.op_Hat_Hat uu____5313 uu____5317  in
             FStar_Pprint.group uu____5312)
    | uu____5323 -> p_indexingTerm e

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
         (let uu____5332 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5332 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5334 = str "#"  in
        let uu____5335 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5334 uu____5335
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5337  ->
    match uu____5337 with | (e,uu____5343) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5348 =
        let uu____5349 = unparen e  in uu____5349.FStar_Parser_AST.tm  in
      match uu____5348 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5350;_},e1::e2::[])
          ->
          let uu____5355 =
            let uu____5356 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5357 =
              let uu____5358 =
                let uu____5359 = p_term e2  in
                soft_parens_with_nesting uu____5359  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5358  in
            FStar_Pprint.op_Hat_Hat uu____5356 uu____5357  in
          FStar_Pprint.group uu____5355
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5360;_},e1::e2::[])
          ->
          let uu____5365 =
            let uu____5366 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5367 =
              let uu____5368 =
                let uu____5369 = p_term e2  in
                soft_brackets_with_nesting uu____5369  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5368  in
            FStar_Pprint.op_Hat_Hat uu____5366 uu____5367  in
          FStar_Pprint.group uu____5365
      | uu____5370 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5373 =
      let uu____5374 = unparen e  in uu____5374.FStar_Parser_AST.tm  in
    match uu____5373 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5377 = p_quident lid  in
        let uu____5378 =
          let uu____5379 =
            let uu____5380 = p_term e1  in
            soft_parens_with_nesting uu____5380  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5379  in
        FStar_Pprint.op_Hat_Hat uu____5377 uu____5378
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5386 = str (FStar_Ident.text_of_id op)  in
        let uu____5387 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5386 uu____5387
    | uu____5388 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5390 =
      let uu____5391 = unparen e  in uu____5391.FStar_Parser_AST.tm  in
    match uu____5390 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____5396 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5403 = str (FStar_Ident.text_of_id op)  in
        let uu____5404 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5403 uu____5404
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5408 =
          let uu____5409 =
            let uu____5410 = str (FStar_Ident.text_of_id op)  in
            let uu____5411 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5410 uu____5411  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5409  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5408
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5426 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5427 =
          let uu____5428 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5429 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5428 p_tmEq uu____5429  in
        let uu____5436 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5426 uu____5427 uu____5436
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5439 =
          let uu____5440 = p_atomicTermNotQUident e1  in
          let uu____5441 =
            let uu____5442 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5442  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5440 uu____5441
           in
        FStar_Pprint.group uu____5439
    | uu____5443 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5445 =
      let uu____5446 = unparen e  in uu____5446.FStar_Parser_AST.tm  in
    match uu____5445 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5450 = p_quident constr_lid  in
        let uu____5451 =
          let uu____5452 =
            let uu____5453 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5453  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5452  in
        FStar_Pprint.op_Hat_Hat uu____5450 uu____5451
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5455 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5455 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5457 = p_term e1  in soft_parens_with_nesting uu____5457
    | uu____5458 when is_array e ->
        let es = extract_from_list e  in
        let uu____5462 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5463 =
          let uu____5464 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5464 p_noSeqTerm es  in
        let uu____5465 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5462 uu____5463 uu____5465
    | uu____5466 when is_list e ->
        let uu____5467 =
          let uu____5468 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5469 = extract_from_list e  in
          separate_map_or_flow uu____5468 p_noSeqTerm uu____5469  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5467 FStar_Pprint.rbracket
    | uu____5472 when is_lex_list e ->
        let uu____5473 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5474 =
          let uu____5475 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5476 = extract_from_list e  in
          separate_map_or_flow uu____5475 p_noSeqTerm uu____5476  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5473 uu____5474 FStar_Pprint.rbracket
    | uu____5479 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5483 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5484 =
          let uu____5485 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5485 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5483 uu____5484 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5489 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5490 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5489 uu____5490
    | FStar_Parser_AST.Op (op,args) when
        let uu____5497 = handleable_op op args  in
        Prims.op_Negation uu____5497 ->
        let uu____5498 =
          let uu____5499 =
            let uu____5500 =
              let uu____5501 =
                let uu____5502 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5502
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5501  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5500  in
          Prims.strcat "Operation " uu____5499  in
        failwith uu____5498
    | FStar_Parser_AST.Uvar uu____5503 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5504 = p_term e  in soft_parens_with_nesting uu____5504
    | FStar_Parser_AST.Const uu____5505 ->
        let uu____5506 = p_term e  in soft_parens_with_nesting uu____5506
    | FStar_Parser_AST.Op uu____5507 ->
        let uu____5514 = p_term e  in soft_parens_with_nesting uu____5514
    | FStar_Parser_AST.Tvar uu____5515 ->
        let uu____5516 = p_term e  in soft_parens_with_nesting uu____5516
    | FStar_Parser_AST.Var uu____5517 ->
        let uu____5518 = p_term e  in soft_parens_with_nesting uu____5518
    | FStar_Parser_AST.Name uu____5519 ->
        let uu____5520 = p_term e  in soft_parens_with_nesting uu____5520
    | FStar_Parser_AST.Construct uu____5521 ->
        let uu____5532 = p_term e  in soft_parens_with_nesting uu____5532
    | FStar_Parser_AST.Abs uu____5533 ->
        let uu____5540 = p_term e  in soft_parens_with_nesting uu____5540
    | FStar_Parser_AST.App uu____5541 ->
        let uu____5548 = p_term e  in soft_parens_with_nesting uu____5548
    | FStar_Parser_AST.Let uu____5549 ->
        let uu____5562 = p_term e  in soft_parens_with_nesting uu____5562
    | FStar_Parser_AST.LetOpen uu____5563 ->
        let uu____5568 = p_term e  in soft_parens_with_nesting uu____5568
    | FStar_Parser_AST.Seq uu____5569 ->
        let uu____5574 = p_term e  in soft_parens_with_nesting uu____5574
    | FStar_Parser_AST.Bind uu____5575 ->
        let uu____5582 = p_term e  in soft_parens_with_nesting uu____5582
    | FStar_Parser_AST.If uu____5583 ->
        let uu____5590 = p_term e  in soft_parens_with_nesting uu____5590
    | FStar_Parser_AST.Match uu____5591 ->
        let uu____5606 = p_term e  in soft_parens_with_nesting uu____5606
    | FStar_Parser_AST.TryWith uu____5607 ->
        let uu____5622 = p_term e  in soft_parens_with_nesting uu____5622
    | FStar_Parser_AST.Ascribed uu____5623 ->
        let uu____5632 = p_term e  in soft_parens_with_nesting uu____5632
    | FStar_Parser_AST.Record uu____5633 ->
        let uu____5646 = p_term e  in soft_parens_with_nesting uu____5646
    | FStar_Parser_AST.Project uu____5647 ->
        let uu____5652 = p_term e  in soft_parens_with_nesting uu____5652
    | FStar_Parser_AST.Product uu____5653 ->
        let uu____5660 = p_term e  in soft_parens_with_nesting uu____5660
    | FStar_Parser_AST.Sum uu____5661 ->
        let uu____5668 = p_term e  in soft_parens_with_nesting uu____5668
    | FStar_Parser_AST.QForall uu____5669 ->
        let uu____5682 = p_term e  in soft_parens_with_nesting uu____5682
    | FStar_Parser_AST.QExists uu____5683 ->
        let uu____5696 = p_term e  in soft_parens_with_nesting uu____5696
    | FStar_Parser_AST.Refine uu____5697 ->
        let uu____5702 = p_term e  in soft_parens_with_nesting uu____5702
    | FStar_Parser_AST.NamedTyp uu____5703 ->
        let uu____5708 = p_term e  in soft_parens_with_nesting uu____5708
    | FStar_Parser_AST.Requires uu____5709 ->
        let uu____5716 = p_term e  in soft_parens_with_nesting uu____5716
    | FStar_Parser_AST.Ensures uu____5717 ->
        let uu____5724 = p_term e  in soft_parens_with_nesting uu____5724
    | FStar_Parser_AST.Assign uu____5725 ->
        let uu____5730 = p_term e  in soft_parens_with_nesting uu____5730
    | FStar_Parser_AST.Attributes uu____5731 ->
        let uu____5734 = p_term e  in soft_parens_with_nesting uu____5734

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___106_5735  ->
    match uu___106_5735 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5739 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____5739
    | FStar_Const.Const_string (bytes,uu____5741) ->
        let uu____5746 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____5746
    | FStar_Const.Const_bytearray (bytes,uu____5748) ->
        let uu____5753 =
          let uu____5754 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____5754  in
        let uu____5755 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____5753 uu____5755
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_5773 =
          match uu___104_5773 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___105_5777 =
          match uu___105_5777 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5788  ->
               match uu____5788 with
               | (s,w) ->
                   let uu____5795 = signedness s  in
                   let uu____5796 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____5795 uu____5796)
            sign_width_opt
           in
        let uu____5797 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____5797 ending
    | FStar_Const.Const_range r ->
        let uu____5799 = FStar_Range.string_of_range r  in str uu____5799
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5801 = p_quident lid  in
        let uu____5802 =
          let uu____5803 =
            let uu____5804 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5804  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5803  in
        FStar_Pprint.op_Hat_Hat uu____5801 uu____5802

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5806 = str "u#"  in
    let uu____5807 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____5806 uu____5807

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5809 =
      let uu____5810 = unparen u  in uu____5810.FStar_Parser_AST.tm  in
    match uu____5809 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5811;_},u1::u2::[])
        ->
        let uu____5816 =
          let uu____5817 = p_universeFrom u1  in
          let uu____5818 =
            let uu____5819 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5819  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5817 uu____5818  in
        FStar_Pprint.group uu____5816
    | FStar_Parser_AST.App uu____5820 ->
        let uu____5827 = head_and_args u  in
        (match uu____5827 with
         | (head1,args) ->
             let uu____5852 =
               let uu____5853 = unparen head1  in
               uu____5853.FStar_Parser_AST.tm  in
             (match uu____5852 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____5855 =
                    let uu____5856 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____5857 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____5865  ->
                           match uu____5865 with
                           | (u1,uu____5871) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____5856 uu____5857  in
                  FStar_Pprint.group uu____5855
              | uu____5872 ->
                  let uu____5873 =
                    let uu____5874 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____5874
                     in
                  failwith uu____5873))
    | uu____5875 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5877 =
      let uu____5878 = unparen u  in uu____5878.FStar_Parser_AST.tm  in
    match uu____5877 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____5901 = p_universeFrom u1  in
        soft_parens_with_nesting uu____5901
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5902;_},uu____5903::uu____5904::[])
        ->
        let uu____5907 = p_universeFrom u  in
        soft_parens_with_nesting uu____5907
    | FStar_Parser_AST.App uu____5908 ->
        let uu____5915 = p_universeFrom u  in
        soft_parens_with_nesting uu____5915
    | uu____5916 ->
        let uu____5917 =
          let uu____5918 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____5918
           in
        failwith uu____5917

let term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_term e 
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
       | FStar_Parser_AST.Module (uu____5951,decls) ->
           let uu____5957 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____5957
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____5966,decls,uu____5968) ->
           let uu____5973 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____5973
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6016  ->
         match uu____6016 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6058,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6064,decls,uu____6066) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6102 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6115;
                 FStar_Parser_AST.doc = uu____6116;
                 FStar_Parser_AST.quals = uu____6117;
                 FStar_Parser_AST.attrs = uu____6118;_}::uu____6119 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6125 =
                   let uu____6128 =
                     let uu____6131 = FStar_List.tl ds  in d :: uu____6131
                      in
                   d0 :: uu____6128  in
                 (uu____6125, (d0.FStar_Parser_AST.drange))
             | uu____6136 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6102 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6197 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6197 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6290 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6290, comments1))))))
  