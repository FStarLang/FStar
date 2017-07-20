open Prims
let should_print_fs_typ_app : Prims.bool FStar_ST.ref =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____14 'Auu____15 .
    Prims.bool -> ('Auu____15 -> 'Auu____14) -> 'Auu____15 -> 'Auu____14
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.read should_print_fs_typ_app  in
        FStar_ST.write should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.write should_print_fs_typ_app b0; res)
  
let should_unparen : Prims.bool FStar_ST.ref = FStar_Util.mk_ref true 
let rec unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term =
  fun t  ->
    let uu____44 =
      let uu____45 = FStar_ST.read should_unparen  in
      Prims.op_Negation uu____45  in
    if uu____44
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____48 -> t)
  
let str : Prims.string -> FStar_Pprint.document =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____63 'Auu____64 .
    'Auu____64 ->
      ('Auu____63 -> 'Auu____64) ->
        'Auu____63 FStar_Pervasives_Native.option -> 'Auu____64
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
  'Auu____133 .
    FStar_Pprint.document ->
      ('Auu____133 -> FStar_Pprint.document) ->
        'Auu____133 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____155 =
          let uu____156 =
            let uu____157 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____157  in
          FStar_Pprint.separate_map uu____156 f l  in
        FStar_Pprint.group uu____155
  
let precede_break_separate_map :
  'Auu____168 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____168 -> FStar_Pprint.document) ->
          'Auu____168 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____194 =
            let uu____195 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____196 =
              let uu____197 = FStar_List.hd l  in
              FStar_All.pipe_right uu____197 f  in
            FStar_Pprint.precede uu____195 uu____196  in
          let uu____198 =
            let uu____199 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____205 =
                   let uu____206 =
                     let uu____207 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____207  in
                   FStar_Pprint.op_Hat_Hat sep uu____206  in
                 FStar_Pprint.op_Hat_Hat break1 uu____205) uu____199
             in
          FStar_Pprint.op_Hat_Hat uu____194 uu____198
  
let concat_break_map :
  'Auu____214 .
    ('Auu____214 -> FStar_Pprint.document) ->
      'Auu____214 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____232 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____236 = f x  in FStar_Pprint.op_Hat_Hat uu____236 break1)
          l
         in
      FStar_Pprint.group uu____232
  
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
    let uu____265 = str "begin"  in
    let uu____266 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____265 contents uu____266
  
let separate_map_or_flow :
  'Auu____275 .
    FStar_Pprint.document ->
      ('Auu____275 -> FStar_Pprint.document) ->
        'Auu____275 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____316 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____316 -> FStar_Pprint.document) ->
                  'Auu____316 Prims.list -> FStar_Pprint.document
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
                    (let uu____361 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____361
                       closing)
  
let doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____375  ->
    match uu____375 with
    | (comment,keywords) ->
        let uu____400 =
          let uu____401 =
            let uu____404 = str comment  in
            let uu____405 =
              let uu____408 =
                let uu____411 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____420  ->
                       match uu____420 with
                       | (k,v1) ->
                           let uu____427 =
                             let uu____430 = str k  in
                             let uu____431 =
                               let uu____434 =
                                 let uu____437 = str v1  in [uu____437]  in
                               FStar_Pprint.rarrow :: uu____434  in
                             uu____430 :: uu____431  in
                           FStar_Pprint.concat uu____427) keywords
                   in
                [uu____411]  in
              FStar_Pprint.space :: uu____408  in
            uu____404 :: uu____405  in
          FStar_Pprint.concat uu____401  in
        FStar_Pprint.group uu____400
  
let is_unit : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____442 =
      let uu____443 = unparen e  in uu____443.FStar_Parser_AST.tm  in
    match uu____442 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____444 -> false
  
let matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool =
  fun t  ->
    fun x  ->
      let uu____453 =
        let uu____454 = unparen t  in uu____454.FStar_Parser_AST.tm  in
      match uu____453 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____456 -> false
  
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
        let uu____478 =
          let uu____479 = unparen e  in uu____479.FStar_Parser_AST.tm  in
        match uu____478 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____492::(e2,uu____494)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____517 -> false  in
      aux
  
let is_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let is_lex_list : FStar_Parser_AST.term -> Prims.bool =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____530 =
      let uu____531 = unparen e  in uu____531.FStar_Parser_AST.tm  in
    match uu____530 with
    | FStar_Parser_AST.Construct (uu____534,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____545,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____566 = extract_from_list e2  in e1 :: uu____566
    | uu____569 ->
        let uu____570 =
          let uu____571 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____571  in
        failwith uu____570
  
let is_array : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____578 =
      let uu____579 = unparen e  in uu____579.FStar_Parser_AST.tm  in
    match uu____578 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____581;
           FStar_Parser_AST.level = uu____582;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____584 -> false
  
let rec is_ref_set : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____589 =
      let uu____590 = unparen e  in uu____590.FStar_Parser_AST.tm  in
    match uu____589 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.tset_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____593;
           FStar_Parser_AST.level = uu____594;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_ref_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____596;
                                                        FStar_Parser_AST.level
                                                          = uu____597;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____599;
                                                   FStar_Parser_AST.level =
                                                     uu____600;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____602;
                FStar_Parser_AST.level = uu____603;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____605;
           FStar_Parser_AST.level = uu____606;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid
            FStar_Parser_Const.tset_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____608 -> false
  
let rec extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list =
  fun e  ->
    let uu____615 =
      let uu____616 = unparen e  in uu____616.FStar_Parser_AST.tm  in
    match uu____615 with
    | FStar_Parser_AST.Var uu____619 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____620;
           FStar_Parser_AST.range = uu____621;
           FStar_Parser_AST.level = uu____622;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____623;
                                                        FStar_Parser_AST.range
                                                          = uu____624;
                                                        FStar_Parser_AST.level
                                                          = uu____625;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____627;
                                                   FStar_Parser_AST.level =
                                                     uu____628;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____629;
                FStar_Parser_AST.range = uu____630;
                FStar_Parser_AST.level = uu____631;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____633;
           FStar_Parser_AST.level = uu____634;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____636 = extract_from_ref_set e1  in
        let uu____639 = extract_from_ref_set e2  in
        FStar_List.append uu____636 uu____639
    | uu____642 ->
        let uu____643 =
          let uu____644 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____644  in
        failwith uu____643
  
let is_general_application : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____651 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____651
  
let is_general_construction : FStar_Parser_AST.term -> Prims.bool =
  fun e  ->
    let uu____656 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____656
  
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
      let uu____705 =
        let uu____706 = unparen e1  in uu____706.FStar_Parser_AST.tm  in
      match uu____705 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____724 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc 
let uu___is_Left : associativity -> Prims.bool =
  fun projectee  -> match projectee with | Left  -> true | uu____739 -> false 
let uu___is_Right : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | Right  -> true | uu____744 -> false
  
let uu___is_NonAssoc : associativity -> Prims.bool =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____749 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2
let token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string =
  fun uu___93_767  ->
    match uu___93_767 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool
  =
  fun s  ->
    fun uu___94_785  ->
      match uu___94_785 with
      | FStar_Util.Inl c ->
          let uu____791 = FStar_String.get s (Prims.parse_int "0")  in
          uu____791 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____799 .
    Prims.string ->
      ('Auu____799,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____817  ->
      match uu____817 with
      | (assoc_levels,tokens) ->
          let uu____842 = FStar_List.tryFind (matches_token s) tokens  in
          uu____842 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____865 .
    Prims.unit ->
      (associativity,('Auu____865,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____876  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____893 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____893) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____904  ->
    (Left, [FStar_Util.Inl '*'; FStar_Util.Inl '/'; FStar_Util.Inl '%'])
  
let opinfix2 :
  'Auu____929 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____929) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____940  -> (Left, [FStar_Util.Inl '+'; FStar_Util.Inl '-']) 
let minus_lvl :
  'Auu____961 .
    Prims.unit ->
      (associativity,('Auu____961,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____972  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____989 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____989) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1000  -> (Right, [FStar_Util.Inl '@'; FStar_Util.Inl '^']) 
let pipe_right :
  'Auu____1021 .
    Prims.unit ->
      (associativity,('Auu____1021,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1032  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1049 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1049) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1060  -> (Left, [FStar_Util.Inl '$']) 
let opinfix0c :
  'Auu____1077 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1077) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1088  ->
    (Left, [FStar_Util.Inl '='; FStar_Util.Inl '<'; FStar_Util.Inl '>'])
  
let equal :
  'Auu____1113 .
    Prims.unit ->
      (associativity,('Auu____1113,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1124  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1141 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1141) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1152  -> (Left, [FStar_Util.Inl '&']) 
let opinfix0a :
  'Auu____1169 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1169) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1180  -> (Left, [FStar_Util.Inl '|']) 
let colon_equals :
  'Auu____1197 .
    Prims.unit ->
      (associativity,('Auu____1197,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1208  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1225 .
    Prims.unit ->
      (associativity,('Auu____1225,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1236  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1253 .
    Prims.unit ->
      (associativity,('Auu____1253,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1264  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___95_1451 =
    match uu___95_1451 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1489  ->
         match uu____1489 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1566 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1566 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1614) ->
          assoc_levels
      | uu____1655 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let max : Prims.int -> Prims.int -> Prims.int =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1693 .
    ('Auu____1693,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1749 =
        FStar_List.tryFind
          (fun uu____1787  ->
             match uu____1787 with
             | (uu____1804,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1749 with
      | FStar_Pervasives_Native.Some ((uu____1842,l1,uu____1844),uu____1845)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____1896 =
            let uu____1897 =
              let uu____1898 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____1898  in
            FStar_Util.format1 "Undefined associativity level %s" uu____1897
             in
          failwith uu____1896
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____1932 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1932) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____1945  ->
    [Obj.magic (opinfix0a ());
    Obj.magic (opinfix0b ());
    Obj.magic (opinfix0c ());
    Obj.magic (opinfix0d ());
    Obj.magic (opinfix1 ());
    Obj.magic (opinfix2 ())]
  
let is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool =
  fun op  ->
    let uu____2020 =
      let uu____2033 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2033 (Obj.magic (operatorInfix0ad12 ()))  in
    uu____2020 <> FStar_Pervasives_Native.None
  
let is_operatorInfix34 : FStar_Ident.ident -> Prims.bool =
  let opinfix34 = [Obj.magic (opinfix3 ()); Obj.magic (opinfix4 ())]  in
  fun op  ->
    let uu____2137 =
      let uu____2150 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2150 opinfix34  in
    uu____2137 <> FStar_Pervasives_Native.None
  
let handleable_args_length : FStar_Ident.ident -> Prims.int =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2212 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2212
    then (Prims.parse_int "1")
    else
      (let uu____2214 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2214
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2223 . FStar_Ident.ident -> 'Auu____2223 Prims.list -> Prims.bool =
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
      | uu____2236 -> false
  
let comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2264 .
    ('Auu____2264 -> FStar_Pprint.document) ->
      'Auu____2264 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2296 = FStar_ST.read comment_stack  in
          match uu____2296 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2330 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2330
              then
                (FStar_ST.write comment_stack cs;
                 (let uu____2342 =
                    let uu____2343 =
                      let uu____2344 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2344
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2343  in
                  comments_before_pos uu____2342 print_pos lookahead_pos))
              else
                (let uu____2346 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2346))
           in
        let uu____2347 =
          let uu____2352 =
            let uu____2353 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2353  in
          let uu____2354 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2352 uu____2354  in
        match uu____2347 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2360 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2360
              else comments  in
            let uu____2366 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2366
  
let rec place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2383 = FStar_ST.read comment_stack  in
          match uu____2383 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.write comment_stack cs;
               (let lnum =
                  let uu____2417 =
                    let uu____2418 =
                      let uu____2419 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2419  in
                    uu____2418 - lbegin  in
                  max k uu____2417  in
                let doc2 =
                  let uu____2421 =
                    let uu____2422 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2423 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2422 uu____2423  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2421  in
                let uu____2424 =
                  let uu____2425 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2425  in
                place_comments_until_pos (Prims.parse_int "1") uu____2424
                  pos_end doc2))
          | uu____2426 ->
              let lnum =
                let uu____2434 =
                  let uu____2435 = FStar_Range.line_of_pos pos_end  in
                  uu____2435 - lbegin  in
                max (Prims.parse_int "1") uu____2434  in
              let uu____2436 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2436
  
let separate_map_with_comments :
  'Auu____2449 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2449 -> FStar_Pprint.document) ->
          'Auu____2449 Prims.list ->
            ('Auu____2449 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2497 x =
              match uu____2497 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2511 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2511 doc1
                     in
                  let uu____2512 =
                    let uu____2513 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2513  in
                  let uu____2514 =
                    let uu____2515 =
                      let uu____2516 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2516  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2515  in
                  (uu____2512, uu____2514)
               in
            let uu____2517 =
              let uu____2524 = FStar_List.hd xs  in
              let uu____2525 = FStar_List.tl xs  in (uu____2524, uu____2525)
               in
            match uu____2517 with
            | (x,xs1) ->
                let init1 =
                  let uu____2541 =
                    let uu____2542 =
                      let uu____2543 = extract_range x  in
                      FStar_Range.end_of_range uu____2543  in
                    FStar_Range.line_of_pos uu____2542  in
                  let uu____2544 =
                    let uu____2545 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2545  in
                  (uu____2541, uu____2544)  in
                let uu____2546 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2546
  
let rec p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    let uu____2833 =
      let uu____2834 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____2835 =
        let uu____2836 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____2837 =
          let uu____2838 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____2839 =
            let uu____2840 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____2840
             in
          FStar_Pprint.op_Hat_Hat uu____2838 uu____2839  in
        FStar_Pprint.op_Hat_Hat uu____2836 uu____2837  in
      FStar_Pprint.op_Hat_Hat uu____2834 uu____2835  in
    FStar_Pprint.group uu____2833

and p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document =
  fun attrs  ->
    let uu____2843 =
      let uu____2844 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____2844  in
    let uu____2845 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_separate_map (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____2843 FStar_Pprint.space uu____2845
      p_atomicTerm attrs

and p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document =
  fun uu____2846  ->
    match uu____2846 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____2880 =
                match uu____2880 with
                | (kwd,arg) ->
                    let uu____2887 = str "@"  in
                    let uu____2888 =
                      let uu____2889 = str kwd  in
                      let uu____2890 =
                        let uu____2891 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2891
                         in
                      FStar_Pprint.op_Hat_Hat uu____2889 uu____2890  in
                    FStar_Pprint.op_Hat_Hat uu____2887 uu____2888
                 in
              let uu____2892 =
                let uu____2893 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____2893 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2892
           in
        let uu____2898 =
          let uu____2899 =
            let uu____2900 =
              let uu____2901 =
                let uu____2902 = str doc1  in
                let uu____2903 =
                  let uu____2904 =
                    let uu____2905 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2905  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____2904  in
                FStar_Pprint.op_Hat_Hat uu____2902 uu____2903  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2901  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____2900  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____2899  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____2898

and p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____2908 =
          let uu____2909 = str "open"  in
          let uu____2910 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2909 uu____2910  in
        FStar_Pprint.group uu____2908
    | FStar_Parser_AST.Include uid ->
        let uu____2912 =
          let uu____2913 = str "include"  in
          let uu____2914 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____2913 uu____2914  in
        FStar_Pprint.group uu____2912
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____2917 =
          let uu____2918 = str "module"  in
          let uu____2919 =
            let uu____2920 =
              let uu____2921 = p_uident uid1  in
              let uu____2922 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____2921 uu____2922  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2920  in
          FStar_Pprint.op_Hat_Hat uu____2918 uu____2919  in
        let uu____2923 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____2917 uu____2923
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____2925 =
          let uu____2926 = str "module"  in
          let uu____2927 =
            let uu____2928 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2928  in
          FStar_Pprint.op_Hat_Hat uu____2926 uu____2927  in
        FStar_Pprint.group uu____2925
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____2961 = str "effect"  in
          let uu____2962 =
            let uu____2963 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____2963  in
          FStar_Pprint.op_Hat_Hat uu____2961 uu____2962  in
        let uu____2964 =
          let uu____2965 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____2965 FStar_Pprint.equals
           in
        let uu____2966 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____2964 uu____2966
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____2984 = str "type"  in
        let uu____2985 = str "and"  in
        precede_break_separate_map uu____2984 uu____2985 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3007 = str "let"  in
          let uu____3008 =
            let uu____3009 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3009 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3007 uu____3008  in
        let uu____3010 =
          let uu____3011 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3011 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3010 p_letbinding lbs
          (fun uu____3019  ->
             match uu____3019 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3028 =
          let uu____3029 = str "val"  in
          let uu____3030 =
            let uu____3031 =
              let uu____3032 = p_lident lid  in
              let uu____3033 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3032 uu____3033  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3031  in
          FStar_Pprint.op_Hat_Hat uu____3029 uu____3030  in
        let uu____3034 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3028 uu____3034
    | FStar_Parser_AST.Assume (id,t) ->
        let decl_keyword =
          let uu____3038 =
            let uu____3039 =
              FStar_Util.char_at id.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3039 FStar_Util.is_upper  in
          if uu____3038
          then FStar_Pprint.empty
          else
            (let uu____3041 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3041 FStar_Pprint.space)
           in
        let uu____3042 =
          let uu____3043 =
            let uu____3044 = p_ident id  in
            let uu____3045 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3044 uu____3045  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3043  in
        let uu____3046 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3042 uu____3046
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3053 = str "exception"  in
        let uu____3054 =
          let uu____3055 =
            let uu____3056 = p_uident uid  in
            let uu____3057 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3062 = str "of"  in
                   let uu____3063 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3062 uu____3063) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3056 uu____3057  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3055  in
        FStar_Pprint.op_Hat_Hat uu____3053 uu____3054
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3065 = str "new_effect"  in
        let uu____3066 =
          let uu____3067 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3067  in
        FStar_Pprint.op_Hat_Hat uu____3065 uu____3066
    | FStar_Parser_AST.SubEffect se ->
        let uu____3069 = str "sub_effect"  in
        let uu____3070 =
          let uu____3071 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3071  in
        FStar_Pprint.op_Hat_Hat uu____3069 uu____3070
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3074 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3074 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3075 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3076) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document =
  fun uu___96_3093  ->
    match uu___96_3093 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3095 = str "#set-options"  in
        let uu____3096 =
          let uu____3097 =
            let uu____3098 = str s  in FStar_Pprint.dquotes uu____3098  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3097  in
        FStar_Pprint.op_Hat_Hat uu____3095 uu____3096
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3102 = str "#reset-options"  in
        let uu____3103 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3107 =
                 let uu____3108 = str s  in FStar_Pprint.dquotes uu____3108
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3107) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3102 uu____3103
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.write should_print_fs_typ_app true; str "#light \"off\"")

and p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document =
  fun bs  -> p_binders true bs

and p_fsdocTypeDeclPairs :
  (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                            FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3113  ->
    match uu____3113 with
    | (typedecl,fsdoc_opt) ->
        let uu____3126 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3127 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3126 uu____3127

and p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document =
  fun uu___97_3128  ->
    match uu___97_3128 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3143 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3159 =
          let uu____3160 = p_typ t  in prefix2 FStar_Pprint.equals uu____3160
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3204 =
          match uu____3204 with
          | (lid1,t,doc_opt) ->
              let uu____3220 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3220
           in
        let p_fields uu____3234 =
          let uu____3235 =
            let uu____3236 =
              let uu____3237 =
                let uu____3238 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3238 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3237  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3236  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3235  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3302 =
          match uu____3302 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3328 =
                  let uu____3329 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3329  in
                FStar_Range.extend_to_end_of_line uu____3328  in
              let p_constructorBranch decl =
                let uu____3362 =
                  let uu____3363 =
                    let uu____3364 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3364  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3363  in
                FStar_Pprint.group uu____3362  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3384 =
          let uu____3385 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3385  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3400  ->
             let uu____3401 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3401)

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
            let uu____3416 = p_ident lid  in
            let uu____3417 =
              let uu____3418 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3418  in
            FStar_Pprint.op_Hat_Hat uu____3416 uu____3417
          else
            (let binders_doc =
               let uu____3421 = p_typars bs  in
               let uu____3422 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3426 =
                        let uu____3427 =
                          let uu____3428 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3428
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3427
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3426) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3421 uu____3422  in
             let uu____3429 = p_ident lid  in
             let uu____3430 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3429 binders_doc uu____3430)

and p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____3431  ->
    match uu____3431 with
    | (lid,t,doc_opt) ->
        let uu____3447 =
          let uu____3448 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____3449 =
            let uu____3450 = p_lident lid  in
            let uu____3451 =
              let uu____3452 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3452  in
            FStar_Pprint.op_Hat_Hat uu____3450 uu____3451  in
          FStar_Pprint.op_Hat_Hat uu____3448 uu____3449  in
        FStar_Pprint.group uu____3447

and p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document
  =
  fun uu____3453  ->
    match uu____3453 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3481 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3482 =
          let uu____3483 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3484 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3489 =
                   let uu____3490 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3490  in
                 let uu____3491 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____3489 uu____3491) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3483 uu____3484  in
        FStar_Pprint.op_Hat_Hat uu____3481 uu____3482

and p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document
  =
  fun uu____3492  ->
    match uu____3492 with
    | (pat,e) ->
        let pat_doc =
          let uu____3500 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed (pat1,t) ->
                let uu____3511 =
                  let uu____3512 =
                    let uu____3513 =
                      let uu____3514 =
                        let uu____3515 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3515
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3514
                       in
                    FStar_Pprint.group uu____3513  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3512  in
                (pat1, uu____3511)
            | uu____3516 -> (pat, FStar_Pprint.empty)  in
          match uu____3500 with
          | (pat1,ascr_doc) ->
              (match pat1.FStar_Parser_AST.pat with
               | FStar_Parser_AST.PatApp
                   ({
                      FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                        (x,uu____3520);
                      FStar_Parser_AST.prange = uu____3521;_},pats)
                   ->
                   let uu____3531 = p_lident x  in
                   let uu____3532 =
                     let uu____3533 =
                       FStar_Pprint.separate_map break1 p_atomicPattern pats
                        in
                     FStar_Pprint.op_Hat_Hat uu____3533 ascr_doc  in
                   FStar_Pprint.surround (Prims.parse_int "2")
                     (Prims.parse_int "1") uu____3531 uu____3532
                     FStar_Pprint.equals
               | uu____3534 ->
                   let uu____3535 =
                     let uu____3536 = p_tuplePattern pat1  in
                     let uu____3537 =
                       FStar_Pprint.op_Hat_Slash_Hat ascr_doc
                         FStar_Pprint.equals
                        in
                     FStar_Pprint.op_Hat_Hat uu____3536 uu____3537  in
                   FStar_Pprint.group uu____3535)
           in
        let uu____3538 = p_term e  in prefix2 pat_doc uu____3538

and p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document =
  fun uu___98_3539  ->
    match uu___98_3539 with
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
        let uu____3564 = p_uident uid  in
        let uu____3565 = p_binders true bs  in
        let uu____3566 =
          let uu____3567 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____3567  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3564 uu____3565 uu____3566

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
          let uu____3576 =
            let uu____3577 =
              let uu____3578 =
                let uu____3579 = p_uident uid  in
                let uu____3580 = p_binders true bs  in
                let uu____3581 =
                  let uu____3582 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____3582  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____3579 uu____3580 uu____3581
                 in
              FStar_Pprint.group uu____3578  in
            let uu____3583 =
              let uu____3584 = str "with"  in
              let uu____3585 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____3584 uu____3585  in
            FStar_Pprint.op_Hat_Slash_Hat uu____3577 uu____3583  in
          braces_with_nesting uu____3576

and p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____3615 =
          let uu____3616 = p_lident lid  in
          let uu____3617 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____3616 uu____3617  in
        let uu____3618 = p_simpleTerm e  in prefix2 uu____3615 uu____3618
    | uu____3619 ->
        let uu____3620 =
          let uu____3621 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____3621
           in
        failwith uu____3620

and p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____3676 =
        match uu____3676 with
        | (kwd,t) ->
            let uu____3683 =
              let uu____3684 = str kwd  in
              let uu____3685 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3684 uu____3685  in
            let uu____3686 = p_simpleTerm t  in prefix2 uu____3683 uu____3686
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____3691 =
      let uu____3692 =
        let uu____3693 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____3694 =
          let uu____3695 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3695  in
        FStar_Pprint.op_Hat_Hat uu____3693 uu____3694  in
      let uu____3696 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____3692 uu____3696  in
    let uu____3697 =
      let uu____3698 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3698  in
    FStar_Pprint.op_Hat_Hat uu____3691 uu____3697

and p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document =
  fun uu___99_3699  ->
    match uu___99_3699 with
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
    let uu____3701 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____3701

and p_letqualifier : FStar_Parser_AST.let_qualifier -> FStar_Pprint.document
  =
  fun uu___100_3702  ->
    match uu___100_3702 with
    | FStar_Parser_AST.Rec  ->
        let uu____3703 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3703
    | FStar_Parser_AST.Mutable  ->
        let uu____3704 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3704
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document =
  fun uu___101_3705  ->
    match uu___101_3705 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and p_disjunctivePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____3710 =
          let uu____3711 =
            let uu____3712 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____3712  in
          FStar_Pprint.separate_map uu____3711 p_tuplePattern pats  in
        FStar_Pprint.group uu____3710
    | uu____3713 -> p_tuplePattern p

and p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____3720 =
          let uu____3721 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____3721 p_constructorPattern pats  in
        FStar_Pprint.group uu____3720
    | uu____3722 -> p_constructorPattern p

and p_constructorPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document
  =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____3725;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____3730 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____3731 = p_constructorPattern hd1  in
        let uu____3732 = p_constructorPattern tl1  in
        infix0 uu____3730 uu____3731 uu____3732
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____3734;_},pats)
        ->
        let uu____3740 = p_quident uid  in
        let uu____3741 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____3740 uu____3741
    | uu____3742 -> p_atomicPattern p

and p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____3746 =
          let uu____3751 =
            let uu____3752 = unparen t  in uu____3752.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____3751)  in
        (match uu____3746 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____3757;
               FStar_Parser_AST.blevel = uu____3758;
               FStar_Parser_AST.aqual = uu____3759;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____3765 =
               let uu____3766 = p_ident lid  in
               p_refinement aqual uu____3766 t1 phi  in
             soft_parens_with_nesting uu____3765
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____3768;
               FStar_Parser_AST.blevel = uu____3769;
               FStar_Parser_AST.aqual = uu____3770;_},phi))
             ->
             let uu____3772 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____3772
         | uu____3773 ->
             let uu____3778 =
               let uu____3779 = p_tuplePattern pat  in
               let uu____3780 =
                 let uu____3781 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____3782 =
                   let uu____3783 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3783  in
                 FStar_Pprint.op_Hat_Hat uu____3781 uu____3782  in
               FStar_Pprint.op_Hat_Hat uu____3779 uu____3780  in
             soft_parens_with_nesting uu____3778)
    | FStar_Parser_AST.PatList pats ->
        let uu____3787 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____3787 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____3802 =
          match uu____3802 with
          | (lid,pat) ->
              let uu____3809 = p_qlident lid  in
              let uu____3810 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____3809 uu____3810
           in
        let uu____3811 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____3811
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____3821 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____3822 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____3823 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____3821 uu____3822 uu____3823
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____3834 =
          let uu____3835 =
            let uu____3836 = str (FStar_Ident.text_of_id op)  in
            let uu____3837 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____3836 uu____3837  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3835  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3834
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____3845 = FStar_Pprint.optional p_aqual aqual  in
        let uu____3846 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____3845 uu____3846
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____3848 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____3851;
           FStar_Parser_AST.prange = uu____3852;_},uu____3853)
        ->
        let uu____3858 = p_tuplePattern p  in
        soft_parens_with_nesting uu____3858
    | FStar_Parser_AST.PatTuple (uu____3859,false ) ->
        let uu____3864 = p_tuplePattern p  in
        soft_parens_with_nesting uu____3864
    | uu____3865 ->
        let uu____3866 =
          let uu____3867 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____3867  in
        failwith uu____3866

and p_binder : Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document
  =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____3871 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____3872 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____3871 uu____3872
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____3877 =
              let uu____3878 = unparen t  in uu____3878.FStar_Parser_AST.tm
               in
            match uu____3877 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____3881;
                   FStar_Parser_AST.blevel = uu____3882;
                   FStar_Parser_AST.aqual = uu____3883;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____3885 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____3885 t1 phi
            | uu____3886 ->
                let uu____3887 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____3888 =
                  let uu____3889 = p_lident lid  in
                  let uu____3890 =
                    let uu____3891 =
                      let uu____3892 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____3893 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____3892 uu____3893  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3891  in
                  FStar_Pprint.op_Hat_Hat uu____3889 uu____3890  in
                FStar_Pprint.op_Hat_Hat uu____3887 uu____3888
             in
          if is_atomic
          then
            let uu____3894 =
              let uu____3895 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3895  in
            FStar_Pprint.group uu____3894
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____3897 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____3903 =
            let uu____3904 = unparen t  in uu____3904.FStar_Parser_AST.tm  in
          (match uu____3903 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____3906;
                  FStar_Parser_AST.blevel = uu____3907;
                  FStar_Parser_AST.aqual = uu____3908;_},phi)
               ->
               if is_atomic
               then
                 let uu____3910 =
                   let uu____3911 =
                     let uu____3912 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____3912 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3911  in
                 FStar_Pprint.group uu____3910
               else
                 (let uu____3914 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____3914)
           | uu____3915 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____3923 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____3924 =
            let uu____3925 =
              let uu____3926 =
                let uu____3927 = p_appTerm t  in
                let uu____3928 =
                  let uu____3929 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____3929  in
                FStar_Pprint.op_Hat_Hat uu____3927 uu____3928  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3926  in
            FStar_Pprint.op_Hat_Hat binder uu____3925  in
          FStar_Pprint.op_Hat_Hat uu____3923 uu____3924

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
    let uu____3943 =
      let uu____3944 = unparen e  in uu____3944.FStar_Parser_AST.tm  in
    match uu____3943 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____3947 =
          let uu____3948 =
            let uu____3949 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____3949 FStar_Pprint.semi  in
          FStar_Pprint.group uu____3948  in
        let uu____3950 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____3947 uu____3950
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____3954 =
          let uu____3955 =
            let uu____3956 =
              let uu____3957 = p_lident x  in
              let uu____3958 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____3957 uu____3958  in
            let uu____3959 =
              let uu____3960 = p_noSeqTerm e1  in
              let uu____3961 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____3960 uu____3961  in
            op_Hat_Slash_Plus_Hat uu____3956 uu____3959  in
          FStar_Pprint.group uu____3955  in
        let uu____3962 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____3954 uu____3962
    | uu____3963 ->
        let uu____3964 = p_noSeqTerm e  in FStar_Pprint.group uu____3964

and p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____3967 =
      let uu____3968 = unparen e  in uu____3968.FStar_Parser_AST.tm  in
    match uu____3967 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____3973 =
          let uu____3974 = p_tmIff e1  in
          let uu____3975 =
            let uu____3976 =
              let uu____3977 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3977  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____3976  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3974 uu____3975  in
        FStar_Pprint.group uu____3973
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____3983 =
          let uu____3984 = p_tmIff e1  in
          let uu____3985 =
            let uu____3986 =
              let uu____3987 =
                let uu____3988 = p_typ t  in
                let uu____3989 =
                  let uu____3990 = str "by"  in
                  let uu____3991 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____3990 uu____3991  in
                FStar_Pprint.op_Hat_Slash_Hat uu____3988 uu____3989  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____3987  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____3986  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3984 uu____3985  in
        FStar_Pprint.group uu____3983
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____3992;_},e1::e2::e3::[])
        ->
        let uu____3998 =
          let uu____3999 =
            let uu____4000 =
              let uu____4001 = p_atomicTermNotQUident e1  in
              let uu____4002 =
                let uu____4003 =
                  let uu____4004 =
                    let uu____4005 = p_term e2  in
                    soft_parens_with_nesting uu____4005  in
                  let uu____4006 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4004 uu____4006  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4003  in
              FStar_Pprint.op_Hat_Hat uu____4001 uu____4002  in
            FStar_Pprint.group uu____4000  in
          let uu____4007 =
            let uu____4008 = p_noSeqTerm e3  in jump2 uu____4008  in
          FStar_Pprint.op_Hat_Hat uu____3999 uu____4007  in
        FStar_Pprint.group uu____3998
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4009;_},e1::e2::e3::[])
        ->
        let uu____4015 =
          let uu____4016 =
            let uu____4017 =
              let uu____4018 = p_atomicTermNotQUident e1  in
              let uu____4019 =
                let uu____4020 =
                  let uu____4021 =
                    let uu____4022 = p_term e2  in
                    soft_brackets_with_nesting uu____4022  in
                  let uu____4023 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4021 uu____4023  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4020  in
              FStar_Pprint.op_Hat_Hat uu____4018 uu____4019  in
            FStar_Pprint.group uu____4017  in
          let uu____4024 =
            let uu____4025 = p_noSeqTerm e3  in jump2 uu____4025  in
          FStar_Pprint.op_Hat_Hat uu____4016 uu____4024  in
        FStar_Pprint.group uu____4015
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4035 =
          let uu____4036 = str "requires"  in
          let uu____4037 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4036 uu____4037  in
        FStar_Pprint.group uu____4035
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4047 =
          let uu____4048 = str "ensures"  in
          let uu____4049 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4048 uu____4049  in
        FStar_Pprint.group uu____4047
    | FStar_Parser_AST.Attributes es ->
        let uu____4053 =
          let uu____4054 = str "attributes"  in
          let uu____4055 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4054 uu____4055  in
        FStar_Pprint.group uu____4053
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4059 = is_unit e3  in
        if uu____4059
        then
          let uu____4060 =
            let uu____4061 =
              let uu____4062 = str "if"  in
              let uu____4063 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4062 uu____4063  in
            let uu____4064 =
              let uu____4065 = str "then"  in
              let uu____4066 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4065 uu____4066  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4061 uu____4064  in
          FStar_Pprint.group uu____4060
        else
          (let e2_doc =
             let uu____4069 =
               let uu____4070 = unparen e2  in uu____4070.FStar_Parser_AST.tm
                in
             match uu____4069 with
             | FStar_Parser_AST.If (uu____4071,uu____4072,e31) when
                 is_unit e31 ->
                 let uu____4074 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4074
             | uu____4075 -> p_noSeqTerm e2  in
           let uu____4076 =
             let uu____4077 =
               let uu____4078 = str "if"  in
               let uu____4079 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4078 uu____4079  in
             let uu____4080 =
               let uu____4081 =
                 let uu____4082 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4082 e2_doc  in
               let uu____4083 =
                 let uu____4084 = str "else"  in
                 let uu____4085 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4084 uu____4085  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4081 uu____4083  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4077 uu____4080  in
           FStar_Pprint.group uu____4076)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4108 =
          let uu____4109 =
            let uu____4110 = str "try"  in
            let uu____4111 = p_noSeqTerm e1  in prefix2 uu____4110 uu____4111
             in
          let uu____4112 =
            let uu____4113 = str "with"  in
            let uu____4114 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4113 uu____4114  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4109 uu____4112  in
        FStar_Pprint.group uu____4108
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4145 =
          let uu____4146 =
            let uu____4147 = str "match"  in
            let uu____4148 = p_noSeqTerm e1  in
            let uu____4149 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4147 uu____4148 uu____4149
             in
          let uu____4150 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4146 uu____4150  in
        FStar_Pprint.group uu____4145
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4161 =
          let uu____4162 =
            let uu____4163 = str "let open"  in
            let uu____4164 = p_quident uid  in
            let uu____4165 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4163 uu____4164 uu____4165
             in
          let uu____4166 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4162 uu____4166  in
        FStar_Pprint.group uu____4161
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4183 = str "let"  in
          let uu____4184 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4183 uu____4184  in
        let uu____4185 =
          let uu____4186 =
            let uu____4187 =
              let uu____4188 = str "and"  in
              precede_break_separate_map let_doc uu____4188 p_letbinding lbs
               in
            let uu____4193 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4187 uu____4193  in
          FStar_Pprint.group uu____4186  in
        let uu____4194 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4185 uu____4194
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4197;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4200;
                                                         FStar_Parser_AST.level
                                                           = uu____4201;_})
        when matches_var maybe_x x ->
        let uu____4228 =
          let uu____4229 = str "function"  in
          let uu____4230 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4229 uu____4230  in
        FStar_Pprint.group uu____4228
    | FStar_Parser_AST.Assign (id,e1) ->
        let uu____4241 =
          let uu____4242 = p_lident id  in
          let uu____4243 =
            let uu____4244 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4244  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4242 uu____4243  in
        FStar_Pprint.group uu____4241
    | uu____4245 -> p_typ e

and p_typ : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4248 =
      let uu____4249 = unparen e  in uu____4249.FStar_Parser_AST.tm  in
    match uu____4248 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4265 =
          let uu____4266 =
            let uu____4267 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4267 FStar_Pprint.space  in
          let uu____4268 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4266 uu____4268 FStar_Pprint.dot
           in
        let uu____4269 =
          let uu____4270 = p_trigger trigger  in
          let uu____4271 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4270 uu____4271  in
        prefix2 uu____4265 uu____4269
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4287 =
          let uu____4288 =
            let uu____4289 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4289 FStar_Pprint.space  in
          let uu____4290 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4288 uu____4290 FStar_Pprint.dot
           in
        let uu____4291 =
          let uu____4292 = p_trigger trigger  in
          let uu____4293 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4292 uu____4293  in
        prefix2 uu____4287 uu____4291
    | uu____4294 -> p_simpleTerm e

and p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4296 =
      let uu____4297 = unparen e  in uu____4297.FStar_Parser_AST.tm  in
    match uu____4296 with
    | FStar_Parser_AST.QForall uu____4298 -> str "forall"
    | FStar_Parser_AST.QExists uu____4311 -> str "exists"
    | uu____4324 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun uu___102_4325  ->
    match uu___102_4325 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4337 =
          let uu____4338 =
            let uu____4339 = str "pattern"  in
            let uu____4340 =
              let uu____4341 =
                let uu____4342 = p_disjunctivePats pats  in jump2 uu____4342
                 in
              let uu____4343 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4341 uu____4343  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4339 uu____4340  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4338  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4337

and p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4349 = str "\\/"  in
    FStar_Pprint.separate_map uu____4349 p_conjunctivePats pats

and p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document =
  fun pats  ->
    let uu____4355 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4355

and p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4357 =
      let uu____4358 = unparen e  in uu____4358.FStar_Parser_AST.tm  in
    match uu____4357 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4365 =
          let uu____4366 = str "fun"  in
          let uu____4367 =
            let uu____4368 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4368 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4366 uu____4367  in
        let uu____4369 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4365 uu____4369
    | uu____4370 -> p_tmIff e

and p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document
  =
  fun uu____4373  ->
    match uu____4373 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4392 =
            let uu____4393 = unparen e  in uu____4393.FStar_Parser_AST.tm  in
          match uu____4392 with
          | FStar_Parser_AST.Match uu____4396 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4411 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4427);
                 FStar_Parser_AST.prange = uu____4428;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4430);
                                                               FStar_Parser_AST.range
                                                                 = uu____4431;
                                                               FStar_Parser_AST.level
                                                                 = uu____4432;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4459 -> (fun x  -> x)  in
        let uu____4461 =
          let uu____4462 =
            let uu____4463 =
              let uu____4464 =
                let uu____4465 =
                  let uu____4466 = p_disjunctivePattern pat  in
                  let uu____4467 =
                    let uu____4468 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____4468 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____4466 uu____4467  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4465  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4464  in
            FStar_Pprint.group uu____4463  in
          let uu____4469 =
            let uu____4470 = p_term e  in maybe_paren uu____4470  in
          op_Hat_Slash_Plus_Hat uu____4462 uu____4469  in
        FStar_Pprint.group uu____4461

and p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document
  =
  fun uu___103_4471  ->
    match uu___103_4471 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4475 = str "when"  in
        let uu____4476 =
          let uu____4477 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____4477 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____4475 uu____4476

and p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4479 =
      let uu____4480 = unparen e  in uu____4480.FStar_Parser_AST.tm  in
    match uu____4479 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4481;_},e1::e2::[])
        ->
        let uu____4486 = str "<==>"  in
        let uu____4487 = p_tmImplies e1  in
        let uu____4488 = p_tmIff e2  in
        infix0 uu____4486 uu____4487 uu____4488
    | uu____4489 -> p_tmImplies e

and p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4491 =
      let uu____4492 = unparen e  in uu____4492.FStar_Parser_AST.tm  in
    match uu____4491 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4493;_},e1::e2::[])
        ->
        let uu____4498 = str "==>"  in
        let uu____4499 = p_tmArrow p_tmFormula e1  in
        let uu____4500 = p_tmImplies e2  in
        infix0 uu____4498 uu____4499 uu____4500
    | uu____4501 -> p_tmArrow p_tmFormula e

and p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4506 =
        let uu____4507 = unparen e  in uu____4507.FStar_Parser_AST.tm  in
      match uu____4506 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4514 =
            let uu____4515 =
              FStar_Pprint.concat_map
                (fun b  ->
                   let uu____4520 = p_binder false b  in
                   let uu____4521 =
                     let uu____4522 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4522
                      in
                   FStar_Pprint.op_Hat_Hat uu____4520 uu____4521) bs
               in
            let uu____4523 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____4515 uu____4523  in
          FStar_Pprint.group uu____4514
      | uu____4524 -> p_Tm e

and p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4526 =
      let uu____4527 = unparen e  in uu____4527.FStar_Parser_AST.tm  in
    match uu____4526 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4528;_},e1::e2::[])
        ->
        let uu____4533 = str "\\/"  in
        let uu____4534 = p_tmFormula e1  in
        let uu____4535 = p_tmConjunction e2  in
        infix0 uu____4533 uu____4534 uu____4535
    | uu____4536 -> p_tmConjunction e

and p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4538 =
      let uu____4539 = unparen e  in uu____4539.FStar_Parser_AST.tm  in
    match uu____4538 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4540;_},e1::e2::[])
        ->
        let uu____4545 = str "/\\"  in
        let uu____4546 = p_tmConjunction e1  in
        let uu____4547 = p_tmTuple e2  in
        infix0 uu____4545 uu____4546 uu____4547
    | uu____4548 -> p_tmTuple e

and p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4551 =
      let uu____4552 = unparen e  in uu____4552.FStar_Parser_AST.tm  in
    match uu____4551 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____4567 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____4567
          (fun uu____4575  ->
             match uu____4575 with | (e1,uu____4581) -> p_tmEq e1) args
    | uu____4582 -> p_tmEq e

and paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____4587 =
             let uu____4588 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4588  in
           FStar_Pprint.group uu____4587)

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
      let uu____4633 =
        let uu____4634 = unparen e  in uu____4634.FStar_Parser_AST.tm  in
      match uu____4633 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____4641 = levels op1  in
          (match uu____4641 with
           | (left1,mine,right1) ->
               let uu____4651 =
                 let uu____4652 = FStar_All.pipe_left str op1  in
                 let uu____4653 = p_tmEq' left1 e1  in
                 let uu____4654 = p_tmEq' right1 e2  in
                 infix0 uu____4652 uu____4653 uu____4654  in
               paren_if curr mine uu____4651)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____4655;_},e1::e2::[])
          ->
          let uu____4660 =
            let uu____4661 = p_tmEq e1  in
            let uu____4662 =
              let uu____4663 =
                let uu____4664 =
                  let uu____4665 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____4665  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4664  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4663  in
            FStar_Pprint.op_Hat_Hat uu____4661 uu____4662  in
          FStar_Pprint.group uu____4660
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____4666;_},e1::[])
          ->
          let uu____4670 = levels "-"  in
          (match uu____4670 with
           | (left1,mine,right1) ->
               let uu____4680 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____4680)
      | uu____4681 -> p_tmNoEq e

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
      let uu____4736 =
        let uu____4737 = unparen e  in uu____4737.FStar_Parser_AST.tm  in
      match uu____4736 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____4740)::(e2,uu____4742)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____4762 = is_list e  in Prims.op_Negation uu____4762)
          ->
          let op = "::"  in
          let uu____4764 = levels op  in
          (match uu____4764 with
           | (left1,mine,right1) ->
               let uu____4774 =
                 let uu____4775 = str op  in
                 let uu____4776 = p_tmNoEq' left1 e1  in
                 let uu____4777 = p_tmNoEq' right1 e2  in
                 infix0 uu____4775 uu____4776 uu____4777  in
               paren_if curr mine uu____4774)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____4785 = levels op  in
          (match uu____4785 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____4799 = p_binder false b  in
                 let uu____4800 =
                   let uu____4801 =
                     let uu____4802 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____4802 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4801  in
                 FStar_Pprint.op_Hat_Hat uu____4799 uu____4800  in
               let uu____4803 =
                 let uu____4804 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____4805 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____4804 uu____4805  in
               paren_if curr mine uu____4803)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____4812 = levels op1  in
          (match uu____4812 with
           | (left1,mine,right1) ->
               let uu____4822 =
                 let uu____4823 = str op1  in
                 let uu____4824 = p_tmNoEq' left1 e1  in
                 let uu____4825 = p_tmNoEq' right1 e2  in
                 infix0 uu____4823 uu____4824 uu____4825  in
               paren_if curr mine uu____4822)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____4828 =
            let uu____4829 = p_lidentOrUnderscore lid  in
            let uu____4830 =
              let uu____4831 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4831  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4829 uu____4830  in
          FStar_Pprint.group uu____4828
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____4852 =
            let uu____4853 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____4854 =
              let uu____4855 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____4855 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____4853 uu____4854  in
          braces_with_nesting uu____4852
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____4860;_},e1::[])
          ->
          let uu____4864 =
            let uu____4865 = str "~"  in
            let uu____4866 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4865 uu____4866  in
          FStar_Pprint.group uu____4864
      | uu____4867 -> p_appTerm e

and p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4869 = p_appTerm e  in
    let uu____4870 =
      let uu____4871 =
        let uu____4872 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____4872 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4871  in
    FStar_Pprint.op_Hat_Hat uu____4869 uu____4870

and p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____4877 =
            let uu____4878 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____4878 t phi  in
          soft_parens_with_nesting uu____4877
      | FStar_Parser_AST.TAnnotated uu____4879 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____4884 ->
          let uu____4885 =
            let uu____4886 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4886
             in
          failwith uu____4885
      | FStar_Parser_AST.TVariable uu____4887 ->
          let uu____4888 =
            let uu____4889 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4889
             in
          failwith uu____4888
      | FStar_Parser_AST.NoName uu____4890 ->
          let uu____4891 =
            let uu____4892 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____4892
             in
          failwith uu____4891

and p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document
  =
  fun uu____4893  ->
    match uu____4893 with
    | (lid,e) ->
        let uu____4900 =
          let uu____4901 = p_qlident lid  in
          let uu____4902 =
            let uu____4903 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____4903  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4901 uu____4902  in
        FStar_Pprint.group uu____4900

and p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____4905 =
      let uu____4906 = unparen e  in uu____4906.FStar_Parser_AST.tm  in
    match uu____4905 with
    | FStar_Parser_AST.App uu____4907 when is_general_application e ->
        let uu____4914 = head_and_args e  in
        (match uu____4914 with
         | (head1,args) ->
             let uu____4939 =
               let uu____4950 = FStar_ST.read should_print_fs_typ_app  in
               if uu____4950
               then
                 let uu____4961 =
                   FStar_Util.take
                     (fun uu____4985  ->
                        match uu____4985 with
                        | (uu____4990,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____4961 with
                 | (fs_typ_args,args1) ->
                     let uu____5028 =
                       let uu____5029 = p_indexingTerm head1  in
                       let uu____5030 =
                         let uu____5031 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_separate_map (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5031 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5029 uu____5030  in
                     (uu____5028, args1)
               else
                 (let uu____5043 = p_indexingTerm head1  in
                  (uu____5043, args))
                in
             (match uu____4939 with
              | (head_doc,args1) ->
                  let uu____5064 =
                    let uu____5065 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_separate_map (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5065 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5064))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5085 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5085)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5103 =
               let uu____5104 = p_quident lid  in
               let uu____5105 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5104 uu____5105  in
             FStar_Pprint.group uu____5103
         | hd1::tl1 ->
             let uu____5122 =
               let uu____5123 =
                 let uu____5124 =
                   let uu____5125 = p_quident lid  in
                   let uu____5126 = p_argTerm hd1  in
                   prefix2 uu____5125 uu____5126  in
                 FStar_Pprint.group uu____5124  in
               let uu____5127 =
                 let uu____5128 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5128  in
               FStar_Pprint.op_Hat_Hat uu____5123 uu____5127  in
             FStar_Pprint.group uu____5122)
    | uu____5133 -> p_indexingTerm e

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
         (let uu____5142 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5142 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5144 = str "#"  in
        let uu____5145 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5144 uu____5145
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document
  =
  fun uu____5147  ->
    match uu____5147 with | (e,uu____5153) -> p_indexingTerm e

and p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document
  =
  fun exit1  ->
    fun e  ->
      let uu____5158 =
        let uu____5159 = unparen e  in uu____5159.FStar_Parser_AST.tm  in
      match uu____5158 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5160;_},e1::e2::[])
          ->
          let uu____5165 =
            let uu____5166 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5167 =
              let uu____5168 =
                let uu____5169 = p_term e2  in
                soft_parens_with_nesting uu____5169  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5168  in
            FStar_Pprint.op_Hat_Hat uu____5166 uu____5167  in
          FStar_Pprint.group uu____5165
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5170;_},e1::e2::[])
          ->
          let uu____5175 =
            let uu____5176 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5177 =
              let uu____5178 =
                let uu____5179 = p_term e2  in
                soft_brackets_with_nesting uu____5179  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5178  in
            FStar_Pprint.op_Hat_Hat uu____5176 uu____5177  in
          FStar_Pprint.group uu____5175
      | uu____5180 -> exit1 e

and p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5183 =
      let uu____5184 = unparen e  in uu____5184.FStar_Parser_AST.tm  in
    match uu____5183 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5187 = p_quident lid  in
        let uu____5188 =
          let uu____5189 =
            let uu____5190 = p_term e1  in
            soft_parens_with_nesting uu____5190  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5189  in
        FStar_Pprint.op_Hat_Hat uu____5187 uu____5188
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5196 = str (FStar_Ident.text_of_id op)  in
        let uu____5197 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5196 uu____5197
    | uu____5198 -> p_atomicTermNotQUident e

and p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5200 =
      let uu____5201 = unparen e  in uu____5201.FStar_Parser_AST.tm  in
    match uu____5200 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = '\n' -> str "0x0Az"
         | uu____5206 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5213 = str (FStar_Ident.text_of_id op)  in
        let uu____5214 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5213 uu____5214
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5218 =
          let uu____5219 =
            let uu____5220 = str (FStar_Ident.text_of_id op)  in
            let uu____5221 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5220 uu____5221  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5219  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5218
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5236 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5237 =
          let uu____5238 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5239 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5238 p_tmEq uu____5239  in
        let uu____5246 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5236 uu____5237 uu____5246
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5249 =
          let uu____5250 = p_atomicTermNotQUident e1  in
          let uu____5251 =
            let uu____5252 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5252  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5250 uu____5251
           in
        FStar_Pprint.group uu____5249
    | uu____5253 -> p_projectionLHS e

and p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun e  ->
    let uu____5255 =
      let uu____5256 = unparen e  in uu____5256.FStar_Parser_AST.tm  in
    match uu____5255 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5260 = p_quident constr_lid  in
        let uu____5261 =
          let uu____5262 =
            let uu____5263 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5263  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5262  in
        FStar_Pprint.op_Hat_Hat uu____5260 uu____5261
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5265 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5265 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5267 = p_term e1  in soft_parens_with_nesting uu____5267
    | uu____5268 when is_array e ->
        let es = extract_from_list e  in
        let uu____5272 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5273 =
          let uu____5274 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5274 p_noSeqTerm es  in
        let uu____5275 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5272 uu____5273 uu____5275
    | uu____5276 when is_list e ->
        let uu____5277 =
          let uu____5278 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5279 = extract_from_list e  in
          separate_map_or_flow uu____5278 p_noSeqTerm uu____5279  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5277 FStar_Pprint.rbracket
    | uu____5282 when is_lex_list e ->
        let uu____5283 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5284 =
          let uu____5285 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5286 = extract_from_list e  in
          separate_map_or_flow uu____5285 p_noSeqTerm uu____5286  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5283 uu____5284 FStar_Pprint.rbracket
    | uu____5289 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5293 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5294 =
          let uu____5295 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5295 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5293 uu____5294 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5299 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5300 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5299 uu____5300
    | FStar_Parser_AST.Op (op,args) when
        let uu____5307 = handleable_op op args  in
        Prims.op_Negation uu____5307 ->
        let uu____5308 =
          let uu____5309 =
            let uu____5310 =
              let uu____5311 =
                let uu____5312 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5312
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5311  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5310  in
          Prims.strcat "Operation " uu____5309  in
        failwith uu____5308
    | FStar_Parser_AST.Uvar uu____5313 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5314 = p_term e  in soft_parens_with_nesting uu____5314
    | FStar_Parser_AST.Const uu____5315 ->
        let uu____5316 = p_term e  in soft_parens_with_nesting uu____5316
    | FStar_Parser_AST.Op uu____5317 ->
        let uu____5324 = p_term e  in soft_parens_with_nesting uu____5324
    | FStar_Parser_AST.Tvar uu____5325 ->
        let uu____5326 = p_term e  in soft_parens_with_nesting uu____5326
    | FStar_Parser_AST.Var uu____5327 ->
        let uu____5328 = p_term e  in soft_parens_with_nesting uu____5328
    | FStar_Parser_AST.Name uu____5329 ->
        let uu____5330 = p_term e  in soft_parens_with_nesting uu____5330
    | FStar_Parser_AST.Construct uu____5331 ->
        let uu____5342 = p_term e  in soft_parens_with_nesting uu____5342
    | FStar_Parser_AST.Abs uu____5343 ->
        let uu____5350 = p_term e  in soft_parens_with_nesting uu____5350
    | FStar_Parser_AST.App uu____5351 ->
        let uu____5358 = p_term e  in soft_parens_with_nesting uu____5358
    | FStar_Parser_AST.Let uu____5359 ->
        let uu____5372 = p_term e  in soft_parens_with_nesting uu____5372
    | FStar_Parser_AST.LetOpen uu____5373 ->
        let uu____5378 = p_term e  in soft_parens_with_nesting uu____5378
    | FStar_Parser_AST.Seq uu____5379 ->
        let uu____5384 = p_term e  in soft_parens_with_nesting uu____5384
    | FStar_Parser_AST.Bind uu____5385 ->
        let uu____5392 = p_term e  in soft_parens_with_nesting uu____5392
    | FStar_Parser_AST.If uu____5393 ->
        let uu____5400 = p_term e  in soft_parens_with_nesting uu____5400
    | FStar_Parser_AST.Match uu____5401 ->
        let uu____5416 = p_term e  in soft_parens_with_nesting uu____5416
    | FStar_Parser_AST.TryWith uu____5417 ->
        let uu____5432 = p_term e  in soft_parens_with_nesting uu____5432
    | FStar_Parser_AST.Ascribed uu____5433 ->
        let uu____5442 = p_term e  in soft_parens_with_nesting uu____5442
    | FStar_Parser_AST.Record uu____5443 ->
        let uu____5456 = p_term e  in soft_parens_with_nesting uu____5456
    | FStar_Parser_AST.Project uu____5457 ->
        let uu____5462 = p_term e  in soft_parens_with_nesting uu____5462
    | FStar_Parser_AST.Product uu____5463 ->
        let uu____5470 = p_term e  in soft_parens_with_nesting uu____5470
    | FStar_Parser_AST.Sum uu____5471 ->
        let uu____5478 = p_term e  in soft_parens_with_nesting uu____5478
    | FStar_Parser_AST.QForall uu____5479 ->
        let uu____5492 = p_term e  in soft_parens_with_nesting uu____5492
    | FStar_Parser_AST.QExists uu____5493 ->
        let uu____5506 = p_term e  in soft_parens_with_nesting uu____5506
    | FStar_Parser_AST.Refine uu____5507 ->
        let uu____5512 = p_term e  in soft_parens_with_nesting uu____5512
    | FStar_Parser_AST.NamedTyp uu____5513 ->
        let uu____5518 = p_term e  in soft_parens_with_nesting uu____5518
    | FStar_Parser_AST.Requires uu____5519 ->
        let uu____5526 = p_term e  in soft_parens_with_nesting uu____5526
    | FStar_Parser_AST.Ensures uu____5527 ->
        let uu____5534 = p_term e  in soft_parens_with_nesting uu____5534
    | FStar_Parser_AST.Assign uu____5535 ->
        let uu____5540 = p_term e  in soft_parens_with_nesting uu____5540
    | FStar_Parser_AST.Attributes uu____5541 ->
        let uu____5544 = p_term e  in soft_parens_with_nesting uu____5544

and p_constant : FStar_Const.sconst -> FStar_Pprint.document =
  fun uu___106_5545  ->
    match uu___106_5545 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____5549 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____5549
    | FStar_Const.Const_string (bytes,uu____5551) ->
        let uu____5556 = str (FStar_Util.string_of_bytes bytes)  in
        FStar_Pprint.dquotes uu____5556
    | FStar_Const.Const_bytearray (bytes,uu____5558) ->
        let uu____5563 =
          let uu____5564 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____5564  in
        let uu____5565 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____5563 uu____5565
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___104_5583 =
          match uu___104_5583 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___105_5587 =
          match uu___105_5587 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____5598  ->
               match uu____5598 with
               | (s,w) ->
                   let uu____5605 = signedness s  in
                   let uu____5606 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____5605 uu____5606)
            sign_width_opt
           in
        let uu____5607 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____5607 ending
    | FStar_Const.Const_range r ->
        let uu____5609 = FStar_Range.string_of_range r  in str uu____5609
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____5611 = p_quident lid  in
        let uu____5612 =
          let uu____5613 =
            let uu____5614 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5614  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5613  in
        FStar_Pprint.op_Hat_Hat uu____5611 uu____5612

and p_universe : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5616 = str "u#"  in
    let uu____5617 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____5616 uu____5617

and p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5619 =
      let uu____5620 = unparen u  in uu____5620.FStar_Parser_AST.tm  in
    match uu____5619 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5621;_},u1::u2::[])
        ->
        let uu____5626 =
          let uu____5627 = p_universeFrom u1  in
          let uu____5628 =
            let uu____5629 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____5629  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5627 uu____5628  in
        FStar_Pprint.group uu____5626
    | FStar_Parser_AST.App uu____5630 ->
        let uu____5637 = head_and_args u  in
        (match uu____5637 with
         | (head1,args) ->
             let uu____5662 =
               let uu____5663 = unparen head1  in
               uu____5663.FStar_Parser_AST.tm  in
             (match uu____5662 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____5665 =
                    let uu____5666 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____5667 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____5675  ->
                           match uu____5675 with
                           | (u1,uu____5681) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____5666 uu____5667  in
                  FStar_Pprint.group uu____5665
              | uu____5682 ->
                  let uu____5683 =
                    let uu____5684 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____5684
                     in
                  failwith uu____5683))
    | uu____5685 -> p_atomicUniverse u

and p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document =
  fun u  ->
    let uu____5687 =
      let uu____5688 = unparen u  in uu____5688.FStar_Parser_AST.tm  in
    match uu____5687 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id -> str (FStar_Ident.text_of_id id)
    | FStar_Parser_AST.Paren u1 ->
        let uu____5711 = p_universeFrom u1  in
        soft_parens_with_nesting uu____5711
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____5712;_},uu____5713::uu____5714::[])
        ->
        let uu____5717 = p_universeFrom u  in
        soft_parens_with_nesting uu____5717
    | FStar_Parser_AST.App uu____5718 ->
        let uu____5725 = p_universeFrom u  in
        soft_parens_with_nesting uu____5725
    | uu____5726 ->
        let uu____5727 =
          let uu____5728 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____5728
           in
        failwith uu____5727

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
    FStar_ST.write should_print_fs_typ_app false;
    (let res =
       match m with
       | FStar_Parser_AST.Module (uu____5751,decls) ->
           let uu____5757 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____5757
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____5766,decls,uu____5768) ->
           let uu____5773 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____5773
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.write should_print_fs_typ_app false; res)
  
let comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____5806  ->
         match uu____5806 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____5848,decls) -> decls
        | FStar_Parser_AST.Interface (uu____5854,decls,uu____5856) -> decls
         in
      FStar_ST.write should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____5882 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____5895;
                 FStar_Parser_AST.doc = uu____5896;
                 FStar_Parser_AST.quals = uu____5897;
                 FStar_Parser_AST.attrs = uu____5898;_}::uu____5899 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____5905 =
                   let uu____5908 =
                     let uu____5911 = FStar_List.tl ds  in d :: uu____5911
                      in
                   d0 :: uu____5908  in
                 (uu____5905, (d0.FStar_Parser_AST.drange))
             | uu____5916 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____5882 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.write comment_stack comments;
                 (let initial_comment =
                    let uu____5949 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____5949 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.read comment_stack  in
                  FStar_ST.write comment_stack [];
                  FStar_ST.write should_print_fs_typ_app false;
                  (let uu____5976 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____5976, comments1))))))
  