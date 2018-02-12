open Prims
let (should_print_fs_typ_app : Prims.bool FStar_ST.ref) =
  FStar_Util.mk_ref false 
let with_fs_typ_app :
  'Auu____45 'Auu____46 .
    Prims.bool -> ('Auu____46 -> 'Auu____45) -> 'Auu____46 -> 'Auu____45
  =
  fun b  ->
    fun printer  ->
      fun t  ->
        let b0 = FStar_ST.op_Bang should_print_fs_typ_app  in
        FStar_ST.op_Colon_Equals should_print_fs_typ_app b;
        (let res = printer t  in
         FStar_ST.op_Colon_Equals should_print_fs_typ_app b0; res)
  
let (should_unparen : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref true 
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    let uu____167 =
      let uu____168 = FStar_ST.op_Bang should_unparen  in
      Prims.op_Negation uu____168  in
    if uu____167
    then t
    else
      (match t.FStar_Parser_AST.tm with
       | FStar_Parser_AST.Paren t1 -> unparen t1
       | uu____190 -> t)
  
let (str : Prims.string -> FStar_Pprint.document) =
  fun s  -> FStar_Pprint.doc_of_string s 
let default_or_map :
  'Auu____199 'Auu____200 .
    'Auu____200 ->
      ('Auu____199 -> 'Auu____200) ->
        'Auu____199 FStar_Pervasives_Native.option -> 'Auu____200
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
  'Auu____254 .
    FStar_Pprint.document ->
      ('Auu____254 -> FStar_Pprint.document) ->
        'Auu____254 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____276 =
          let uu____277 =
            let uu____278 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____278  in
          FStar_Pprint.separate_map uu____277 f l  in
        FStar_Pprint.group uu____276
  
let precede_break_separate_map :
  'Auu____284 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____284 -> FStar_Pprint.document) ->
          'Auu____284 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____310 =
            let uu____311 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____312 =
              let uu____313 = FStar_List.hd l  in
              FStar_All.pipe_right uu____313 f  in
            FStar_Pprint.precede uu____311 uu____312  in
          let uu____314 =
            let uu____315 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____321 =
                   let uu____322 =
                     let uu____323 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____323  in
                   FStar_Pprint.op_Hat_Hat sep uu____322  in
                 FStar_Pprint.op_Hat_Hat break1 uu____321) uu____315
             in
          FStar_Pprint.op_Hat_Hat uu____310 uu____314
  
let concat_break_map :
  'Auu____327 .
    ('Auu____327 -> FStar_Pprint.document) ->
      'Auu____327 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____345 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____349 = f x  in FStar_Pprint.op_Hat_Hat uu____349 break1)
          l
         in
      FStar_Pprint.group uu____345
  
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
    let uu____371 = str "begin"  in
    let uu____372 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____371 contents uu____372
  
let separate_map_or_flow :
  'Auu____377 .
    FStar_Pprint.document ->
      ('Auu____377 -> FStar_Pprint.document) ->
        'Auu____377 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let soft_surround_separate_map :
  'Auu____409 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____409 -> FStar_Pprint.document) ->
                  'Auu____409 Prims.list -> FStar_Pprint.document
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
                    (let uu____454 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____454
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____464 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____464 -> FStar_Pprint.document) ->
                  'Auu____464 Prims.list -> FStar_Pprint.document
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
                    (let uu____509 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____509
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____522  ->
    match uu____522 with
    | (comment,keywords) ->
        let uu____547 =
          let uu____548 =
            let uu____551 = str comment  in
            let uu____552 =
              let uu____555 =
                let uu____558 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____567  ->
                       match uu____567 with
                       | (k,v1) ->
                           let uu____574 =
                             let uu____577 = str k  in
                             let uu____578 =
                               let uu____581 =
                                 let uu____584 = str v1  in [uu____584]  in
                               FStar_Pprint.rarrow :: uu____581  in
                             uu____577 :: uu____578  in
                           FStar_Pprint.concat uu____574) keywords
                   in
                [uu____558]  in
              FStar_Pprint.space :: uu____555  in
            uu____551 :: uu____552  in
          FStar_Pprint.concat uu____548  in
        FStar_Pprint.group uu____547
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____588 =
      let uu____589 = unparen e  in uu____589.FStar_Parser_AST.tm  in
    match uu____588 with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____590 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      let uu____597 =
        let uu____598 = unparen t  in uu____598.FStar_Parser_AST.tm  in
      match uu____597 with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____600 -> false
  
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
        let uu____617 =
          let uu____618 = unparen e  in uu____618.FStar_Parser_AST.tm  in
        match uu____617 with
        | FStar_Parser_AST.Construct (lid,[]) ->
            FStar_Ident.lid_equals lid nil_lid1
        | FStar_Parser_AST.Construct (lid,uu____631::(e2,uu____633)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____656 -> false  in
      aux
  
let (is_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.cons_lid FStar_Parser_Const.nil_lid 
let (is_lex_list : FStar_Parser_AST.term -> Prims.bool) =
  is_list_structure FStar_Parser_Const.lexcons_lid
    FStar_Parser_Const.lextop_lid
  
let rec (extract_from_list :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    let uu____666 =
      let uu____667 = unparen e  in uu____667.FStar_Parser_AST.tm  in
    match uu____666 with
    | FStar_Parser_AST.Construct (uu____670,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____681,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____702 = extract_from_list e2  in e1 :: uu____702
    | uu____705 ->
        let uu____706 =
          let uu____707 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____707  in
        failwith uu____706
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____713 =
      let uu____714 = unparen e  in uu____714.FStar_Parser_AST.tm  in
    match uu____713 with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____716;
           FStar_Parser_AST.level = uu____717;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____719 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____723 =
      let uu____724 = unparen e  in uu____724.FStar_Parser_AST.tm  in
    match uu____723 with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____727;
           FStar_Parser_AST.level = uu____728;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____730;
                                                        FStar_Parser_AST.level
                                                          = uu____731;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____733;
                                                   FStar_Parser_AST.level =
                                                     uu____734;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____736;
                FStar_Parser_AST.level = uu____737;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____739;
           FStar_Parser_AST.level = uu____740;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____742 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    let uu____748 =
      let uu____749 = unparen e  in uu____749.FStar_Parser_AST.tm  in
    match uu____748 with
    | FStar_Parser_AST.Var uu____752 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____753;
           FStar_Parser_AST.range = uu____754;
           FStar_Parser_AST.level = uu____755;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____756;
                                                        FStar_Parser_AST.range
                                                          = uu____757;
                                                        FStar_Parser_AST.level
                                                          = uu____758;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____760;
                                                   FStar_Parser_AST.level =
                                                     uu____761;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____762;
                FStar_Parser_AST.range = uu____763;
                FStar_Parser_AST.level = uu____764;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____766;
           FStar_Parser_AST.level = uu____767;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____769 = extract_from_ref_set e1  in
        let uu____772 = extract_from_ref_set e2  in
        FStar_List.append uu____769 uu____772
    | uu____775 ->
        let uu____776 =
          let uu____777 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____777  in
        failwith uu____776
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____783 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____783
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____787 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____787
  
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
      let uu____837 =
        let uu____838 = unparen e1  in uu____838.FStar_Parser_AST.tm  in
      match uu____837 with
      | FStar_Parser_AST.App (head1,arg,imp) -> aux head1 ((arg, imp) :: acc)
      | uu____856 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____870 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____874 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____878 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___49_896  ->
    match uu___49_896 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___50_913  ->
      match uu___50_913 with
      | FStar_Util.Inl c ->
          let uu____922 = FStar_String.get s (Prims.parse_int "0")  in
          uu____922 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____930 .
    Prims.string ->
      ('Auu____930,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____949  ->
      match uu____949 with
      | (assoc_levels,tokens) ->
          let uu____977 = FStar_List.tryFind (matches_token s) tokens  in
          uu____977 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1003 .
    Prims.unit ->
      (associativity,('Auu____1003,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1014  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1030 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1030) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1042  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1077 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1077) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1089  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1117 .
    Prims.unit ->
      (associativity,('Auu____1117,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1128  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1144 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1144) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1156  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1184 .
    Prims.unit ->
      (associativity,('Auu____1184,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1195  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1211 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1211) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1223  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1244 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1244) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1256  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1291 .
    Prims.unit ->
      (associativity,('Auu____1291,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1302  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1318 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1318) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1330  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1351 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1351) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1363  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1384 .
    Prims.unit ->
      (associativity,('Auu____1384,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1395  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1411 .
    Prims.unit ->
      (associativity,('Auu____1411,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1422  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1438 .
    Prims.unit ->
      (associativity,('Auu____1438,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1449  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___51_1656 =
    match uu___51_1656 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  -> (l, l, l)  in
  FStar_List.mapi
    (fun i  ->
       fun uu____1696  ->
         match uu____1696 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1776 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1776 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1826) ->
          assoc_levels
      | uu____1870 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1905 .
    ('Auu____1905,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____1965 =
        FStar_List.tryFind
          (fun uu____2005  ->
             match uu____2005 with
             | (uu____2023,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____1965 with
      | FStar_Pervasives_Native.Some ((uu____2065,l1,uu____2067),uu____2068)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2123 =
            let uu____2124 =
              let uu____2125 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2125  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2124
             in
          failwith uu____2123
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  = assign_levels level_associativity_spec 
let operatorInfix0ad12 :
  'Auu____2159 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2159) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2173  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2254 =
      let uu____2268 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2268 (operatorInfix0ad12 ())  in
    uu____2254 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2381 =
      let uu____2395 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2395 opinfix34  in
    uu____2381 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2461 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2461
    then (Prims.parse_int "1")
    else
      (let uu____2463 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2463
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2469 . FStar_Ident.ident -> 'Auu____2469 Prims.list -> Prims.bool =
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
      | uu____2482 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2542 .
    ('Auu____2542 -> FStar_Pprint.document) ->
      'Auu____2542 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2574 = FStar_ST.op_Bang comment_stack  in
          match uu____2574 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2633 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2633
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2670 =
                    let uu____2671 =
                      let uu____2672 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2672
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2671  in
                  comments_before_pos uu____2670 print_pos lookahead_pos))
              else
                (let uu____2674 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2674))
           in
        let uu____2675 =
          let uu____2680 =
            let uu____2681 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2681  in
          let uu____2682 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2680 uu____2682  in
        match uu____2675 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2688 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2688
              else comments  in
            let uu____2694 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2694
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2707 = FStar_ST.op_Bang comment_stack  in
          match uu____2707 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2791 =
                    let uu____2792 =
                      let uu____2793 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2793  in
                    uu____2792 - lbegin  in
                  max k uu____2791  in
                let doc2 =
                  let uu____2795 =
                    let uu____2796 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2797 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2796 uu____2797  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2795  in
                let uu____2798 =
                  let uu____2799 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2799  in
                place_comments_until_pos (Prims.parse_int "1") uu____2798
                  pos_end doc2))
          | uu____2800 ->
              let lnum =
                let uu____2808 =
                  let uu____2809 = FStar_Range.line_of_pos pos_end  in
                  uu____2809 - lbegin  in
                max (Prims.parse_int "1") uu____2808  in
              let uu____2810 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2810
  
let separate_map_with_comments :
  'Auu____2817 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2817 -> FStar_Pprint.document) ->
          'Auu____2817 Prims.list ->
            ('Auu____2817 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2865 x =
              match uu____2865 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2879 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2879 doc1
                     in
                  let uu____2880 =
                    let uu____2881 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2881  in
                  let uu____2882 =
                    let uu____2883 =
                      let uu____2884 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2884  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2883  in
                  (uu____2880, uu____2882)
               in
            let uu____2885 =
              let uu____2892 = FStar_List.hd xs  in
              let uu____2893 = FStar_List.tl xs  in (uu____2892, uu____2893)
               in
            match uu____2885 with
            | (x,xs1) ->
                let init1 =
                  let uu____2909 =
                    let uu____2910 =
                      let uu____2911 = extract_range x  in
                      FStar_Range.end_of_range uu____2911  in
                    FStar_Range.line_of_pos uu____2910  in
                  let uu____2912 =
                    let uu____2913 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2913  in
                  (uu____2909, uu____2912)  in
                let uu____2914 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2914
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3209 =
      let uu____3210 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc
         in
      let uu____3211 =
        let uu____3212 = p_attributes d.FStar_Parser_AST.attrs  in
        let uu____3213 =
          let uu____3214 = p_qualifiers d.FStar_Parser_AST.quals  in
          let uu____3215 =
            let uu____3216 = p_rawDecl d  in
            FStar_Pprint.op_Hat_Hat
              (if d.FStar_Parser_AST.quals = []
               then FStar_Pprint.empty
               else break1) uu____3216
             in
          FStar_Pprint.op_Hat_Hat uu____3214 uu____3215  in
        FStar_Pprint.op_Hat_Hat uu____3212 uu____3213  in
      FStar_Pprint.op_Hat_Hat uu____3210 uu____3211  in
    FStar_Pprint.group uu____3209

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    let uu____3219 =
      let uu____3220 = str "@"  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3220  in
    let uu____3221 =
      FStar_Pprint.op_Hat_Hat FStar_Pprint.rbracket FStar_Pprint.hardline  in
    soft_surround_map_or_flow (Prims.parse_int "0") (Prims.parse_int "2")
      FStar_Pprint.empty uu____3219 FStar_Pprint.space uu____3221
      p_atomicTerm attrs

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3222  ->
    match uu____3222 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3256 =
                match uu____3256 with
                | (kwd,arg) ->
                    let uu____3263 = str "@"  in
                    let uu____3264 =
                      let uu____3265 = str kwd  in
                      let uu____3266 =
                        let uu____3267 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3267
                         in
                      FStar_Pprint.op_Hat_Hat uu____3265 uu____3266  in
                    FStar_Pprint.op_Hat_Hat uu____3263 uu____3264
                 in
              let uu____3268 =
                let uu____3269 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3269 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3268
           in
        let uu____3274 =
          let uu____3275 =
            let uu____3276 =
              let uu____3277 =
                let uu____3278 = str doc1  in
                let uu____3279 =
                  let uu____3280 =
                    let uu____3281 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3281  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3280  in
                FStar_Pprint.op_Hat_Hat uu____3278 uu____3279  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3277  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3276  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3275  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3274

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3285 =
          let uu____3286 = str "val"  in
          let uu____3287 =
            let uu____3288 =
              let uu____3289 = p_lident lid  in
              let uu____3290 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3289 uu____3290  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3288  in
          FStar_Pprint.op_Hat_Hat uu____3286 uu____3287  in
        let uu____3291 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3285 uu____3291
    | FStar_Parser_AST.TopLevelLet (uu____3292,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3317 =
               let uu____3318 = str "let"  in
               let uu____3319 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3318 uu____3319  in
             FStar_Pprint.group uu____3317) lbs
    | uu____3320 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3323 =
          let uu____3324 = str "open"  in
          let uu____3325 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3324 uu____3325  in
        FStar_Pprint.group uu____3323
    | FStar_Parser_AST.Include uid ->
        let uu____3327 =
          let uu____3328 = str "include"  in
          let uu____3329 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3328 uu____3329  in
        FStar_Pprint.group uu____3327
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3332 =
          let uu____3333 = str "module"  in
          let uu____3334 =
            let uu____3335 =
              let uu____3336 = p_uident uid1  in
              let uu____3337 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3336 uu____3337  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3335  in
          FStar_Pprint.op_Hat_Hat uu____3333 uu____3334  in
        let uu____3338 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3332 uu____3338
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3340 =
          let uu____3341 = str "module"  in
          let uu____3342 =
            let uu____3343 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3343  in
          FStar_Pprint.op_Hat_Hat uu____3341 uu____3342  in
        FStar_Pprint.group uu____3340
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3376 = str "effect"  in
          let uu____3377 =
            let uu____3378 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3378  in
          FStar_Pprint.op_Hat_Hat uu____3376 uu____3377  in
        let uu____3379 =
          let uu____3380 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3380 FStar_Pprint.equals
           in
        let uu____3381 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3379 uu____3381
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3399 = str "type"  in
        let uu____3400 = str "and"  in
        precede_break_separate_map uu____3399 uu____3400 p_fsdocTypeDeclPairs
          tcdefs
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3422 = str "let"  in
          let uu____3423 =
            let uu____3424 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3424 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3422 uu____3423  in
        let uu____3425 =
          let uu____3426 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3426 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3425 p_letbinding lbs
          (fun uu____3434  ->
             match uu____3434 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3443 =
          let uu____3444 = str "val"  in
          let uu____3445 =
            let uu____3446 =
              let uu____3447 = p_lident lid  in
              let uu____3448 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3447 uu____3448  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3446  in
          FStar_Pprint.op_Hat_Hat uu____3444 uu____3445  in
        let uu____3449 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3443 uu____3449
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3453 =
            let uu____3454 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3454 FStar_Util.is_upper  in
          if uu____3453
          then FStar_Pprint.empty
          else
            (let uu____3456 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3456 FStar_Pprint.space)
           in
        let uu____3457 =
          let uu____3458 =
            let uu____3459 = p_ident id1  in
            let uu____3460 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3459 uu____3460  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3458  in
        let uu____3461 = p_typ t  in
        op_Hat_Slash_Plus_Hat uu____3457 uu____3461
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3468 = str "exception"  in
        let uu____3469 =
          let uu____3470 =
            let uu____3471 = p_uident uid  in
            let uu____3472 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3477 = str "of"  in
                   let uu____3478 = p_typ t  in
                   op_Hat_Slash_Plus_Hat uu____3477 uu____3478) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3471 uu____3472  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3470  in
        FStar_Pprint.op_Hat_Hat uu____3468 uu____3469
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3480 = str "new_effect"  in
        let uu____3481 =
          let uu____3482 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3482  in
        FStar_Pprint.op_Hat_Hat uu____3480 uu____3481
    | FStar_Parser_AST.SubEffect se ->
        let uu____3484 = str "sub_effect"  in
        let uu____3485 =
          let uu____3486 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3486  in
        FStar_Pprint.op_Hat_Hat uu____3484 uu____3485
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3489 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3489 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3490 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3491) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___52_3508  ->
    match uu___52_3508 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3510 = str "#set-options"  in
        let uu____3511 =
          let uu____3512 =
            let uu____3513 = str s  in FStar_Pprint.dquotes uu____3513  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3512  in
        FStar_Pprint.op_Hat_Hat uu____3510 uu____3511
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3517 = str "#reset-options"  in
        let uu____3518 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3522 =
                 let uu____3523 = str s  in FStar_Pprint.dquotes uu____3523
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3522) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3517 uu____3518
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
  fun uu____3547  ->
    match uu____3547 with
    | (typedecl,fsdoc_opt) ->
        let uu____3560 = FStar_Pprint.optional p_fsdoc fsdoc_opt  in
        let uu____3561 = p_typeDecl typedecl  in
        FStar_Pprint.op_Hat_Hat uu____3560 uu____3561

and (p_typeDecl : FStar_Parser_AST.tycon -> FStar_Pprint.document) =
  fun uu___53_3562  ->
    match uu___53_3562 with
    | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
        let empty' uu____3577 = FStar_Pprint.empty  in
        p_typeDeclPrefix lid bs typ_opt empty'
    | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
        let f uu____3593 =
          let uu____3594 = p_typ t  in prefix2 FStar_Pprint.equals uu____3594
           in
        p_typeDeclPrefix lid bs typ_opt f
    | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
        let p_recordFieldAndComments uu____3638 =
          match uu____3638 with
          | (lid1,t,doc_opt) ->
              let uu____3654 =
                FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                 in
              with_comment p_recordFieldDecl (lid1, t, doc_opt) uu____3654
           in
        let p_fields uu____3668 =
          let uu____3669 =
            let uu____3670 =
              let uu____3671 =
                let uu____3672 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                FStar_Pprint.separate_map uu____3672 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3671  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3670  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____3669  in
        p_typeDeclPrefix lid bs typ_opt p_fields
    | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
        let p_constructorBranchAndComments uu____3736 =
          match uu____3736 with
          | (uid,t_opt,doc_opt,use_of) ->
              let range =
                let uu____3762 =
                  let uu____3763 =
                    FStar_Util.map_opt t_opt
                      (fun t  -> t.FStar_Parser_AST.range)
                     in
                  FStar_Util.dflt uid.FStar_Ident.idRange uu____3763  in
                FStar_Range.extend_to_end_of_line uu____3762  in
              let p_constructorBranch decl =
                let uu____3796 =
                  let uu____3797 =
                    let uu____3798 = p_constructorDecl decl  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3798  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____3797  in
                FStar_Pprint.group uu____3796  in
              with_comment p_constructorBranch (uid, t_opt, doc_opt, use_of)
                range
           in
        let datacon_doc uu____3818 =
          let uu____3819 =
            FStar_Pprint.separate_map break1 p_constructorBranchAndComments
              ct_decls
             in
          FStar_Pprint.group uu____3819  in
        p_typeDeclPrefix lid bs typ_opt
          (fun uu____3834  ->
             let uu____3835 = datacon_doc ()  in
             prefix2 FStar_Pprint.equals uu____3835)

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
            let uu____3850 = p_ident lid  in
            let uu____3851 =
              let uu____3852 = cont ()  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3852  in
            FStar_Pprint.op_Hat_Hat uu____3850 uu____3851
          else
            (let binders_doc =
               let uu____3855 = p_typars bs  in
               let uu____3856 =
                 FStar_Pprint.optional
                   (fun t  ->
                      let uu____3860 =
                        let uu____3861 =
                          let uu____3862 = p_typ t  in
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            uu____3862
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3861
                         in
                      FStar_Pprint.op_Hat_Hat break1 uu____3860) typ_opt
                  in
               FStar_Pprint.op_Hat_Hat uu____3855 uu____3856  in
             let uu____3863 = p_ident lid  in
             let uu____3864 = cont ()  in
             FStar_Pprint.surround (Prims.parse_int "2")
               (Prims.parse_int "1") uu____3863 binders_doc uu____3864)

and (p_recordFieldDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                             FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun uu____3865  ->
    match uu____3865 with
    | (lid,t,doc_opt) ->
        let uu____3881 =
          let uu____3882 = FStar_Pprint.optional p_fsdoc doc_opt  in
          let uu____3883 =
            let uu____3884 = p_lident lid  in
            let uu____3885 =
              let uu____3886 = p_typ t  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3886  in
            FStar_Pprint.op_Hat_Hat uu____3884 uu____3885  in
          FStar_Pprint.op_Hat_Hat uu____3882 uu____3883  in
        FStar_Pprint.group uu____3881

and (p_constructorDecl :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____3887  ->
    match uu____3887 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc = p_uident uid  in
        let uu____3915 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____3916 =
          let uu____3917 = FStar_Pprint.break_ (Prims.parse_int "0")  in
          let uu____3918 =
            default_or_map uid_doc
              (fun t  ->
                 let uu____3923 =
                   let uu____3924 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____3924  in
                 let uu____3925 = p_typ t  in
                 op_Hat_Slash_Plus_Hat uu____3923 uu____3925) t_opt
             in
          FStar_Pprint.op_Hat_Hat uu____3917 uu____3918  in
        FStar_Pprint.op_Hat_Hat uu____3915 uu____3916

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3926  ->
    match uu____3926 with
    | (pat,uu____3932) ->
        let uu____3933 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed (pat1,t) ->
              let uu____3944 =
                let uu____3945 =
                  let uu____3946 =
                    let uu____3947 =
                      let uu____3948 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3948
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3947  in
                  FStar_Pprint.group uu____3946  in
                FStar_Pprint.op_Hat_Hat break1 uu____3945  in
              (pat1, uu____3944)
          | uu____3949 -> (pat, FStar_Pprint.empty)  in
        (match uu____3933 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____3953);
                     FStar_Parser_AST.prange = uu____3954;_},pats)
                  ->
                  let uu____3964 =
                    let uu____3965 = p_lident x  in
                    let uu____3966 =
                      let uu____3967 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____3967 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____3965 uu____3966  in
                  FStar_Pprint.group uu____3964
              | uu____3968 ->
                  let uu____3969 =
                    let uu____3970 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____3970 ascr_doc  in
                  FStar_Pprint.group uu____3969))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____3971  ->
    match uu____3971 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____3979 =
          let uu____3980 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____3980  in
        let uu____3981 = p_term e  in prefix2 uu____3979 uu____3981

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___54_3982  ->
    match uu___54_3982 with
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
        let uu____4007 = p_uident uid  in
        let uu____4008 = p_binders true bs  in
        let uu____4009 =
          let uu____4010 = p_simpleTerm t  in
          prefix2 FStar_Pprint.equals uu____4010  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4007 uu____4008 uu____4009

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
          let uu____4019 =
            let uu____4020 =
              let uu____4021 =
                let uu____4022 = p_uident uid  in
                let uu____4023 = p_binders true bs  in
                let uu____4024 =
                  let uu____4025 = p_typ t  in
                  prefix2 FStar_Pprint.colon uu____4025  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4022 uu____4023 uu____4024
                 in
              FStar_Pprint.group uu____4021  in
            let uu____4026 =
              let uu____4027 = str "with"  in
              let uu____4028 =
                separate_break_map FStar_Pprint.semi p_effectDecl eff_decls
                 in
              prefix2 uu____4027 uu____4028  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4020 uu____4026  in
          braces_with_nesting uu____4019

and (p_effectDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Tycon
        (false
         ,(FStar_Parser_AST.TyconAbbrev
           (lid,[],FStar_Pervasives_Native.None ,e),FStar_Pervasives_Native.None
           )::[])
        ->
        let uu____4058 =
          let uu____4059 = p_lident lid  in
          let uu____4060 =
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
             in
          FStar_Pprint.op_Hat_Hat uu____4059 uu____4060  in
        let uu____4061 = p_simpleTerm e  in prefix2 uu____4058 uu____4061
    | uu____4062 ->
        let uu____4063 =
          let uu____4064 = FStar_Parser_AST.decl_to_string d  in
          FStar_Util.format1
            "Not a declaration of an effect member... or at least I hope so : %s"
            uu____4064
           in
        failwith uu____4063

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lif_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift uu____4119 =
        match uu____4119 with
        | (kwd,t) ->
            let uu____4126 =
              let uu____4127 = str kwd  in
              let uu____4128 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4127 uu____4128  in
            let uu____4129 = p_simpleTerm t  in prefix2 uu____4126 uu____4129
         in
      separate_break_map FStar_Pprint.semi p_lift lifts  in
    let uu____4134 =
      let uu____4135 =
        let uu____4136 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4137 =
          let uu____4138 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4138  in
        FStar_Pprint.op_Hat_Hat uu____4136 uu____4137  in
      let uu____4139 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4135 uu____4139  in
    let uu____4140 =
      let uu____4141 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4141  in
    FStar_Pprint.op_Hat_Hat uu____4134 uu____4140

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___55_4142  ->
    match uu___55_4142 with
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
    let uu____4144 = FStar_Pprint.separate_map break1 p_qualifier qs  in
    FStar_Pprint.group uu____4144

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___56_4145  ->
    match uu___56_4145 with
    | FStar_Parser_AST.Rec  ->
        let uu____4146 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4146
    | FStar_Parser_AST.Mutable  ->
        let uu____4147 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4147
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___57_4148  ->
    match uu___57_4148 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4153 =
          let uu____4154 =
            let uu____4155 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4155  in
          FStar_Pprint.separate_map uu____4154 p_tuplePattern pats  in
        FStar_Pprint.group uu____4153
    | uu____4156 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4163 =
          let uu____4164 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4164 p_constructorPattern pats  in
        FStar_Pprint.group uu____4163
    | uu____4165 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4168;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4173 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4174 = p_constructorPattern hd1  in
        let uu____4175 = p_constructorPattern tl1  in
        infix0 uu____4173 uu____4174 uu____4175
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4177;_},pats)
        ->
        let uu____4183 = p_quident uid  in
        let uu____4184 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4183 uu____4184
    | uu____4185 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,t) ->
        let uu____4189 =
          let uu____4194 =
            let uu____4195 = unparen t  in uu____4195.FStar_Parser_AST.tm  in
          ((pat.FStar_Parser_AST.pat), uu____4194)  in
        (match uu____4189 with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4200;
               FStar_Parser_AST.blevel = uu____4201;
               FStar_Parser_AST.aqual = uu____4202;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4208 =
               let uu____4209 = p_ident lid  in
               p_refinement aqual uu____4209 t1 phi  in
             soft_parens_with_nesting uu____4208
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4211;
               FStar_Parser_AST.blevel = uu____4212;
               FStar_Parser_AST.aqual = uu____4213;_},phi))
             ->
             let uu____4215 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4215
         | uu____4216 ->
             let uu____4221 =
               let uu____4222 = p_tuplePattern pat  in
               let uu____4223 =
                 let uu____4224 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4225 =
                   let uu____4226 = p_typ t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4226  in
                 FStar_Pprint.op_Hat_Hat uu____4224 uu____4225  in
               FStar_Pprint.op_Hat_Hat uu____4222 uu____4223  in
             soft_parens_with_nesting uu____4221)
    | FStar_Parser_AST.PatList pats ->
        let uu____4230 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4230 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4245 =
          match uu____4245 with
          | (lid,pat) ->
              let uu____4252 = p_qlident lid  in
              let uu____4253 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4252 uu____4253
           in
        let uu____4254 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4254
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4264 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4265 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4266 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4264 uu____4265 uu____4266
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4277 =
          let uu____4278 =
            let uu____4279 = str (FStar_Ident.text_of_id op)  in
            let uu____4280 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4279 uu____4280  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4278  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4277
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4288 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4289 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4288 uu____4289
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4291 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4294;
           FStar_Parser_AST.prange = uu____4295;_},uu____4296)
        ->
        let uu____4301 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4301
    | FStar_Parser_AST.PatTuple (uu____4302,false ) ->
        let uu____4307 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4307
    | uu____4308 ->
        let uu____4309 =
          let uu____4310 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4310  in
        failwith uu____4309

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4314 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4315 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4314 uu____4315
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            let uu____4320 =
              let uu____4321 = unparen t  in uu____4321.FStar_Parser_AST.tm
               in
            match uu____4320 with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4324;
                   FStar_Parser_AST.blevel = uu____4325;
                   FStar_Parser_AST.aqual = uu____4326;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4328 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4328 t1 phi
            | uu____4329 ->
                let uu____4330 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4331 =
                  let uu____4332 = p_lident lid  in
                  let uu____4333 =
                    let uu____4334 =
                      let uu____4335 =
                        FStar_Pprint.break_ (Prims.parse_int "0")  in
                      let uu____4336 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4335 uu____4336  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4334  in
                  FStar_Pprint.op_Hat_Hat uu____4332 uu____4333  in
                FStar_Pprint.op_Hat_Hat uu____4330 uu____4331
             in
          if is_atomic
          then
            let uu____4337 =
              let uu____4338 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4338  in
            FStar_Pprint.group uu____4337
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4340 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          let uu____4346 =
            let uu____4347 = unparen t  in uu____4347.FStar_Parser_AST.tm  in
          (match uu____4346 with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4349;
                  FStar_Parser_AST.blevel = uu____4350;
                  FStar_Parser_AST.aqual = uu____4351;_},phi)
               ->
               if is_atomic
               then
                 let uu____4353 =
                   let uu____4354 =
                     let uu____4355 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4355 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4354  in
                 FStar_Pprint.group uu____4353
               else
                 (let uu____4357 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4357)
           | uu____4358 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let uu____4366 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4367 =
            let uu____4368 =
              let uu____4369 =
                let uu____4370 = p_appTerm t  in
                let uu____4371 =
                  let uu____4372 = p_noSeqTerm phi  in
                  soft_braces_with_nesting uu____4372  in
                FStar_Pprint.op_Hat_Hat uu____4370 uu____4371  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4369  in
            FStar_Pprint.op_Hat_Hat binder uu____4368  in
          FStar_Pprint.op_Hat_Hat uu____4366 uu____4367

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

and (p_term : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4386 =
      let uu____4387 = unparen e  in uu____4387.FStar_Parser_AST.tm  in
    match uu____4386 with
    | FStar_Parser_AST.Seq (e1,e2) ->
        let uu____4390 =
          let uu____4391 =
            let uu____4392 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____4392 FStar_Pprint.semi  in
          FStar_Pprint.group uu____4391  in
        let uu____4393 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4390 uu____4393
    | FStar_Parser_AST.Bind (x,e1,e2) ->
        let uu____4397 =
          let uu____4398 =
            let uu____4399 =
              let uu____4400 = p_lident x  in
              let uu____4401 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.long_left_arrow
                 in
              FStar_Pprint.op_Hat_Hat uu____4400 uu____4401  in
            let uu____4402 =
              let uu____4403 = p_noSeqTerm e1  in
              let uu____4404 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.semi
                 in
              FStar_Pprint.op_Hat_Hat uu____4403 uu____4404  in
            op_Hat_Slash_Plus_Hat uu____4399 uu____4402  in
          FStar_Pprint.group uu____4398  in
        let uu____4405 = p_term e2  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4397 uu____4405
    | uu____4406 ->
        let uu____4407 = p_noSeqTerm e  in FStar_Pprint.group uu____4407

and (p_noSeqTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_noSeqTerm' e e.FStar_Parser_AST.range

and (p_noSeqTerm' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4410 =
      let uu____4411 = unparen e  in uu____4411.FStar_Parser_AST.tm  in
    match uu____4410 with
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.None ) ->
        let uu____4416 =
          let uu____4417 = p_tmIff e1  in
          let uu____4418 =
            let uu____4419 =
              let uu____4420 = p_typ t  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4420  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4419  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4417 uu____4418  in
        FStar_Pprint.group uu____4416
    | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac) ->
        let uu____4426 =
          let uu____4427 = p_tmIff e1  in
          let uu____4428 =
            let uu____4429 =
              let uu____4430 =
                let uu____4431 = p_typ t  in
                let uu____4432 =
                  let uu____4433 = str "by"  in
                  let uu____4434 = p_typ tac  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4433 uu____4434  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4431 uu____4432  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4430  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4429  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4427 uu____4428  in
        FStar_Pprint.group uu____4426
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".()<-"; FStar_Ident.idRange = uu____4435;_},e1::e2::e3::[])
        ->
        let uu____4441 =
          let uu____4442 =
            let uu____4443 =
              let uu____4444 = p_atomicTermNotQUident e1  in
              let uu____4445 =
                let uu____4446 =
                  let uu____4447 =
                    let uu____4448 = p_term e2  in
                    soft_parens_with_nesting uu____4448  in
                  let uu____4449 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4447 uu____4449  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4446  in
              FStar_Pprint.op_Hat_Hat uu____4444 uu____4445  in
            FStar_Pprint.group uu____4443  in
          let uu____4450 =
            let uu____4451 = p_noSeqTerm e3  in jump2 uu____4451  in
          FStar_Pprint.op_Hat_Hat uu____4442 uu____4450  in
        FStar_Pprint.group uu____4441
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = ".[]<-"; FStar_Ident.idRange = uu____4452;_},e1::e2::e3::[])
        ->
        let uu____4458 =
          let uu____4459 =
            let uu____4460 =
              let uu____4461 = p_atomicTermNotQUident e1  in
              let uu____4462 =
                let uu____4463 =
                  let uu____4464 =
                    let uu____4465 = p_term e2  in
                    soft_brackets_with_nesting uu____4465  in
                  let uu____4466 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.larrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4464 uu____4466  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4463  in
              FStar_Pprint.op_Hat_Hat uu____4461 uu____4462  in
            FStar_Pprint.group uu____4460  in
          let uu____4467 =
            let uu____4468 = p_noSeqTerm e3  in jump2 uu____4468  in
          FStar_Pprint.op_Hat_Hat uu____4459 uu____4467  in
        FStar_Pprint.group uu____4458
    | FStar_Parser_AST.Requires (e1,wtf) ->
        let uu____4478 =
          let uu____4479 = str "requires"  in
          let uu____4480 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4479 uu____4480  in
        FStar_Pprint.group uu____4478
    | FStar_Parser_AST.Ensures (e1,wtf) ->
        let uu____4490 =
          let uu____4491 = str "ensures"  in
          let uu____4492 = p_typ e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4491 uu____4492  in
        FStar_Pprint.group uu____4490
    | FStar_Parser_AST.Attributes es ->
        let uu____4496 =
          let uu____4497 = str "attributes"  in
          let uu____4498 = FStar_Pprint.separate_map break1 p_atomicTerm es
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4497 uu____4498  in
        FStar_Pprint.group uu____4496
    | FStar_Parser_AST.If (e1,e2,e3) ->
        let uu____4502 = is_unit e3  in
        if uu____4502
        then
          let uu____4503 =
            let uu____4504 =
              let uu____4505 = str "if"  in
              let uu____4506 = p_noSeqTerm e1  in
              op_Hat_Slash_Plus_Hat uu____4505 uu____4506  in
            let uu____4507 =
              let uu____4508 = str "then"  in
              let uu____4509 = p_noSeqTerm e2  in
              op_Hat_Slash_Plus_Hat uu____4508 uu____4509  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4504 uu____4507  in
          FStar_Pprint.group uu____4503
        else
          (let e2_doc =
             let uu____4512 =
               let uu____4513 = unparen e2  in uu____4513.FStar_Parser_AST.tm
                in
             match uu____4512 with
             | FStar_Parser_AST.If (uu____4514,uu____4515,e31) when
                 is_unit e31 ->
                 let uu____4517 = p_noSeqTerm e2  in
                 soft_parens_with_nesting uu____4517
             | uu____4518 -> p_noSeqTerm e2  in
           let uu____4519 =
             let uu____4520 =
               let uu____4521 = str "if"  in
               let uu____4522 = p_noSeqTerm e1  in
               op_Hat_Slash_Plus_Hat uu____4521 uu____4522  in
             let uu____4523 =
               let uu____4524 =
                 let uu____4525 = str "then"  in
                 op_Hat_Slash_Plus_Hat uu____4525 e2_doc  in
               let uu____4526 =
                 let uu____4527 = str "else"  in
                 let uu____4528 = p_noSeqTerm e3  in
                 op_Hat_Slash_Plus_Hat uu____4527 uu____4528  in
               FStar_Pprint.op_Hat_Slash_Hat uu____4524 uu____4526  in
             FStar_Pprint.op_Hat_Slash_Hat uu____4520 uu____4523  in
           FStar_Pprint.group uu____4519)
    | FStar_Parser_AST.TryWith (e1,branches) ->
        let uu____4551 =
          let uu____4552 =
            let uu____4553 = str "try"  in
            let uu____4554 = p_noSeqTerm e1  in prefix2 uu____4553 uu____4554
             in
          let uu____4555 =
            let uu____4556 = str "with"  in
            let uu____4557 =
              FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
                branches
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____4556 uu____4557  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4552 uu____4555  in
        FStar_Pprint.group uu____4551
    | FStar_Parser_AST.Match (e1,branches) ->
        let uu____4588 =
          let uu____4589 =
            let uu____4590 = str "match"  in
            let uu____4591 = p_noSeqTerm e1  in
            let uu____4592 = str "with"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4590 uu____4591 uu____4592
             in
          let uu____4593 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4589 uu____4593  in
        FStar_Pprint.group uu____4588
    | FStar_Parser_AST.LetOpen (uid,e1) ->
        let uu____4604 =
          let uu____4605 =
            let uu____4606 = str "let open"  in
            let uu____4607 = p_quident uid  in
            let uu____4608 = str "in"  in
            FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
              uu____4606 uu____4607 uu____4608
             in
          let uu____4609 = p_term e1  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4605 uu____4609  in
        FStar_Pprint.group uu____4604
    | FStar_Parser_AST.Let (q,lbs,e1) ->
        let let_doc =
          let uu____4626 = str "let"  in
          let uu____4627 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____4626 uu____4627  in
        let uu____4628 =
          let uu____4629 =
            let uu____4630 =
              let uu____4631 = str "and"  in
              precede_break_separate_map let_doc uu____4631 p_letbinding lbs
               in
            let uu____4636 = str "in"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4630 uu____4636  in
          FStar_Pprint.group uu____4629  in
        let uu____4637 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4628 uu____4637
    | FStar_Parser_AST.Abs
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
           FStar_Parser_AST.prange = uu____4640;_}::[],{
                                                         FStar_Parser_AST.tm
                                                           =
                                                           FStar_Parser_AST.Match
                                                           (maybe_x,branches);
                                                         FStar_Parser_AST.range
                                                           = uu____4643;
                                                         FStar_Parser_AST.level
                                                           = uu____4644;_})
        when matches_var maybe_x x ->
        let uu____4671 =
          let uu____4672 = str "function"  in
          let uu____4673 =
            FStar_Pprint.separate_map FStar_Pprint.hardline p_patternBranch
              branches
             in
          FStar_Pprint.op_Hat_Slash_Hat uu____4672 uu____4673  in
        FStar_Pprint.group uu____4671
    | FStar_Parser_AST.Assign (id1,e1) ->
        let uu____4684 =
          let uu____4685 = p_lident id1  in
          let uu____4686 =
            let uu____4687 = p_noSeqTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.larrow uu____4687  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4685 uu____4686  in
        FStar_Pprint.group uu____4684
    | uu____4688 -> p_typ e

and (p_typ : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_typ' e e.FStar_Parser_AST.range

and (p_typ' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4691 =
      let uu____4692 = unparen e  in uu____4692.FStar_Parser_AST.tm  in
    match uu____4691 with
    | FStar_Parser_AST.QForall (bs,trigger,e1) ->
        let uu____4708 =
          let uu____4709 =
            let uu____4710 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4710 FStar_Pprint.space  in
          let uu____4711 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4709 uu____4711 FStar_Pprint.dot
           in
        let uu____4712 =
          let uu____4713 = p_trigger trigger  in
          let uu____4714 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4713 uu____4714  in
        prefix2 uu____4708 uu____4712
    | FStar_Parser_AST.QExists (bs,trigger,e1) ->
        let uu____4730 =
          let uu____4731 =
            let uu____4732 = p_quantifier e  in
            FStar_Pprint.op_Hat_Hat uu____4732 FStar_Pprint.space  in
          let uu____4733 = p_binders true bs  in
          FStar_Pprint.soft_surround (Prims.parse_int "2")
            (Prims.parse_int "0") uu____4731 uu____4733 FStar_Pprint.dot
           in
        let uu____4734 =
          let uu____4735 = p_trigger trigger  in
          let uu____4736 = p_noSeqTerm e1  in
          FStar_Pprint.op_Hat_Hat uu____4735 uu____4736  in
        prefix2 uu____4730 uu____4734
    | uu____4737 -> p_simpleTerm e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4739 =
      let uu____4740 = unparen e  in uu____4740.FStar_Parser_AST.tm  in
    match uu____4739 with
    | FStar_Parser_AST.QForall uu____4741 -> str "forall"
    | FStar_Parser_AST.QExists uu____4754 -> str "exists"
    | uu____4767 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___58_4768  ->
    match uu___58_4768 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____4780 =
          let uu____4781 =
            let uu____4782 = str "pattern"  in
            let uu____4783 =
              let uu____4784 =
                let uu____4785 = p_disjunctivePats pats  in jump2 uu____4785
                 in
              let uu____4786 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4784 uu____4786  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4782 uu____4783  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4781  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____4780

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____4792 = str "\\/"  in
    FStar_Pprint.separate_map uu____4792 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____4798 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____4798

and (p_simpleTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4800 =
      let uu____4801 = unparen e  in uu____4801.FStar_Parser_AST.tm  in
    match uu____4800 with
    | FStar_Parser_AST.Abs (pats,e1) ->
        let uu____4808 =
          let uu____4809 = str "fun"  in
          let uu____4810 =
            let uu____4811 =
              FStar_Pprint.separate_map break1 p_atomicPattern pats  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4811 FStar_Pprint.rarrow  in
          op_Hat_Slash_Plus_Hat uu____4809 uu____4810  in
        let uu____4812 = p_term e1  in
        op_Hat_Slash_Plus_Hat uu____4808 uu____4812
    | uu____4813 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                              FStar_Pervasives_Native.option,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun uu____4816  ->
    match uu____4816 with
    | (pat,when_opt,e) ->
        let maybe_paren =
          let uu____4835 =
            let uu____4836 = unparen e  in uu____4836.FStar_Parser_AST.tm  in
          match uu____4835 with
          | FStar_Parser_AST.Match uu____4839 -> soft_begin_end_with_nesting
          | FStar_Parser_AST.TryWith uu____4854 ->
              soft_begin_end_with_nesting
          | FStar_Parser_AST.Abs
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____4870);
                 FStar_Parser_AST.prange = uu____4871;_}::[],{
                                                               FStar_Parser_AST.tm
                                                                 =
                                                                 FStar_Parser_AST.Match
                                                                 (maybe_x,uu____4873);
                                                               FStar_Parser_AST.range
                                                                 = uu____4874;
                                                               FStar_Parser_AST.level
                                                                 = uu____4875;_})
              when matches_var maybe_x x -> soft_begin_end_with_nesting
          | uu____4902 -> (fun x  -> x)  in
        let uu____4904 =
          let uu____4905 =
            let uu____4906 =
              let uu____4907 =
                let uu____4908 =
                  let uu____4909 = p_disjunctivePattern pat  in
                  let uu____4910 =
                    let uu____4911 = p_maybeWhen when_opt  in
                    FStar_Pprint.op_Hat_Hat uu____4911 FStar_Pprint.rarrow
                     in
                  op_Hat_Slash_Plus_Hat uu____4909 uu____4910  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4908  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4907  in
            FStar_Pprint.group uu____4906  in
          let uu____4912 =
            let uu____4913 = p_term e  in maybe_paren uu____4913  in
          op_Hat_Slash_Plus_Hat uu____4905 uu____4912  in
        FStar_Pprint.group uu____4904

and (p_maybeWhen :
  FStar_Parser_AST.term FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_4914  ->
    match uu___59_4914 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some e ->
        let uu____4918 = str "when"  in
        let uu____4919 =
          let uu____4920 = p_tmFormula e  in
          FStar_Pprint.op_Hat_Hat uu____4920 FStar_Pprint.space  in
        op_Hat_Slash_Plus_Hat uu____4918 uu____4919

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4922 =
      let uu____4923 = unparen e  in uu____4923.FStar_Parser_AST.tm  in
    match uu____4922 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____4924;_},e1::e2::[])
        ->
        let uu____4929 = str "<==>"  in
        let uu____4930 = p_tmImplies e1  in
        let uu____4931 = p_tmIff e2  in
        infix0 uu____4929 uu____4930 uu____4931
    | uu____4932 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4934 =
      let uu____4935 = unparen e  in uu____4935.FStar_Parser_AST.tm  in
    match uu____4934 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____4936;_},e1::e2::[])
        ->
        let uu____4941 = str "==>"  in
        let uu____4942 = p_tmArrow p_tmFormula e1  in
        let uu____4943 = p_tmImplies e2  in
        infix0 uu____4941 uu____4942 uu____4943
    | uu____4944 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let uu____4949 =
        let uu____4950 = unparen e  in uu____4950.FStar_Parser_AST.tm  in
      match uu____4949 with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____4957 =
            let uu____4958 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____4963 = p_binder false b  in
                   let uu____4964 =
                     let uu____4965 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4965
                      in
                   FStar_Pprint.op_Hat_Hat uu____4963 uu____4964) bs
               in
            let uu____4966 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____4958 uu____4966  in
          FStar_Pprint.group uu____4957
      | uu____4967 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4969 =
      let uu____4970 = unparen e  in uu____4970.FStar_Parser_AST.tm  in
    match uu____4969 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____4971;_},e1::e2::[])
        ->
        let uu____4976 = str "\\/"  in
        let uu____4977 = p_tmFormula e1  in
        let uu____4978 = p_tmConjunction e2  in
        infix0 uu____4976 uu____4977 uu____4978
    | uu____4979 -> p_tmConjunction e

and (p_tmConjunction : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4981 =
      let uu____4982 = unparen e  in uu____4982.FStar_Parser_AST.tm  in
    match uu____4981 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____4983;_},e1::e2::[])
        ->
        let uu____4988 = str "/\\"  in
        let uu____4989 = p_tmConjunction e1  in
        let uu____4990 = p_tmTuple e2  in
        infix0 uu____4988 uu____4989 uu____4990
    | uu____4991 -> p_tmTuple e

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____4994 =
      let uu____4995 = unparen e  in uu____4995.FStar_Parser_AST.tm  in
    match uu____4994 with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5010 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5010
          (fun uu____5018  ->
             match uu____5018 with | (e1,uu____5024) -> p_tmEq e1) args
    | uu____5025 -> p_tmEq e

and (paren_if :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5030 =
             let uu____5031 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5031  in
           FStar_Pprint.group uu____5030)

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
      let uu____5082 =
        let uu____5083 = unparen e  in uu____5083.FStar_Parser_AST.tm  in
      match uu____5082 with
      | FStar_Parser_AST.Op (op,e1::e2::[]) when
          ((is_operatorInfix0ad12 op) || ((FStar_Ident.text_of_id op) = "="))
            || ((FStar_Ident.text_of_id op) = "|>")
          ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5090 = levels op1  in
          (match uu____5090 with
           | (left1,mine,right1) ->
               let uu____5100 =
                 let uu____5101 = FStar_All.pipe_left str op1  in
                 let uu____5102 = p_tmEq' left1 e1  in
                 let uu____5103 = p_tmEq' right1 e2  in
                 infix0 uu____5101 uu____5102 uu____5103  in
               paren_if curr mine uu____5100)
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5104;_},e1::e2::[])
          ->
          let uu____5109 =
            let uu____5110 = p_tmEq e1  in
            let uu____5111 =
              let uu____5112 =
                let uu____5113 =
                  let uu____5114 = p_tmEq e2  in
                  op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5114  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5113  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5112  in
            FStar_Pprint.op_Hat_Hat uu____5110 uu____5111  in
          FStar_Pprint.group uu____5109
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5115;_},e1::[])
          ->
          let uu____5119 = levels "-"  in
          (match uu____5119 with
           | (left1,mine,right1) ->
               let uu____5129 = p_tmEq' mine e1  in
               FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5129)
      | uu____5130 -> p_tmNoEq e

and (p_tmNoEq : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]  in
    p_tmNoEq' n1 e

and (p_tmNoEq' : Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun curr  ->
    fun e  ->
      let uu____5193 =
        let uu____5194 = unparen e  in uu____5194.FStar_Parser_AST.tm  in
      match uu____5193 with
      | FStar_Parser_AST.Construct (lid,(e1,uu____5197)::(e2,uu____5199)::[])
          when
          (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
            (let uu____5219 = is_list e  in Prims.op_Negation uu____5219)
          ->
          let op = "::"  in
          let uu____5221 = levels op  in
          (match uu____5221 with
           | (left1,mine,right1) ->
               let uu____5231 =
                 let uu____5232 = str op  in
                 let uu____5233 = p_tmNoEq' left1 e1  in
                 let uu____5234 = p_tmNoEq' right1 e2  in
                 infix0 uu____5232 uu____5233 uu____5234  in
               paren_if curr mine uu____5231)
      | FStar_Parser_AST.Sum (binders,res) ->
          let op = "&"  in
          let uu____5242 = levels op  in
          (match uu____5242 with
           | (left1,mine,right1) ->
               let p_dsumfst b =
                 let uu____5256 = p_binder false b  in
                 let uu____5257 =
                   let uu____5258 =
                     let uu____5259 = str op  in
                     FStar_Pprint.op_Hat_Hat uu____5259 break1  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5258  in
                 FStar_Pprint.op_Hat_Hat uu____5256 uu____5257  in
               let uu____5260 =
                 let uu____5261 = FStar_Pprint.concat_map p_dsumfst binders
                    in
                 let uu____5262 = p_tmNoEq' right1 res  in
                 FStar_Pprint.op_Hat_Hat uu____5261 uu____5262  in
               paren_if curr mine uu____5260)
      | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
          let op1 = FStar_Ident.text_of_id op  in
          let uu____5269 = levels op1  in
          (match uu____5269 with
           | (left1,mine,right1) ->
               let uu____5279 =
                 let uu____5280 = str op1  in
                 let uu____5281 = p_tmNoEq' left1 e1  in
                 let uu____5282 = p_tmNoEq' right1 e2  in
                 infix0 uu____5280 uu____5281 uu____5282  in
               paren_if curr mine uu____5279)
      | FStar_Parser_AST.NamedTyp (lid,e1) ->
          let uu____5285 =
            let uu____5286 = p_lidentOrUnderscore lid  in
            let uu____5287 =
              let uu____5288 = p_appTerm e1  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5288  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5286 uu____5287  in
          FStar_Pprint.group uu____5285
      | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
      | FStar_Parser_AST.Record (with_opt,record_fields) ->
          let uu____5309 =
            let uu____5310 =
              default_or_map FStar_Pprint.empty p_with_clause with_opt  in
            let uu____5311 =
              let uu____5312 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
              FStar_Pprint.separate_map uu____5312 p_simpleDef record_fields
               in
            FStar_Pprint.op_Hat_Hat uu____5310 uu____5311  in
          braces_with_nesting uu____5309
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5317;_},e1::[])
          ->
          let uu____5321 =
            let uu____5322 = str "~"  in
            let uu____5323 = p_atomicTerm e1  in
            FStar_Pprint.op_Hat_Hat uu____5322 uu____5323  in
          FStar_Pprint.group uu____5321
      | uu____5324 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5326 = p_appTerm e  in
    let uu____5327 =
      let uu____5328 =
        let uu____5329 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5329 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5328  in
    FStar_Pprint.op_Hat_Hat uu____5326 uu____5327

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5334 =
            let uu____5335 = p_lident lid  in
            p_refinement b.FStar_Parser_AST.aqual uu____5335 t phi  in
          soft_parens_with_nesting uu____5334
      | FStar_Parser_AST.TAnnotated uu____5336 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5341 ->
          let uu____5342 =
            let uu____5343 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5343
             in
          failwith uu____5342
      | FStar_Parser_AST.TVariable uu____5344 ->
          let uu____5345 =
            let uu____5346 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5346
             in
          failwith uu____5345
      | FStar_Parser_AST.NoName uu____5347 ->
          let uu____5348 =
            let uu____5349 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5349
             in
          failwith uu____5348

and (p_simpleDef :
  (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
    FStar_Pprint.document)
  =
  fun uu____5350  ->
    match uu____5350 with
    | (lid,e) ->
        let uu____5357 =
          let uu____5358 = p_qlident lid  in
          let uu____5359 =
            let uu____5360 = p_tmIff e  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5360  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5358 uu____5359  in
        FStar_Pprint.group uu____5357

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5362 =
      let uu____5363 = unparen e  in uu____5363.FStar_Parser_AST.tm  in
    match uu____5362 with
    | FStar_Parser_AST.App uu____5364 when is_general_application e ->
        let uu____5371 = head_and_args e  in
        (match uu____5371 with
         | (head1,args) ->
             let uu____5396 =
               let uu____5407 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5407
               then
                 let uu____5437 =
                   FStar_Util.take
                     (fun uu____5461  ->
                        match uu____5461 with
                        | (uu____5466,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5437 with
                 | (fs_typ_args,args1) ->
                     let uu____5504 =
                       let uu____5505 = p_indexingTerm head1  in
                       let uu____5506 =
                         let uu____5507 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____5507 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____5505 uu____5506  in
                     (uu____5504, args1)
               else
                 (let uu____5519 = p_indexingTerm head1  in
                  (uu____5519, args))
                in
             (match uu____5396 with
              | (head_doc,args1) ->
                  let uu____5540 =
                    let uu____5541 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____5541 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____5540))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____5561 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____5561)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____5579 =
               let uu____5580 = p_quident lid  in
               let uu____5581 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____5580 uu____5581  in
             FStar_Pprint.group uu____5579
         | hd1::tl1 ->
             let uu____5598 =
               let uu____5599 =
                 let uu____5600 =
                   let uu____5601 = p_quident lid  in
                   let uu____5602 = p_argTerm hd1  in
                   prefix2 uu____5601 uu____5602  in
                 FStar_Pprint.group uu____5600  in
               let uu____5603 =
                 let uu____5604 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____5604  in
               FStar_Pprint.op_Hat_Hat uu____5599 uu____5603  in
             FStar_Pprint.group uu____5598)
    | uu____5609 -> p_indexingTerm e

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
         (let uu____5618 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____5618 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____5620 = str "#"  in
        let uu____5621 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____5620 uu____5621
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____5623  ->
    match uu____5623 with | (e,uu____5629) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      let uu____5634 =
        let uu____5635 = unparen e  in uu____5635.FStar_Parser_AST.tm  in
      match uu____5634 with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____5636;_},e1::e2::[])
          ->
          let uu____5641 =
            let uu____5642 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5643 =
              let uu____5644 =
                let uu____5645 = p_term e2  in
                soft_parens_with_nesting uu____5645  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5644  in
            FStar_Pprint.op_Hat_Hat uu____5642 uu____5643  in
          FStar_Pprint.group uu____5641
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____5646;_},e1::e2::[])
          ->
          let uu____5651 =
            let uu____5652 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____5653 =
              let uu____5654 =
                let uu____5655 = p_term e2  in
                soft_brackets_with_nesting uu____5655  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5654  in
            FStar_Pprint.op_Hat_Hat uu____5652 uu____5653  in
          FStar_Pprint.group uu____5651
      | uu____5656 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5659 =
      let uu____5660 = unparen e  in uu____5660.FStar_Parser_AST.tm  in
    match uu____5659 with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____5663 = p_quident lid  in
        let uu____5664 =
          let uu____5665 =
            let uu____5666 = p_term e1  in
            soft_parens_with_nesting uu____5666  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5665  in
        FStar_Pprint.op_Hat_Hat uu____5663 uu____5664
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5672 = str (FStar_Ident.text_of_id op)  in
        let uu____5673 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____5672 uu____5673
    | uu____5674 -> p_atomicTermNotQUident e

and (p_atomicTermNotQUident : FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun e  ->
    let uu____5676 =
      let uu____5677 = unparen e  in uu____5677.FStar_Parser_AST.tm  in
    match uu____5676 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Var lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.assert_lid ->
        str "assert"
    | FStar_Parser_AST.Tvar tv -> p_tvar tv
    | FStar_Parser_AST.Const c ->
        (match c with
         | FStar_Const.Const_char x when x = 10 -> str "0x0Az"
         | uu____5683 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____5690 = str (FStar_Ident.text_of_id op)  in
        let uu____5691 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____5690 uu____5691
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____5695 =
          let uu____5696 =
            let uu____5697 = str (FStar_Ident.text_of_id op)  in
            let uu____5698 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____5697 uu____5698  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5696  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5695
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____5713 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____5714 =
          let uu____5715 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____5716 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____5715 p_tmEq uu____5716  in
        let uu____5723 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5713 uu____5714 uu____5723
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____5726 =
          let uu____5727 = p_atomicTermNotQUident e1  in
          let uu____5728 =
            let uu____5729 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5729  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____5727 uu____5728
           in
        FStar_Pprint.group uu____5726
    | uu____5730 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5732 =
      let uu____5733 = unparen e  in uu____5733.FStar_Parser_AST.tm  in
    match uu____5732 with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____5737 = p_quident constr_lid  in
        let uu____5738 =
          let uu____5739 =
            let uu____5740 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____5740  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____5739  in
        FStar_Pprint.op_Hat_Hat uu____5737 uu____5738
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____5742 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____5742 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____5744 = p_term e1  in soft_parens_with_nesting uu____5744
    | uu____5745 when is_array e ->
        let es = extract_from_list e  in
        let uu____5749 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____5750 =
          let uu____5751 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow uu____5751 p_noSeqTerm es  in
        let uu____5752 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5749 uu____5750 uu____5752
    | uu____5753 when is_list e ->
        let uu____5754 =
          let uu____5755 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5756 = extract_from_list e  in
          separate_map_or_flow uu____5755 p_noSeqTerm uu____5756  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____5754 FStar_Pprint.rbracket
    | uu____5759 when is_lex_list e ->
        let uu____5760 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____5761 =
          let uu____5762 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____5763 = extract_from_list e  in
          separate_map_or_flow uu____5762 p_noSeqTerm uu____5763  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____5760 uu____5761 FStar_Pprint.rbracket
    | uu____5766 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____5770 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____5771 =
          let uu____5772 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____5772 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____5770 uu____5771 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____5776 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____5777 = p_term e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____5776 uu____5777
    | FStar_Parser_AST.Op (op,args) when
        let uu____5784 = handleable_op op args  in
        Prims.op_Negation uu____5784 ->
        let uu____5785 =
          let uu____5786 =
            let uu____5787 =
              let uu____5788 =
                let uu____5789 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____5789
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____5788  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____5787  in
          Prims.strcat "Operation " uu____5786  in
        failwith uu____5785
    | FStar_Parser_AST.Uvar uu____5790 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____5791 = p_term e  in soft_parens_with_nesting uu____5791
    | FStar_Parser_AST.Const uu____5792 ->
        let uu____5793 = p_term e  in soft_parens_with_nesting uu____5793
    | FStar_Parser_AST.Op uu____5794 ->
        let uu____5801 = p_term e  in soft_parens_with_nesting uu____5801
    | FStar_Parser_AST.Tvar uu____5802 ->
        let uu____5803 = p_term e  in soft_parens_with_nesting uu____5803
    | FStar_Parser_AST.Var uu____5804 ->
        let uu____5805 = p_term e  in soft_parens_with_nesting uu____5805
    | FStar_Parser_AST.Name uu____5806 ->
        let uu____5807 = p_term e  in soft_parens_with_nesting uu____5807
    | FStar_Parser_AST.Construct uu____5808 ->
        let uu____5819 = p_term e  in soft_parens_with_nesting uu____5819
    | FStar_Parser_AST.Abs uu____5820 ->
        let uu____5827 = p_term e  in soft_parens_with_nesting uu____5827
    | FStar_Parser_AST.App uu____5828 ->
        let uu____5835 = p_term e  in soft_parens_with_nesting uu____5835
    | FStar_Parser_AST.Let uu____5836 ->
        let uu____5849 = p_term e  in soft_parens_with_nesting uu____5849
    | FStar_Parser_AST.LetOpen uu____5850 ->
        let uu____5855 = p_term e  in soft_parens_with_nesting uu____5855
    | FStar_Parser_AST.Seq uu____5856 ->
        let uu____5861 = p_term e  in soft_parens_with_nesting uu____5861
    | FStar_Parser_AST.Bind uu____5862 ->
        let uu____5869 = p_term e  in soft_parens_with_nesting uu____5869
    | FStar_Parser_AST.If uu____5870 ->
        let uu____5877 = p_term e  in soft_parens_with_nesting uu____5877
    | FStar_Parser_AST.Match uu____5878 ->
        let uu____5893 = p_term e  in soft_parens_with_nesting uu____5893
    | FStar_Parser_AST.TryWith uu____5894 ->
        let uu____5909 = p_term e  in soft_parens_with_nesting uu____5909
    | FStar_Parser_AST.Ascribed uu____5910 ->
        let uu____5919 = p_term e  in soft_parens_with_nesting uu____5919
    | FStar_Parser_AST.Record uu____5920 ->
        let uu____5933 = p_term e  in soft_parens_with_nesting uu____5933
    | FStar_Parser_AST.Project uu____5934 ->
        let uu____5939 = p_term e  in soft_parens_with_nesting uu____5939
    | FStar_Parser_AST.Product uu____5940 ->
        let uu____5947 = p_term e  in soft_parens_with_nesting uu____5947
    | FStar_Parser_AST.Sum uu____5948 ->
        let uu____5955 = p_term e  in soft_parens_with_nesting uu____5955
    | FStar_Parser_AST.QForall uu____5956 ->
        let uu____5969 = p_term e  in soft_parens_with_nesting uu____5969
    | FStar_Parser_AST.QExists uu____5970 ->
        let uu____5983 = p_term e  in soft_parens_with_nesting uu____5983
    | FStar_Parser_AST.Refine uu____5984 ->
        let uu____5989 = p_term e  in soft_parens_with_nesting uu____5989
    | FStar_Parser_AST.NamedTyp uu____5990 ->
        let uu____5995 = p_term e  in soft_parens_with_nesting uu____5995
    | FStar_Parser_AST.Requires uu____5996 ->
        let uu____6003 = p_term e  in soft_parens_with_nesting uu____6003
    | FStar_Parser_AST.Ensures uu____6004 ->
        let uu____6011 = p_term e  in soft_parens_with_nesting uu____6011
    | FStar_Parser_AST.Assign uu____6012 ->
        let uu____6017 = p_term e  in soft_parens_with_nesting uu____6017
    | FStar_Parser_AST.Attributes uu____6018 ->
        let uu____6021 = p_term e  in soft_parens_with_nesting uu____6021

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___62_6022  ->
    match uu___62_6022 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6026 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6026
    | FStar_Const.Const_string (s,uu____6028) ->
        let uu____6029 = str s  in FStar_Pprint.dquotes uu____6029
    | FStar_Const.Const_bytearray (bytes,uu____6031) ->
        let uu____6036 =
          let uu____6037 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6037  in
        let uu____6038 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6036 uu____6038
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___60_6056 =
          match uu___60_6056 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___61_6060 =
          match uu___61_6060 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6071  ->
               match uu____6071 with
               | (s,w) ->
                   let uu____6078 = signedness s  in
                   let uu____6079 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6078 uu____6079)
            sign_width_opt
           in
        let uu____6080 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6080 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6082 = FStar_Range.string_of_range r  in str uu____6082
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6084 = p_quident lid  in
        let uu____6085 =
          let uu____6086 =
            let uu____6087 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6087  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6086  in
        FStar_Pprint.op_Hat_Hat uu____6084 uu____6085

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6089 = str "u#"  in
    let uu____6090 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6089 uu____6090

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6092 =
      let uu____6093 = unparen u  in uu____6093.FStar_Parser_AST.tm  in
    match uu____6092 with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6094;_},u1::u2::[])
        ->
        let uu____6099 =
          let uu____6100 = p_universeFrom u1  in
          let uu____6101 =
            let uu____6102 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6102  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6100 uu____6101  in
        FStar_Pprint.group uu____6099
    | FStar_Parser_AST.App uu____6103 ->
        let uu____6110 = head_and_args u  in
        (match uu____6110 with
         | (head1,args) ->
             let uu____6135 =
               let uu____6136 = unparen head1  in
               uu____6136.FStar_Parser_AST.tm  in
             (match uu____6135 with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6138 =
                    let uu____6139 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6140 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6148  ->
                           match uu____6148 with
                           | (u1,uu____6154) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6139 uu____6140  in
                  FStar_Pprint.group uu____6138
              | uu____6155 ->
                  let uu____6156 =
                    let uu____6157 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6157
                     in
                  failwith uu____6156))
    | uu____6158 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6160 =
      let uu____6161 = unparen u  in uu____6161.FStar_Parser_AST.tm  in
    match uu____6160 with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6184 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6184
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6185;_},uu____6186::uu____6187::[])
        ->
        let uu____6190 = p_universeFrom u  in
        soft_parens_with_nesting uu____6190
    | FStar_Parser_AST.App uu____6191 ->
        let uu____6198 = p_universeFrom u  in
        soft_parens_with_nesting uu____6198
    | uu____6199 ->
        let uu____6200 =
          let uu____6201 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6201
           in
        failwith uu____6200

let (term_to_document : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_term e 
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
       | FStar_Parser_AST.Module (uu____6241,decls) ->
           let uu____6247 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6247
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6256,decls,uu____6258) ->
           let uu____6263 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6263
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6314  ->
         match uu____6314 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6354,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6360,decls,uu____6362) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6407 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6420;
                 FStar_Parser_AST.doc = uu____6421;
                 FStar_Parser_AST.quals = uu____6422;
                 FStar_Parser_AST.attrs = uu____6423;_}::uu____6424 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6430 =
                   let uu____6433 =
                     let uu____6436 = FStar_List.tl ds  in d :: uu____6436
                      in
                   d0 :: uu____6433  in
                 (uu____6430, (d0.FStar_Parser_AST.drange))
             | uu____6441 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6407 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____6499 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____6499 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____6595 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____6595, comments1))))))
  