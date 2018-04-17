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
  
let (soft_braces_with_nesting_tight :
  FStar_Pprint.document -> FStar_Pprint.document) =
  fun contents  ->
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "0")
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
    let uu____282 = str "begin"  in
    let uu____283 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____282 contents uu____283
  
let separate_map_last :
  'Auu____288 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____288 -> FStar_Pprint.document) ->
        'Auu____288 Prims.list -> FStar_Pprint.document
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
  'Auu____333 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____333 -> FStar_Pprint.document) ->
        'Auu____333 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____360 =
          let uu____361 =
            let uu____362 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____362  in
          separate_map_last uu____361 f l  in
        FStar_Pprint.group uu____360
  
let separate_map_or_flow :
  'Auu____367 .
    FStar_Pprint.document ->
      ('Auu____367 -> FStar_Pprint.document) ->
        'Auu____367 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____394 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____394 -> FStar_Pprint.document) ->
        'Auu____394 Prims.list -> FStar_Pprint.document
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
  'Auu____439 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____439 -> FStar_Pprint.document) ->
        'Auu____439 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then separate_map_last sep f l
        else flow_map_last sep f l
  
let (separate_or_flow :
  FStar_Pprint.document ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun sep  -> fun l  -> separate_map_or_flow sep FStar_Pervasives.id l 
let soft_surround_separate_map :
  'Auu____486 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____486 -> FStar_Pprint.document) ->
                  'Auu____486 Prims.list -> FStar_Pprint.document
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
                    (let uu____531 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____531
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____541 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____541 -> FStar_Pprint.document) ->
                  'Auu____541 Prims.list -> FStar_Pprint.document
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
                    (let uu____586 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____586
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____599  ->
    match uu____599 with
    | (comment,keywords) ->
        let uu____624 =
          let uu____625 =
            let uu____628 = str comment  in
            let uu____629 =
              let uu____632 =
                let uu____635 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____644  ->
                       match uu____644 with
                       | (k,v1) ->
                           let uu____651 =
                             let uu____654 = str k  in
                             let uu____655 =
                               let uu____658 =
                                 let uu____661 = str v1  in [uu____661]  in
                               FStar_Pprint.rarrow :: uu____658  in
                             uu____654 :: uu____655  in
                           FStar_Pprint.concat uu____651) keywords
                   in
                [uu____635]  in
              FStar_Pprint.space :: uu____632  in
            uu____628 :: uu____629  in
          FStar_Pprint.concat uu____625  in
        FStar_Pprint.group uu____624
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____665 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____673 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____702::(e2,uu____704)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____727 -> false  in
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
    | FStar_Parser_AST.Construct (uu____739,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____750,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____771 = extract_from_list e2  in e1 :: uu____771
    | uu____774 ->
        let uu____775 =
          let uu____776 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____776  in
        failwith uu____775
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____783;
           FStar_Parser_AST.level = uu____784;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____786 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____792;
           FStar_Parser_AST.level = uu____793;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____795;
                                                        FStar_Parser_AST.level
                                                          = uu____796;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____798;
                                                   FStar_Parser_AST.level =
                                                     uu____799;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____801;
                FStar_Parser_AST.level = uu____802;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____804;
           FStar_Parser_AST.level = uu____805;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____807 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____815 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____816;
           FStar_Parser_AST.range = uu____817;
           FStar_Parser_AST.level = uu____818;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____819;
                                                        FStar_Parser_AST.range
                                                          = uu____820;
                                                        FStar_Parser_AST.level
                                                          = uu____821;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____823;
                                                   FStar_Parser_AST.level =
                                                     uu____824;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____825;
                FStar_Parser_AST.range = uu____826;
                FStar_Parser_AST.level = uu____827;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____829;
           FStar_Parser_AST.level = uu____830;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____832 = extract_from_ref_set e1  in
        let uu____835 = extract_from_ref_set e2  in
        FStar_List.append uu____832 uu____835
    | uu____838 ->
        let uu____839 =
          let uu____840 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____840  in
        failwith uu____839
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____846 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____846
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____850 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____850
  
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
      | uu____917 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____931 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____935 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____939 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___50_957  ->
    match uu___50_957 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___51_974  ->
      match uu___51_974 with
      | FStar_Util.Inl c ->
          let uu____983 = FStar_String.get s (Prims.parse_int "0")  in
          uu____983 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____991 .
    Prims.string ->
      ('Auu____991,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1010  ->
      match uu____1010 with
      | (assoc_levels,tokens) ->
          let uu____1038 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1038 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1064 .
    Prims.unit ->
      (associativity,('Auu____1064,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1075  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1091 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1091) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1103  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1138 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1138) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1150  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1178 .
    Prims.unit ->
      (associativity,('Auu____1178,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1189  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1205 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1205) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1217  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1245 .
    Prims.unit ->
      (associativity,('Auu____1245,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1256  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1272 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1272) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1284  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1305 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1305) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1317  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1352 .
    Prims.unit ->
      (associativity,('Auu____1352,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1363  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1379 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1379) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1391  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1412 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1412) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1424  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1445 .
    Prims.unit ->
      (associativity,('Auu____1445,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1456  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1472 .
    Prims.unit ->
      (associativity,('Auu____1472,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1483  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1499 .
    Prims.unit ->
      (associativity,('Auu____1499,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1510  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___52_1717 =
    match uu___52_1717 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1757  ->
         match uu____1757 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1837 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1837 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1887) ->
          assoc_levels
      | uu____1931 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1966 .
    ('Auu____1966,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2026 =
        FStar_List.tryFind
          (fun uu____2066  ->
             match uu____2066 with
             | (uu____2084,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2026 with
      | FStar_Pervasives_Native.Some ((uu____2126,l1,uu____2128),uu____2129)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2184 =
            let uu____2185 =
              let uu____2186 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2186  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2185
             in
          failwith uu____2184
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2220 = assign_levels level_associativity_spec op  in
    match uu____2220 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2244 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2244) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2258  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2339 =
      let uu____2353 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2353 (operatorInfix0ad12 ())  in
    uu____2339 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2466 =
      let uu____2480 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2480 opinfix34  in
    uu____2466 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2546 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2546
    then (Prims.parse_int "1")
    else
      (let uu____2548 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2548
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2554 . FStar_Ident.ident -> 'Auu____2554 Prims.list -> Prims.bool =
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
      | uu____2567 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2601 .
    ('Auu____2601 -> FStar_Pprint.document) ->
      'Auu____2601 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2633 = FStar_ST.op_Bang comment_stack  in
          match uu____2633 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2692 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2692
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2729 =
                    let uu____2730 =
                      let uu____2731 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2731
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2730  in
                  comments_before_pos uu____2729 print_pos lookahead_pos))
              else
                (let uu____2733 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2733))
           in
        let uu____2734 =
          let uu____2739 =
            let uu____2740 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2740  in
          let uu____2741 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2739 uu____2741  in
        match uu____2734 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2747 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2747
              else comments  in
            let uu____2753 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2753
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2766 = FStar_ST.op_Bang comment_stack  in
          match uu____2766 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2850 =
                    let uu____2851 =
                      let uu____2852 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2852  in
                    uu____2851 - lbegin  in
                  max k uu____2850  in
                let doc2 =
                  let uu____2854 =
                    let uu____2855 =
                      FStar_Pprint.repeat lnum FStar_Pprint.hardline  in
                    let uu____2856 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2855 uu____2856  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2854  in
                let uu____2857 =
                  let uu____2858 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2858  in
                place_comments_until_pos (Prims.parse_int "1") uu____2857
                  pos_end doc2))
          | uu____2859 ->
              let lnum =
                let uu____2867 =
                  let uu____2868 = FStar_Range.line_of_pos pos_end  in
                  uu____2868 - lbegin  in
                max (Prims.parse_int "1") uu____2867  in
              let uu____2869 = FStar_Pprint.repeat lnum FStar_Pprint.hardline
                 in
              FStar_Pprint.op_Hat_Hat doc1 uu____2869
  
let separate_map_with_comments :
  'Auu____2876 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2876 -> FStar_Pprint.document) ->
          'Auu____2876 Prims.list ->
            ('Auu____2876 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2924 x =
              match uu____2924 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2938 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2938 doc1
                     in
                  let uu____2939 =
                    let uu____2940 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2940  in
                  let uu____2941 =
                    let uu____2942 =
                      let uu____2943 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2943  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2942  in
                  (uu____2939, uu____2941)
               in
            let uu____2944 =
              let uu____2951 = FStar_List.hd xs  in
              let uu____2952 = FStar_List.tl xs  in (uu____2951, uu____2952)
               in
            match uu____2944 with
            | (x,xs1) ->
                let init1 =
                  let uu____2968 =
                    let uu____2969 =
                      let uu____2970 = extract_range x  in
                      FStar_Range.end_of_range uu____2970  in
                    FStar_Range.line_of_pos uu____2969  in
                  let uu____2971 =
                    let uu____2972 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2972  in
                  (uu____2968, uu____2971)  in
                let uu____2973 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2973
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let uu____3369 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3370 =
      let uu____3371 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3372 =
        let uu____3373 = p_qualifiers d.FStar_Parser_AST.quals  in
        let uu____3374 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat uu____3373 uu____3374  in
      FStar_Pprint.op_Hat_Hat uu____3371 uu____3372  in
    FStar_Pprint.op_Hat_Hat uu____3369 uu____3370

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3376 ->
        let uu____3377 =
          let uu____3378 =
            let uu____3381 =
              let uu____3382 = str "@ "  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3382  in
            let uu____3383 =
              let uu____3386 =
                let uu____3387 =
                  let uu____3388 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3388  in
                FStar_Pprint.align uu____3387  in
              [uu____3386; FStar_Pprint.rbracket]  in
            uu____3381 :: uu____3383  in
          FStar_Pprint.flow FStar_Pprint.empty uu____3378  in
        FStar_Pprint.op_Hat_Hat uu____3377 FStar_Pprint.hardline

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3391  ->
    match uu____3391 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3425 =
                match uu____3425 with
                | (kwd,arg) ->
                    let uu____3432 = str "@"  in
                    let uu____3433 =
                      let uu____3434 = str kwd  in
                      let uu____3435 =
                        let uu____3436 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3436
                         in
                      FStar_Pprint.op_Hat_Hat uu____3434 uu____3435  in
                    FStar_Pprint.op_Hat_Hat uu____3432 uu____3433
                 in
              let uu____3437 =
                let uu____3438 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3438 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3437
           in
        let uu____3443 =
          let uu____3444 =
            let uu____3445 =
              let uu____3446 =
                let uu____3447 = str doc1  in
                let uu____3448 =
                  let uu____3449 =
                    let uu____3450 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3450  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3449  in
                FStar_Pprint.op_Hat_Hat uu____3447 uu____3448  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3446  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3445  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3444  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3443

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3454 =
          let uu____3455 = str "val"  in
          let uu____3456 =
            let uu____3457 =
              let uu____3458 = p_lident lid  in
              let uu____3459 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3458 uu____3459  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3457  in
          FStar_Pprint.op_Hat_Hat uu____3455 uu____3456  in
        let uu____3460 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3454 uu____3460
    | FStar_Parser_AST.TopLevelLet (uu____3461,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3486 =
               let uu____3487 = str "let"  in
               let uu____3488 = p_letlhs lb  in
               FStar_Pprint.op_Hat_Slash_Hat uu____3487 uu____3488  in
             FStar_Pprint.group uu____3486) lbs
    | uu____3489 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3492 =
          let uu____3493 = str "open"  in
          let uu____3494 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3493 uu____3494  in
        FStar_Pprint.group uu____3492
    | FStar_Parser_AST.Include uid ->
        let uu____3496 =
          let uu____3497 = str "include"  in
          let uu____3498 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3497 uu____3498  in
        FStar_Pprint.group uu____3496
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3501 =
          let uu____3502 = str "module"  in
          let uu____3503 =
            let uu____3504 =
              let uu____3505 = p_uident uid1  in
              let uu____3506 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3505 uu____3506  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3504  in
          FStar_Pprint.op_Hat_Hat uu____3502 uu____3503  in
        let uu____3507 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3501 uu____3507
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3509 =
          let uu____3510 = str "module"  in
          let uu____3511 =
            let uu____3512 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3512  in
          FStar_Pprint.op_Hat_Hat uu____3510 uu____3511  in
        FStar_Pprint.group uu____3509
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3545 = str "effect"  in
          let uu____3546 =
            let uu____3547 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3547  in
          FStar_Pprint.op_Hat_Hat uu____3545 uu____3546  in
        let uu____3548 =
          let uu____3549 = p_typars tpars []  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3549 FStar_Pprint.equals
           in
        let uu____3550 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3548 uu____3550
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3568 =
          let uu____3569 = str "type"  in
          let uu____3570 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3569 uu____3570  in
        let uu____3583 =
          let uu____3584 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3622 =
                    let uu____3623 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3623 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3622)) uu____3584
           in
        FStar_Pprint.op_Hat_Hat uu____3568 uu____3583
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3639 = str "let"  in
          let uu____3640 =
            let uu____3641 = p_letqualifier q  in
            FStar_Pprint.op_Hat_Hat uu____3641 FStar_Pprint.space  in
          FStar_Pprint.op_Hat_Hat uu____3639 uu____3640  in
        let uu____3642 =
          let uu____3643 = str "and"  in
          FStar_Pprint.op_Hat_Hat uu____3643 FStar_Pprint.space  in
        separate_map_with_comments let_doc uu____3642 p_letbinding lbs
          (fun uu____3651  ->
             match uu____3651 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3660 =
          let uu____3661 = str "val"  in
          let uu____3662 =
            let uu____3663 =
              let uu____3664 = p_lident lid  in
              let uu____3665 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3664 uu____3665  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3663  in
          FStar_Pprint.op_Hat_Hat uu____3661 uu____3662  in
        let uu____3666 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3660 uu____3666
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3670 =
            let uu____3671 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3671 FStar_Util.is_upper  in
          if uu____3670
          then FStar_Pprint.empty
          else
            (let uu____3673 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3673 FStar_Pprint.space)
           in
        let uu____3674 =
          let uu____3675 =
            let uu____3676 = p_ident id1  in
            let uu____3677 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
               in
            FStar_Pprint.op_Hat_Hat uu____3676 uu____3677  in
          FStar_Pprint.op_Hat_Hat decl_keyword uu____3675  in
        let uu____3678 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3674 uu____3678
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3685 = str "exception"  in
        let uu____3686 =
          let uu____3687 =
            let uu____3688 = p_uident uid  in
            let uu____3689 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3693 =
                     let uu____3694 = str "of"  in
                     let uu____3695 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3694 uu____3695  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3693) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3688 uu____3689  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3687  in
        FStar_Pprint.op_Hat_Hat uu____3685 uu____3686
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3697 = str "new_effect"  in
        let uu____3698 =
          let uu____3699 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3699  in
        FStar_Pprint.op_Hat_Hat uu____3697 uu____3698
    | FStar_Parser_AST.SubEffect se ->
        let uu____3701 = str "sub_effect"  in
        let uu____3702 =
          let uu____3703 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3703  in
        FStar_Pprint.op_Hat_Hat uu____3701 uu____3702
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3706 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3706 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3707 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3708) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3726 = str "%splice"  in
        let uu____3727 =
          let uu____3728 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3728  in
        FStar_Pprint.op_Hat_Hat uu____3726 uu____3727

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___53_3729  ->
    match uu___53_3729 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3731 = str "#set-options"  in
        let uu____3732 =
          let uu____3733 =
            let uu____3734 = str s  in FStar_Pprint.dquotes uu____3734  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3733  in
        FStar_Pprint.op_Hat_Hat uu____3731 uu____3732
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3738 = str "#reset-options"  in
        let uu____3739 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3743 =
                 let uu____3744 = str s  in FStar_Pprint.dquotes uu____3744
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3743) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3738 uu____3739
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  = fun bs  -> fun suffix  -> p_binders true bs suffix

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____3772  ->
      match uu____3772 with
      | (typedecl,fsdoc_opt) ->
          let uu____3785 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3785 with
           | (decl,body) ->
               let uu____3800 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3800)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___54_3802  ->
      match uu___54_3802 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3829 = FStar_Pprint.empty  in
          let uu____3830 = p_typeDeclPrefix pre lid bs typ_opt  in
          (uu____3830, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3848 =
            let uu____3849 = p_typ false false t  in jump2 uu____3849  in
          let uu____3850 = p_typeDeclPrefix pre lid bs typ_opt  in
          (uu____3850, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____3899 =
            match uu____3899 with
            | (lid1,t,doc_opt) ->
                let uu____3915 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____3915
             in
          let p_fields uu____3929 =
            let uu____3930 =
              let uu____3931 =
                let uu____3932 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____3932 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____3931  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3930  in
          let uu____3941 = p_typeDeclPrefix pre lid bs typ_opt  in
          (uu____3941, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____3999 =
            match uu____3999 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4025 =
                    let uu____4026 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4026  in
                  FStar_Range.extend_to_end_of_line uu____4025  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4050 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4063 = p_typeDeclPrefix pre lid bs typ_opt  in
          (uu____4063,
            ((fun uu____4068  ->
                let uu____4069 = datacon_doc ()  in jump2 uu____4069)))

and (p_typeDeclPrefix :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Ident.ident ->
      FStar_Parser_AST.binder Prims.list ->
        FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
          FStar_Pprint.document)
  =
  fun uu____4070  ->
    fun lid  ->
      fun bs  ->
        fun typ_opt  ->
          match uu____4070 with
          | (kw,fsdoc_opt) ->
              if bs = []
              then
                (match fsdoc_opt with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4092 =
                       let uu____4093 =
                         let uu____4094 =
                           let uu____4095 = p_ident lid  in
                           FStar_Pprint.op_Hat_Slash_Hat uu____4095
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.group uu____4094  in
                       FStar_Pprint.op_Hat_Slash_Hat kw uu____4093  in
                     FStar_Pprint.group uu____4092
                 | FStar_Pervasives_Native.Some fsdoc ->
                     let uu____4097 =
                       let uu____4100 =
                         let uu____4103 = p_fsdoc fsdoc  in
                         let uu____4104 =
                           let uu____4107 =
                             let uu____4108 =
                               let uu____4109 = p_ident lid  in
                               FStar_Pprint.op_Hat_Slash_Hat uu____4109
                                 FStar_Pprint.equals
                                in
                             FStar_Pprint.group uu____4108  in
                           [uu____4107]  in
                         uu____4103 :: uu____4104  in
                       kw :: uu____4100  in
                     FStar_Pprint.separate FStar_Pprint.hardline uu____4097)
              else
                (let binders_doc =
                   let uu____4112 =
                     let uu____4115 =
                       FStar_Pprint.optional
                         (fun t  ->
                            let uu____4119 =
                              let uu____4120 = p_typ false false t  in
                              FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                uu____4120
                               in
                            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon
                              uu____4119) typ_opt
                        in
                     [uu____4115; FStar_Pprint.equals]  in
                   p_typars bs uu____4112  in
                 match fsdoc_opt with
                 | FStar_Pervasives_Native.None  ->
                     let uu____4121 =
                       let uu____4122 =
                         let uu____4123 =
                           let uu____4124 =
                             let uu____4125 = p_ident lid  in
                             FStar_Pprint.op_Hat_Slash_Hat kw uu____4125  in
                           FStar_Pprint.group uu____4124  in
                         FStar_Pprint.op_Hat_Slash_Hat uu____4123 binders_doc
                          in
                       FStar_All.pipe_left
                         (FStar_Pprint.hang (Prims.parse_int "2")) uu____4122
                        in
                     FStar_Pprint.group uu____4121
                 | FStar_Pervasives_Native.Some fsdoc ->
                     let uu____4127 =
                       let uu____4130 =
                         let uu____4133 = p_fsdoc fsdoc  in
                         let uu____4134 =
                           let uu____4137 =
                             let uu____4138 =
                               let uu____4139 =
                                 let uu____4140 = p_ident lid  in
                                 FStar_Pprint.op_Hat_Slash_Hat uu____4140
                                   binders_doc
                                  in
                               FStar_Pprint.hang (Prims.parse_int "2")
                                 uu____4139
                                in
                             FStar_Pprint.group uu____4138  in
                           [uu____4137]  in
                         uu____4133 :: uu____4134  in
                       kw :: uu____4130  in
                     FStar_Pprint.separate FStar_Pprint.hardline uu____4127)

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4142  ->
      match uu____4142 with
      | (lid,t,doc_opt) ->
          let uu____4158 =
            let uu____4159 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4160 =
              let uu____4161 = p_lident lid  in
              let uu____4162 =
                let uu____4163 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4163  in
              FStar_Pprint.op_Hat_Hat uu____4161 uu____4162  in
            FStar_Pprint.op_Hat_Hat uu____4159 uu____4160  in
          FStar_Pprint.group uu____4158

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4164  ->
    match uu____4164 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4192 =
            let uu____4193 =
              let uu____4194 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4194  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4193  in
          FStar_Pprint.group uu____4192  in
        let uu____4195 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4196 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4201 =
                 let uu____4202 =
                   let uu____4203 =
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space sep  in
                   FStar_Pprint.op_Hat_Hat uid_doc uu____4203  in
                 FStar_Pprint.group uu____4202  in
               let uu____4204 = p_typ false false t  in
               op_Hat_Slash_Plus_Hat uu____4201 uu____4204) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4195 uu____4196

and (p_letlhs :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4205  ->
    match uu____4205 with
    | (pat,uu____4211) ->
        let uu____4212 =
          match pat.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.None )) ->
              let uu____4231 =
                let uu____4232 =
                  let uu____4233 =
                    let uu____4234 =
                      let uu____4235 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4235
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4234  in
                  FStar_Pprint.group uu____4233  in
                FStar_Pprint.op_Hat_Hat break1 uu____4232  in
              (pat1, uu____4231)
          | FStar_Parser_AST.PatAscribed
              (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
              let uu____4247 =
                let uu____4248 =
                  let uu____4249 =
                    let uu____4250 =
                      let uu____4251 =
                        let uu____4252 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4252
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4251
                       in
                    FStar_Pprint.group uu____4250  in
                  let uu____4253 =
                    let uu____4254 =
                      let uu____4255 = str "by"  in
                      let uu____4256 =
                        let uu____4257 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4257
                         in
                      FStar_Pprint.op_Hat_Hat uu____4255 uu____4256  in
                    FStar_Pprint.group uu____4254  in
                  FStar_Pprint.op_Hat_Hat uu____4249 uu____4253  in
                FStar_Pprint.op_Hat_Hat break1 uu____4248  in
              (pat1, uu____4247)
          | uu____4258 -> (pat, FStar_Pprint.empty)  in
        (match uu____4212 with
         | (pat1,ascr_doc) ->
             (match pat1.FStar_Parser_AST.pat with
              | FStar_Parser_AST.PatApp
                  ({
                     FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                       (x,uu____4262);
                     FStar_Parser_AST.prange = uu____4263;_},pats)
                  ->
                  let uu____4273 =
                    let uu____4274 = p_lident x  in
                    let uu____4275 =
                      let uu____4276 =
                        separate_map_or_flow break1 p_atomicPattern pats  in
                      FStar_Pprint.op_Hat_Hat uu____4276 ascr_doc  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4274 uu____4275  in
                  FStar_Pprint.group uu____4273
              | uu____4277 ->
                  let uu____4278 =
                    let uu____4279 = p_tuplePattern pat1  in
                    FStar_Pprint.op_Hat_Hat uu____4279 ascr_doc  in
                  FStar_Pprint.group uu____4278))

and (p_letbinding :
  (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____4280  ->
    match uu____4280 with
    | (pat,e) ->
        let pat_doc = p_letlhs (pat, e)  in
        let uu____4288 =
          let uu____4289 =
            FStar_Pprint.op_Hat_Slash_Hat pat_doc FStar_Pprint.equals  in
          FStar_Pprint.group uu____4289  in
        let uu____4290 = p_term false false e  in
        prefix2 uu____4288 uu____4290

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___55_4291  ->
    match uu___55_4291 with
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
        let uu____4316 = p_uident uid  in
        let uu____4317 = p_binders true bs []  in
        let uu____4318 =
          let uu____4319 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4319  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4316 uu____4317 uu____4318

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
          let uu____4328 =
            let uu____4329 =
              let uu____4330 =
                let uu____4331 = p_uident uid  in
                let uu____4332 = p_binders true bs []  in
                let uu____4333 =
                  let uu____4334 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4334  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4331 uu____4332 uu____4333
                 in
              FStar_Pprint.group uu____4330  in
            let uu____4335 =
              let uu____4336 = str "with"  in
              let uu____4337 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4336 uu____4337  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4329 uu____4335  in
          braces_with_nesting uu____4328

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
          let uu____4368 =
            let uu____4369 = p_lident lid  in
            let uu____4370 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4369 uu____4370  in
          let uu____4371 = p_simpleTerm ps false e  in
          prefix2 uu____4368 uu____4371
      | uu____4372 ->
          let uu____4373 =
            let uu____4374 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4374
             in
          failwith uu____4373

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4432 =
        match uu____4432 with
        | (kwd,t) ->
            let uu____4439 =
              let uu____4440 = str kwd  in
              let uu____4441 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4440 uu____4441  in
            let uu____4442 = p_simpleTerm ps false t  in
            prefix2 uu____4439 uu____4442
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4447 =
      let uu____4448 =
        let uu____4449 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4450 =
          let uu____4451 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4451  in
        FStar_Pprint.op_Hat_Hat uu____4449 uu____4450  in
      let uu____4452 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4448 uu____4452  in
    let uu____4453 =
      let uu____4454 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4454  in
    FStar_Pprint.op_Hat_Hat uu____4447 uu____4453

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___56_4455  ->
    match uu___56_4455 with
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
    | uu____4457 ->
        let uu____4458 =
          let uu____4459 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4459  in
        FStar_Pprint.op_Hat_Slash_Hat uu____4458 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___57_4462  ->
    match uu___57_4462 with
    | FStar_Parser_AST.Rec  ->
        let uu____4463 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4463
    | FStar_Parser_AST.Mutable  ->
        let uu____4464 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4464
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___58_4465  ->
    match uu___58_4465 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4470 =
          let uu____4471 =
            let uu____4472 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4472  in
          FStar_Pprint.separate_map uu____4471 p_tuplePattern pats  in
        FStar_Pprint.group uu____4470
    | uu____4473 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4480 =
          let uu____4481 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4481 p_constructorPattern pats  in
        FStar_Pprint.group uu____4480
    | uu____4482 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4485;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4490 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4491 = p_constructorPattern hd1  in
        let uu____4492 = p_constructorPattern tl1  in
        infix0 uu____4490 uu____4491 uu____4492
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4494;_},pats)
        ->
        let uu____4500 = p_quident uid  in
        let uu____4501 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4500 uu____4501
    | uu____4502 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4518;
               FStar_Parser_AST.blevel = uu____4519;
               FStar_Parser_AST.aqual = uu____4520;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4526 =
               let uu____4527 = p_ident lid  in
               p_refinement aqual uu____4527 t1 phi  in
             soft_parens_with_nesting uu____4526
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4529;
               FStar_Parser_AST.blevel = uu____4530;
               FStar_Parser_AST.aqual = uu____4531;_},phi))
             ->
             let uu____4533 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4533
         | uu____4534 ->
             let uu____4539 =
               let uu____4540 = p_tuplePattern pat  in
               let uu____4541 =
                 let uu____4542 = FStar_Pprint.break_ (Prims.parse_int "0")
                    in
                 let uu____4543 =
                   let uu____4544 = p_tmEqNoRefinement t  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4544  in
                 FStar_Pprint.op_Hat_Hat uu____4542 uu____4543  in
               FStar_Pprint.op_Hat_Hat uu____4540 uu____4541  in
             soft_parens_with_nesting uu____4539)
    | FStar_Parser_AST.PatList pats ->
        let uu____4548 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4548 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4563 =
          match uu____4563 with
          | (lid,pat) ->
              let uu____4570 = p_qlident lid  in
              let uu____4571 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4570 uu____4571
           in
        let uu____4572 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4572
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4582 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4583 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4584 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4582 uu____4583 uu____4584
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4595 =
          let uu____4596 =
            let uu____4597 = str (FStar_Ident.text_of_id op)  in
            let uu____4598 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4597 uu____4598  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4596  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4595
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4606 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4607 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4606 uu____4607
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4609 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4612;
           FStar_Parser_AST.prange = uu____4613;_},uu____4614)
        ->
        let uu____4619 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4619
    | FStar_Parser_AST.PatTuple (uu____4620,false ) ->
        let uu____4625 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4625
    | uu____4626 ->
        let uu____4627 =
          let uu____4628 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4628  in
        failwith uu____4627

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4632 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4633 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4632 uu____4633
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4640;
                   FStar_Parser_AST.blevel = uu____4641;
                   FStar_Parser_AST.aqual = uu____4642;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4644 = p_ident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4644 t1 phi
            | uu____4645 ->
                let uu____4646 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4647 =
                  let uu____4648 = p_lident lid  in
                  let uu____4649 =
                    let uu____4650 =
                      let uu____4651 =
                        FStar_Pprint.break_ (Prims.parse_int "1")  in
                      let uu____4652 = p_tmFormula t  in
                      FStar_Pprint.op_Hat_Hat uu____4651 uu____4652  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4650  in
                  FStar_Pprint.op_Hat_Hat uu____4648 uu____4649  in
                FStar_Pprint.op_Hat_Hat uu____4646 uu____4647
             in
          if is_atomic
          then
            let uu____4653 =
              let uu____4654 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4654  in
            FStar_Pprint.group uu____4653
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4656 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4663;
                  FStar_Parser_AST.blevel = uu____4664;
                  FStar_Parser_AST.aqual = uu____4665;_},phi)
               ->
               if is_atomic
               then
                 let uu____4667 =
                   let uu____4668 =
                     let uu____4669 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4669 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4668  in
                 FStar_Pprint.group uu____4667
               else
                 (let uu____4671 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4671)
           | uu____4672 -> if is_atomic then p_atomicTerm t else p_appTerm t)

and (p_refinement :
  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Pprint.document ->
      FStar_Parser_AST.term -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun aqual_opt  ->
    fun binder  ->
      fun t  ->
        fun phi  ->
          let is_t_atomic =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Construct uu____4681 -> false
            | FStar_Parser_AST.App uu____4692 -> false
            | FStar_Parser_AST.Op uu____4699 -> false
            | uu____4706 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let uu____4708 = FStar_Pprint.optional p_aqual aqual_opt  in
          let uu____4709 =
            let uu____4710 =
              let uu____4711 =
                let uu____4712 = p_appTerm t  in
                let uu____4713 =
                  let uu____4714 =
                    let uu____4715 =
                      let uu____4716 = soft_braces_with_nesting_tight phi1
                         in
                      let uu____4717 = soft_braces_with_nesting phi1  in
                      FStar_Pprint.ifflat uu____4716 uu____4717  in
                    FStar_Pprint.group uu____4715  in
                  FStar_Pprint.op_Hat_Hat
                    (if is_t_atomic then FStar_Pprint.empty else break1)
                    uu____4714
                   in
                FStar_Pprint.op_Hat_Hat uu____4712 uu____4713  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4711  in
            FStar_Pprint.op_Hat_Hat binder uu____4710  in
          FStar_Pprint.op_Hat_Hat uu____4708 uu____4709

and (p_binders :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list ->
      FStar_Pprint.document Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      fun suffix  ->
        let suffix1 =
          FStar_List.filter (fun x  -> x <> FStar_Pprint.empty) suffix  in
        let uu____4731 =
          let uu____4734 = FStar_List.map (p_binder is_atomic) bs  in
          FStar_List.append uu____4734 suffix1  in
        FStar_All.pipe_left (separate_or_flow break1) uu____4731

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
            let uu____4757 =
              let uu____4758 =
                let uu____4759 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4759 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4758  in
            let uu____4760 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4757 uu____4760
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4764 =
              let uu____4765 =
                let uu____4766 =
                  let uu____4767 = p_lident x  in
                  let uu____4768 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4767 uu____4768  in
                let uu____4769 =
                  let uu____4770 = p_noSeqTerm true false e1  in
                  let uu____4771 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4770 uu____4771  in
                op_Hat_Slash_Plus_Hat uu____4766 uu____4769  in
              FStar_Pprint.group uu____4765  in
            let uu____4772 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4764 uu____4772
        | uu____4773 ->
            let uu____4774 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4774

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
            let uu____4785 =
              let uu____4786 = p_tmIff e1  in
              let uu____4787 =
                let uu____4788 =
                  let uu____4789 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4789
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4788  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4786 uu____4787  in
            FStar_Pprint.group uu____4785
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4795 =
              let uu____4796 = p_tmIff e1  in
              let uu____4797 =
                let uu____4798 =
                  let uu____4799 =
                    let uu____4800 = p_typ false false t  in
                    let uu____4801 =
                      let uu____4802 = str "by"  in
                      let uu____4803 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4802 uu____4803  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4800 uu____4801  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4799
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4798  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4796 uu____4797  in
            FStar_Pprint.group uu____4795
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4804;_},e1::e2::e3::[])
            ->
            let uu____4810 =
              let uu____4811 =
                let uu____4812 =
                  let uu____4813 = p_atomicTermNotQUident e1  in
                  let uu____4814 =
                    let uu____4815 =
                      let uu____4816 =
                        let uu____4817 = p_term false false e2  in
                        soft_parens_with_nesting uu____4817  in
                      let uu____4818 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4816 uu____4818  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4815  in
                  FStar_Pprint.op_Hat_Hat uu____4813 uu____4814  in
                FStar_Pprint.group uu____4812  in
              let uu____4819 =
                let uu____4820 = p_noSeqTerm ps pb e3  in jump2 uu____4820
                 in
              FStar_Pprint.op_Hat_Hat uu____4811 uu____4819  in
            FStar_Pprint.group uu____4810
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4821;_},e1::e2::e3::[])
            ->
            let uu____4827 =
              let uu____4828 =
                let uu____4829 =
                  let uu____4830 = p_atomicTermNotQUident e1  in
                  let uu____4831 =
                    let uu____4832 =
                      let uu____4833 =
                        let uu____4834 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4834  in
                      let uu____4835 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4833 uu____4835  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4832  in
                  FStar_Pprint.op_Hat_Hat uu____4830 uu____4831  in
                FStar_Pprint.group uu____4829  in
              let uu____4836 =
                let uu____4837 = p_noSeqTerm ps pb e3  in jump2 uu____4837
                 in
              FStar_Pprint.op_Hat_Hat uu____4828 uu____4836  in
            FStar_Pprint.group uu____4827
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4847 =
              let uu____4848 = str "requires"  in
              let uu____4849 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4848 uu____4849  in
            FStar_Pprint.group uu____4847
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____4859 =
              let uu____4860 = str "ensures"  in
              let uu____4861 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4860 uu____4861  in
            FStar_Pprint.group uu____4859
        | FStar_Parser_AST.Attributes es ->
            let uu____4865 =
              let uu____4866 = str "attributes"  in
              let uu____4867 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4866 uu____4867  in
            FStar_Pprint.group uu____4865
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____4871 =
                let uu____4872 =
                  let uu____4873 = str "if"  in
                  let uu____4874 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____4873 uu____4874  in
                let uu____4875 =
                  let uu____4876 = str "then"  in
                  let uu____4877 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____4876 uu____4877  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4872 uu____4875  in
              FStar_Pprint.group uu____4871
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____4880,uu____4881,e31) when
                     is_unit e31 ->
                     let uu____4883 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____4883
                 | uu____4884 -> p_noSeqTerm false false e2  in
               let uu____4885 =
                 let uu____4886 =
                   let uu____4887 = str "if"  in
                   let uu____4888 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____4887 uu____4888  in
                 let uu____4889 =
                   let uu____4890 =
                     let uu____4891 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____4891 e2_doc  in
                   let uu____4892 =
                     let uu____4893 = str "else"  in
                     let uu____4894 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____4893 uu____4894  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____4890 uu____4892  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____4886 uu____4889  in
               FStar_Pprint.group uu____4885)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____4917 =
              let uu____4918 =
                let uu____4919 =
                  let uu____4920 = str "try"  in
                  let uu____4921 = p_noSeqTerm false false e1  in
                  prefix2 uu____4920 uu____4921  in
                let uu____4922 =
                  let uu____4923 = str "with"  in
                  let uu____4924 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____4923 uu____4924  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4919 uu____4922  in
              FStar_Pprint.group uu____4918  in
            let uu____4933 = paren_if (ps || pb)  in uu____4933 uu____4917
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____4958 =
              let uu____4959 =
                let uu____4960 =
                  let uu____4961 = str "match"  in
                  let uu____4962 = p_noSeqTerm false false e1  in
                  let uu____4963 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4961 uu____4962 uu____4963
                   in
                let uu____4964 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____4960 uu____4964  in
              FStar_Pprint.group uu____4959  in
            let uu____4973 = paren_if (ps || pb)  in uu____4973 uu____4958
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____4978 =
              let uu____4979 =
                let uu____4980 =
                  let uu____4981 = str "let open"  in
                  let uu____4982 = p_quident uid  in
                  let uu____4983 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____4981 uu____4982 uu____4983
                   in
                let uu____4984 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____4980 uu____4984  in
              FStar_Pprint.group uu____4979  in
            let uu____4985 = paren_if ps  in uu____4985 uu____4978
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5041 is_last =
              match uu____5041 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5074 =
                          let uu____5075 = str "let"  in
                          let uu____5076 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5075 uu____5076
                           in
                        FStar_Pprint.group uu____5074
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5077 -> str "and"  in
                  let doc_pat = p_letlhs (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5082 =
                    if is_last
                    then
                      let uu____5083 =
                        let uu____5084 =
                          FStar_Pprint.surround (Prims.parse_int "2")
                            (Prims.parse_int "1") doc_let_or_and doc_pat
                            FStar_Pprint.equals
                           in
                        let uu____5085 = str "in"  in
                        FStar_Pprint.surround (Prims.parse_int "2")
                          (Prims.parse_int "1") uu____5084 doc_expr
                          uu____5085
                         in
                      FStar_Pprint.group uu____5083
                    else
                      (let uu____5087 =
                         let uu____5088 =
                           FStar_Pprint.surround (Prims.parse_int "2")
                             (Prims.parse_int "1") doc_let_or_and doc_pat
                             FStar_Pprint.equals
                            in
                         FStar_Pprint.prefix (Prims.parse_int "2")
                           (Prims.parse_int "1") uu____5088 doc_expr
                          in
                       FStar_Pprint.group uu____5087)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5082
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5134 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5134
                     else
                       (let uu____5142 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5142)) lbs
               in
            let lbs_doc =
              let uu____5150 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5150  in
            let uu____5151 =
              let uu____5152 =
                let uu____5153 =
                  let uu____5154 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5154
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5153  in
              FStar_Pprint.group uu____5152  in
            let uu____5155 = paren_if ps  in uu____5155 uu____5151
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5160;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5163;
                                                             FStar_Parser_AST.level
                                                               = uu____5164;_})
            when matches_var maybe_x x ->
            let uu____5191 =
              let uu____5192 =
                let uu____5193 = str "function"  in
                let uu____5194 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5193 uu____5194  in
              FStar_Pprint.group uu____5192  in
            let uu____5203 = paren_if (ps || pb)  in uu____5203 uu____5191
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5207 =
              let uu____5208 = str "quote"  in
              let uu____5209 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5208 uu____5209  in
            FStar_Pprint.group uu____5207
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5211 =
              let uu____5212 = str "`"  in
              let uu____5213 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5212 uu____5213  in
            FStar_Pprint.group uu____5211
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5215 =
              let uu____5216 = str "%`"  in
              let uu____5217 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5216 uu____5217  in
            FStar_Pprint.group uu____5215
        | uu____5218 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_5219  ->
    match uu___59_5219 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5231 =
          let uu____5232 =
            let uu____5233 = str "[@"  in
            let uu____5234 =
              let uu____5235 =
                FStar_Pprint.separate_map break1 p_atomicTerm terms  in
              let uu____5236 = str "]"  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5235 uu____5236  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5233 uu____5234  in
          FStar_Pprint.group uu____5232  in
        FStar_Pprint.op_Hat_Hat uu____5231 break1

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
            let uu____5258 =
              let uu____5259 =
                let uu____5260 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5260 FStar_Pprint.space  in
              let uu____5261 = p_binders true bs []  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5259 uu____5261 FStar_Pprint.dot
               in
            let uu____5262 =
              let uu____5263 = p_trigger trigger  in
              let uu____5264 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5263 uu____5264  in
            prefix2 uu____5258 uu____5262
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let uu____5280 =
              let uu____5281 =
                let uu____5282 = p_quantifier e  in
                FStar_Pprint.op_Hat_Hat uu____5282 FStar_Pprint.space  in
              let uu____5283 = p_binders true bs []  in
              FStar_Pprint.soft_surround (Prims.parse_int "2")
                (Prims.parse_int "0") uu____5281 uu____5283 FStar_Pprint.dot
               in
            let uu____5284 =
              let uu____5285 = p_trigger trigger  in
              let uu____5286 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5285 uu____5286  in
            prefix2 uu____5280 uu____5284
        | uu____5287 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5289 -> str "forall"
    | FStar_Parser_AST.QExists uu____5302 -> str "exists"
    | uu____5315 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___60_5316  ->
    match uu___60_5316 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5328 =
          let uu____5329 =
            let uu____5330 = str "pattern"  in
            let uu____5331 =
              let uu____5332 =
                let uu____5333 = p_disjunctivePats pats  in jump2 uu____5333
                 in
              let uu____5334 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.rbrace break1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5332 uu____5334  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5330 uu____5331  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5329  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5328

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5340 = str "\\/"  in
    FStar_Pprint.separate_map uu____5340 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5346 =
      FStar_Pprint.separate_map FStar_Pprint.semi p_appTerm pats  in
    FStar_Pprint.group uu____5346

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5356 =
              let uu____5357 =
                let uu____5358 = str "fun"  in
                let uu____5359 =
                  let uu____5360 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5360
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5358 uu____5359  in
              let uu____5361 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5357 uu____5361  in
            let uu____5362 = paren_if ps  in uu____5362 uu____5356
        | uu____5365 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5369  ->
      match uu____5369 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5390 =
                    let uu____5391 =
                      let uu____5392 =
                        let uu____5393 = p_tuplePattern p  in
                        let uu____5394 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5393 uu____5394  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5392
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5391  in
                  FStar_Pprint.group uu____5390
              | FStar_Pervasives_Native.Some f ->
                  let uu____5396 =
                    let uu____5397 =
                      let uu____5398 =
                        let uu____5399 =
                          let uu____5400 =
                            let uu____5401 = p_tuplePattern p  in
                            let uu____5402 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5401
                              uu____5402
                             in
                          FStar_Pprint.group uu____5400  in
                        let uu____5403 =
                          let uu____5404 =
                            let uu____5407 = p_tmFormula f  in
                            [uu____5407; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5404  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5399 uu____5403
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5398
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5397  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5396
               in
            let uu____5408 =
              let uu____5409 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5409  in
            FStar_Pprint.group uu____5408  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5418 =
                      let uu____5419 =
                        let uu____5420 =
                          let uu____5421 =
                            let uu____5422 =
                              let uu____5423 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5423  in
                            FStar_Pprint.separate_map uu____5422
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5421
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5420
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5419  in
                    FStar_Pprint.group uu____5418
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5424 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5426;_},e1::e2::[])
        ->
        let uu____5431 = str "<==>"  in
        let uu____5432 = p_tmImplies e1  in
        let uu____5433 = p_tmIff e2  in
        infix0 uu____5431 uu____5432 uu____5433
    | uu____5434 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5436;_},e1::e2::[])
        ->
        let uu____5441 = str "==>"  in
        let uu____5442 = p_tmArrow p_tmFormula e1  in
        let uu____5443 = p_tmImplies e2  in
        infix0 uu____5441 uu____5442 uu____5443
    | uu____5444 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5455 =
            let uu____5456 =
              separate_map_or_flow FStar_Pprint.empty
                (fun b  ->
                   let uu____5461 = p_binder false b  in
                   let uu____5462 =
                     let uu____5463 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5463
                      in
                   FStar_Pprint.op_Hat_Hat uu____5461 uu____5462) bs
               in
            let uu____5464 = p_tmArrow p_Tm tgt  in
            FStar_Pprint.op_Hat_Hat uu____5456 uu____5464  in
          FStar_Pprint.group uu____5455
      | uu____5465 -> p_Tm e

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5468 =
        let uu____5469 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5469 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5468  in
    let disj =
      let uu____5471 =
        let uu____5472 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5472 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5471  in
    let formula = p_tmDisjunction e  in
    FStar_Pprint.flow_map disj
      (fun d  ->
         FStar_Pprint.flow_map conj (fun x  -> FStar_Pprint.group x) d)
      formula

and (p_tmDisjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5491;_},e1::e2::[])
        ->
        let uu____5496 = p_tmDisjunction e1  in
        let uu____5501 = let uu____5506 = p_tmConjunction e2  in [uu____5506]
           in
        FStar_List.append uu____5496 uu____5501
    | uu____5515 -> let uu____5516 = p_tmConjunction e  in [uu____5516]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5526;_},e1::e2::[])
        ->
        let uu____5531 = p_tmConjunction e1  in
        let uu____5534 = let uu____5537 = p_tmTuple e2  in [uu____5537]  in
        FStar_List.append uu____5531 uu____5534
    | uu____5538 -> let uu____5539 = p_tmTuple e  in [uu____5539]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5556 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5556
          (fun uu____5564  ->
             match uu____5564 with | (e1,uu____5570) -> p_tmEq e1) args
    | uu____5571 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5576 =
             let uu____5577 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5577  in
           FStar_Pprint.group uu____5576)

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
            let uu____5640 = levels op1  in
            (match uu____5640 with
             | (left1,mine,right1) ->
                 let uu____5650 =
                   let uu____5651 = FStar_All.pipe_left str op1  in
                   let uu____5652 = p_tmEqWith' p_X left1 e1  in
                   let uu____5653 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5651 uu____5652 uu____5653  in
                 paren_if_gt curr mine uu____5650)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5654;_},e1::e2::[])
            ->
            let uu____5659 =
              let uu____5660 = p_tmEqWith p_X e1  in
              let uu____5661 =
                let uu____5662 =
                  let uu____5663 =
                    let uu____5664 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5664  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5663  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5662  in
              FStar_Pprint.op_Hat_Hat uu____5660 uu____5661  in
            FStar_Pprint.group uu____5659
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5665;_},e1::[])
            ->
            let uu____5669 = levels "-"  in
            (match uu____5669 with
             | (left1,mine,right1) ->
                 let uu____5679 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5679)
        | uu____5680 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5751)::(e2,uu____5753)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5773 = is_list e  in Prims.op_Negation uu____5773)
            ->
            let op = "::"  in
            let uu____5775 = levels op  in
            (match uu____5775 with
             | (left1,mine,right1) ->
                 let uu____5785 =
                   let uu____5786 = str op  in
                   let uu____5787 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5788 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5786 uu____5787 uu____5788  in
                 paren_if_gt curr mine uu____5785)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____5796 = levels op  in
            (match uu____5796 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____5810 = p_binder false b  in
                   let uu____5811 =
                     let uu____5812 =
                       let uu____5813 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____5813 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5812
                      in
                   FStar_Pprint.op_Hat_Hat uu____5810 uu____5811  in
                 let uu____5814 =
                   let uu____5815 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____5816 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____5815 uu____5816  in
                 paren_if_gt curr mine uu____5814)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____5823 = levels op1  in
            (match uu____5823 with
             | (left1,mine,right1) ->
                 let uu____5833 =
                   let uu____5834 = str op1  in
                   let uu____5835 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____5836 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5834 uu____5835 uu____5836  in
                 paren_if_gt curr mine uu____5833)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____5855 =
              let uu____5856 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____5857 =
                let uu____5858 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____5858 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____5856 uu____5857  in
            braces_with_nesting uu____5855
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____5863;_},e1::[])
            ->
            let uu____5867 =
              let uu____5868 = str "~"  in
              let uu____5869 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____5868 uu____5869  in
            FStar_Pprint.group uu____5867
        | uu____5870 -> p_X e

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
        let uu____5877 =
          let uu____5878 = p_lidentOrUnderscore lid  in
          let uu____5879 =
            let uu____5880 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____5880  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5878 uu____5879  in
        FStar_Pprint.group uu____5877
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____5883 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____5885 = p_appTerm e  in
    let uu____5886 =
      let uu____5887 =
        let uu____5888 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____5888 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5887  in
    FStar_Pprint.op_Hat_Hat uu____5885 uu____5886

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____5893 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____5893 t phi
      | FStar_Parser_AST.TAnnotated uu____5894 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____5899 ->
          let uu____5900 =
            let uu____5901 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5901
             in
          failwith uu____5900
      | FStar_Parser_AST.TVariable uu____5902 ->
          let uu____5903 =
            let uu____5904 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5904
             in
          failwith uu____5903
      | FStar_Parser_AST.NoName uu____5905 ->
          let uu____5906 =
            let uu____5907 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____5907
             in
          failwith uu____5906

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____5909  ->
      match uu____5909 with
      | (lid,e) ->
          let uu____5916 =
            let uu____5917 = p_qlident lid  in
            let uu____5918 =
              let uu____5919 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____5919
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____5917 uu____5918  in
          FStar_Pprint.group uu____5916

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____5921 when is_general_application e ->
        let uu____5928 = head_and_args e  in
        (match uu____5928 with
         | (head1,args) ->
             let uu____5953 =
               let uu____5964 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____5964
               then
                 let uu____5994 =
                   FStar_Util.take
                     (fun uu____6018  ->
                        match uu____6018 with
                        | (uu____6023,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____5994 with
                 | (fs_typ_args,args1) ->
                     let uu____6061 =
                       let uu____6062 = p_indexingTerm head1  in
                       let uu____6063 =
                         let uu____6064 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6064 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6062 uu____6063  in
                     (uu____6061, args1)
               else
                 (let uu____6076 = p_indexingTerm head1  in
                  (uu____6076, args))
                in
             (match uu____5953 with
              | (head_doc,args1) ->
                  let uu____6097 =
                    let uu____6098 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6098 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6097))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6118 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6118)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6136 =
               let uu____6137 = p_quident lid  in
               let uu____6138 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6137 uu____6138  in
             FStar_Pprint.group uu____6136
         | hd1::tl1 ->
             let uu____6155 =
               let uu____6156 =
                 let uu____6157 =
                   let uu____6158 = p_quident lid  in
                   let uu____6159 = p_argTerm hd1  in
                   prefix2 uu____6158 uu____6159  in
                 FStar_Pprint.group uu____6157  in
               let uu____6160 =
                 let uu____6161 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6161  in
               FStar_Pprint.op_Hat_Hat uu____6156 uu____6160  in
             FStar_Pprint.group uu____6155)
    | uu____6166 -> p_indexingTerm e

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
         (let uu____6175 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6175 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6177 = str "#"  in
        let uu____6178 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6177 uu____6178
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6180  ->
    match uu____6180 with | (e,uu____6186) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6191;_},e1::e2::[])
          ->
          let uu____6196 =
            let uu____6197 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6198 =
              let uu____6199 =
                let uu____6200 = p_term false false e2  in
                soft_parens_with_nesting uu____6200  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6199  in
            FStar_Pprint.op_Hat_Hat uu____6197 uu____6198  in
          FStar_Pprint.group uu____6196
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6201;_},e1::e2::[])
          ->
          let uu____6206 =
            let uu____6207 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6208 =
              let uu____6209 =
                let uu____6210 = p_term false false e2  in
                soft_brackets_with_nesting uu____6210  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6209  in
            FStar_Pprint.op_Hat_Hat uu____6207 uu____6208  in
          FStar_Pprint.group uu____6206
      | uu____6211 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6216 = p_quident lid  in
        let uu____6217 =
          let uu____6218 =
            let uu____6219 = p_term false false e1  in
            soft_parens_with_nesting uu____6219  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6218  in
        FStar_Pprint.op_Hat_Hat uu____6216 uu____6217
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6225 = str (FStar_Ident.text_of_id op)  in
        let uu____6226 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6225 uu____6226
    | uu____6227 -> p_atomicTermNotQUident e

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
         | uu____6234 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6241 = str (FStar_Ident.text_of_id op)  in
        let uu____6242 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6241 uu____6242
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6246 =
          let uu____6247 =
            let uu____6248 = str (FStar_Ident.text_of_id op)  in
            let uu____6249 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6248 uu____6249  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6247  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6246
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6264 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6265 =
          let uu____6266 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6267 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6266 p_tmEq uu____6267  in
        let uu____6274 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6264 uu____6265 uu____6274
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6277 =
          let uu____6278 = p_atomicTermNotQUident e1  in
          let uu____6279 =
            let uu____6280 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6280  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6278 uu____6279
           in
        FStar_Pprint.group uu____6277
    | uu____6281 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6286 = p_quident constr_lid  in
        let uu____6287 =
          let uu____6288 =
            let uu____6289 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6289  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6288  in
        FStar_Pprint.op_Hat_Hat uu____6286 uu____6287
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6291 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6291 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6293 = p_term false false e1  in
        soft_parens_with_nesting uu____6293
    | uu____6294 when is_array e ->
        let es = extract_from_list e  in
        let uu____6298 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6299 =
          let uu____6300 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6300
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6303 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6298 uu____6299 uu____6303
    | uu____6304 when is_list e ->
        let uu____6305 =
          let uu____6306 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6307 = extract_from_list e  in
          separate_map_or_flow_last uu____6306
            (fun ps  -> p_noSeqTerm ps false) uu____6307
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6305 FStar_Pprint.rbracket
    | uu____6312 when is_lex_list e ->
        let uu____6313 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6314 =
          let uu____6315 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6316 = extract_from_list e  in
          separate_map_or_flow_last uu____6315
            (fun ps  -> p_noSeqTerm ps false) uu____6316
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6313 uu____6314 FStar_Pprint.rbracket
    | uu____6321 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6325 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6326 =
          let uu____6327 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6327 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6325 uu____6326 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6331 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6332 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6331 uu____6332
    | FStar_Parser_AST.Op (op,args) when
        let uu____6339 = handleable_op op args  in
        Prims.op_Negation uu____6339 ->
        let uu____6340 =
          let uu____6341 =
            let uu____6342 =
              let uu____6343 =
                let uu____6344 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6344
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6343  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6342  in
          Prims.strcat "Operation " uu____6341  in
        failwith uu____6340
    | FStar_Parser_AST.Uvar uu____6345 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6346 = p_term false false e  in
        soft_parens_with_nesting uu____6346
    | FStar_Parser_AST.Const uu____6347 ->
        let uu____6348 = p_term false false e  in
        soft_parens_with_nesting uu____6348
    | FStar_Parser_AST.Op uu____6349 ->
        let uu____6356 = p_term false false e  in
        soft_parens_with_nesting uu____6356
    | FStar_Parser_AST.Tvar uu____6357 ->
        let uu____6358 = p_term false false e  in
        soft_parens_with_nesting uu____6358
    | FStar_Parser_AST.Var uu____6359 ->
        let uu____6360 = p_term false false e  in
        soft_parens_with_nesting uu____6360
    | FStar_Parser_AST.Name uu____6361 ->
        let uu____6362 = p_term false false e  in
        soft_parens_with_nesting uu____6362
    | FStar_Parser_AST.Construct uu____6363 ->
        let uu____6374 = p_term false false e  in
        soft_parens_with_nesting uu____6374
    | FStar_Parser_AST.Abs uu____6375 ->
        let uu____6382 = p_term false false e  in
        soft_parens_with_nesting uu____6382
    | FStar_Parser_AST.App uu____6383 ->
        let uu____6390 = p_term false false e  in
        soft_parens_with_nesting uu____6390
    | FStar_Parser_AST.Let uu____6391 ->
        let uu____6412 = p_term false false e  in
        soft_parens_with_nesting uu____6412
    | FStar_Parser_AST.LetOpen uu____6413 ->
        let uu____6418 = p_term false false e  in
        soft_parens_with_nesting uu____6418
    | FStar_Parser_AST.Seq uu____6419 ->
        let uu____6424 = p_term false false e  in
        soft_parens_with_nesting uu____6424
    | FStar_Parser_AST.Bind uu____6425 ->
        let uu____6432 = p_term false false e  in
        soft_parens_with_nesting uu____6432
    | FStar_Parser_AST.If uu____6433 ->
        let uu____6440 = p_term false false e  in
        soft_parens_with_nesting uu____6440
    | FStar_Parser_AST.Match uu____6441 ->
        let uu____6456 = p_term false false e  in
        soft_parens_with_nesting uu____6456
    | FStar_Parser_AST.TryWith uu____6457 ->
        let uu____6472 = p_term false false e  in
        soft_parens_with_nesting uu____6472
    | FStar_Parser_AST.Ascribed uu____6473 ->
        let uu____6482 = p_term false false e  in
        soft_parens_with_nesting uu____6482
    | FStar_Parser_AST.Record uu____6483 ->
        let uu____6496 = p_term false false e  in
        soft_parens_with_nesting uu____6496
    | FStar_Parser_AST.Project uu____6497 ->
        let uu____6502 = p_term false false e  in
        soft_parens_with_nesting uu____6502
    | FStar_Parser_AST.Product uu____6503 ->
        let uu____6510 = p_term false false e  in
        soft_parens_with_nesting uu____6510
    | FStar_Parser_AST.Sum uu____6511 ->
        let uu____6518 = p_term false false e  in
        soft_parens_with_nesting uu____6518
    | FStar_Parser_AST.QForall uu____6519 ->
        let uu____6532 = p_term false false e  in
        soft_parens_with_nesting uu____6532
    | FStar_Parser_AST.QExists uu____6533 ->
        let uu____6546 = p_term false false e  in
        soft_parens_with_nesting uu____6546
    | FStar_Parser_AST.Refine uu____6547 ->
        let uu____6552 = p_term false false e  in
        soft_parens_with_nesting uu____6552
    | FStar_Parser_AST.NamedTyp uu____6553 ->
        let uu____6558 = p_term false false e  in
        soft_parens_with_nesting uu____6558
    | FStar_Parser_AST.Requires uu____6559 ->
        let uu____6566 = p_term false false e  in
        soft_parens_with_nesting uu____6566
    | FStar_Parser_AST.Ensures uu____6567 ->
        let uu____6574 = p_term false false e  in
        soft_parens_with_nesting uu____6574
    | FStar_Parser_AST.Attributes uu____6575 ->
        let uu____6578 = p_term false false e  in
        soft_parens_with_nesting uu____6578
    | FStar_Parser_AST.Quote uu____6579 ->
        let uu____6584 = p_term false false e  in
        soft_parens_with_nesting uu____6584
    | FStar_Parser_AST.VQuote uu____6585 ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___63_6587  ->
    match uu___63_6587 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6591 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6591
    | FStar_Const.Const_string (s,uu____6593) ->
        let uu____6594 = str s  in FStar_Pprint.dquotes uu____6594
    | FStar_Const.Const_bytearray (bytes,uu____6596) ->
        let uu____6601 =
          let uu____6602 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6602  in
        let uu____6603 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6601 uu____6603
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___61_6621 =
          match uu___61_6621 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___62_6625 =
          match uu___62_6625 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6636  ->
               match uu____6636 with
               | (s,w) ->
                   let uu____6643 = signedness s  in
                   let uu____6644 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6643 uu____6644)
            sign_width_opt
           in
        let uu____6645 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6645 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6647 = FStar_Range.string_of_range r  in str uu____6647
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6649 = p_quident lid  in
        let uu____6650 =
          let uu____6651 =
            let uu____6652 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6652  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6651  in
        FStar_Pprint.op_Hat_Hat uu____6649 uu____6650

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6654 = str "u#"  in
    let uu____6655 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6654 uu____6655

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6657;_},u1::u2::[])
        ->
        let uu____6662 =
          let uu____6663 = p_universeFrom u1  in
          let uu____6664 =
            let uu____6665 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6665  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6663 uu____6664  in
        FStar_Pprint.group uu____6662
    | FStar_Parser_AST.App uu____6666 ->
        let uu____6673 = head_and_args u  in
        (match uu____6673 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6699 =
                    let uu____6700 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6701 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6709  ->
                           match uu____6709 with
                           | (u1,uu____6715) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6700 uu____6701  in
                  FStar_Pprint.group uu____6699
              | uu____6716 ->
                  let uu____6717 =
                    let uu____6718 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6718
                     in
                  failwith uu____6717))
    | uu____6719 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6743 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6743
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6744;_},uu____6745::uu____6746::[])
        ->
        let uu____6749 = p_universeFrom u  in
        soft_parens_with_nesting uu____6749
    | FStar_Parser_AST.App uu____6750 ->
        let uu____6757 = p_universeFrom u  in
        soft_parens_with_nesting uu____6757
    | uu____6758 ->
        let uu____6759 =
          let uu____6760 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6760
           in
        failwith uu____6759

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
       | FStar_Parser_AST.Module (uu____6800,decls) ->
           let uu____6806 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6806
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____6815,decls,uu____6817) ->
           let uu____6822 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____6822
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____6873  ->
         match uu____6873 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____6913,decls) -> decls
        | FStar_Parser_AST.Interface (uu____6919,decls,uu____6921) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____6966 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____6979;
                 FStar_Parser_AST.doc = uu____6980;
                 FStar_Parser_AST.quals = uu____6981;
                 FStar_Parser_AST.attrs = uu____6982;_}::uu____6983 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____6989 =
                   let uu____6992 =
                     let uu____6995 = FStar_List.tl ds  in d :: uu____6995
                      in
                   d0 :: uu____6992  in
                 (uu____6989, (d0.FStar_Parser_AST.drange))
             | uu____7000 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____6966 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7058 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7058 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7154 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7154, comments1))))))
  