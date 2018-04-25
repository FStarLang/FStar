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
  
let (prefix2_nonempty :
  FStar_Pprint.document -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun prefix_  ->
    fun body  ->
      if body = FStar_Pprint.empty then prefix_ else prefix2 prefix_ body
  
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
  'Auu____169 .
    FStar_Pprint.document ->
      ('Auu____169 -> FStar_Pprint.document) ->
        'Auu____169 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____191 =
          let uu____192 =
            let uu____193 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____193  in
          FStar_Pprint.separate_map uu____192 f l  in
        FStar_Pprint.group uu____191
  
let precede_break_separate_map :
  'Auu____199 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____199 -> FStar_Pprint.document) ->
          'Auu____199 Prims.list -> FStar_Pprint.document
  =
  fun prec  ->
    fun sep  ->
      fun f  ->
        fun l  ->
          let uu____225 =
            let uu____226 = FStar_Pprint.op_Hat_Hat prec FStar_Pprint.space
               in
            let uu____227 =
              let uu____228 = FStar_List.hd l  in
              FStar_All.pipe_right uu____228 f  in
            FStar_Pprint.precede uu____226 uu____227  in
          let uu____229 =
            let uu____230 = FStar_List.tl l  in
            FStar_Pprint.concat_map
              (fun x  ->
                 let uu____236 =
                   let uu____237 =
                     let uu____238 = f x  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____238  in
                   FStar_Pprint.op_Hat_Hat sep uu____237  in
                 FStar_Pprint.op_Hat_Hat break1 uu____236) uu____230
             in
          FStar_Pprint.op_Hat_Hat uu____225 uu____229
  
let concat_break_map :
  'Auu____242 .
    ('Auu____242 -> FStar_Pprint.document) ->
      'Auu____242 Prims.list -> FStar_Pprint.document
  =
  fun f  ->
    fun l  ->
      let uu____260 =
        FStar_Pprint.concat_map
          (fun x  ->
             let uu____264 = f x  in FStar_Pprint.op_Hat_Hat uu____264 break1)
          l
         in
      FStar_Pprint.group uu____260
  
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
    let uu____289 = str "begin"  in
    let uu____290 = str "end"  in
    FStar_Pprint.soft_surround (Prims.parse_int "2") (Prims.parse_int "1")
      uu____289 contents uu____290
  
let separate_map_last :
  'Auu____295 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____295 -> FStar_Pprint.document) ->
        'Auu____295 Prims.list -> FStar_Pprint.document
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
  'Auu____340 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____340 -> FStar_Pprint.document) ->
        'Auu____340 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        let uu____367 =
          let uu____368 =
            let uu____369 = FStar_Pprint.op_Hat_Hat sep break1  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____369  in
          separate_map_last uu____368 f l  in
        FStar_Pprint.group uu____367
  
let separate_map_or_flow :
  'Auu____374 .
    FStar_Pprint.document ->
      ('Auu____374 -> FStar_Pprint.document) ->
        'Auu____374 Prims.list -> FStar_Pprint.document
  =
  fun sep  ->
    fun f  ->
      fun l  ->
        if (FStar_List.length l) < (Prims.parse_int "10")
        then FStar_Pprint.separate_map sep f l
        else FStar_Pprint.flow_map sep f l
  
let flow_map_last :
  'Auu____401 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____401 -> FStar_Pprint.document) ->
        'Auu____401 Prims.list -> FStar_Pprint.document
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
  'Auu____446 .
    FStar_Pprint.document ->
      (Prims.bool -> 'Auu____446 -> FStar_Pprint.document) ->
        'Auu____446 Prims.list -> FStar_Pprint.document
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
  'Auu____493 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____493 -> FStar_Pprint.document) ->
                  'Auu____493 Prims.list -> FStar_Pprint.document
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
                    (let uu____538 = FStar_Pprint.separate_map sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____538
                       closing)
  
let soft_surround_map_or_flow :
  'Auu____548 .
    Prims.int ->
      Prims.int ->
        FStar_Pprint.document ->
          FStar_Pprint.document ->
            FStar_Pprint.document ->
              FStar_Pprint.document ->
                ('Auu____548 -> FStar_Pprint.document) ->
                  'Auu____548 Prims.list -> FStar_Pprint.document
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
                    (let uu____593 = separate_map_or_flow sep f xs  in
                     FStar_Pprint.soft_surround n1 b opening uu____593
                       closing)
  
let (doc_of_fsdoc :
  (Prims.string,(Prims.string,Prims.string) FStar_Pervasives_Native.tuple2
                  Prims.list)
    FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun uu____606  ->
    match uu____606 with
    | (comment,keywords) ->
        let uu____631 =
          let uu____632 =
            let uu____635 = str comment  in
            let uu____636 =
              let uu____639 =
                let uu____642 =
                  FStar_Pprint.separate_map FStar_Pprint.comma
                    (fun uu____651  ->
                       match uu____651 with
                       | (k,v1) ->
                           let uu____658 =
                             let uu____661 = str k  in
                             let uu____662 =
                               let uu____665 =
                                 let uu____668 = str v1  in [uu____668]  in
                               FStar_Pprint.rarrow :: uu____665  in
                             uu____661 :: uu____662  in
                           FStar_Pprint.concat uu____658) keywords
                   in
                [uu____642]  in
              FStar_Pprint.space :: uu____639  in
            uu____635 :: uu____636  in
          FStar_Pprint.concat uu____632  in
        FStar_Pprint.group uu____631
  
let (is_unit : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Const (FStar_Const.Const_unit ) -> true
    | uu____672 -> false
  
let (matches_var : FStar_Parser_AST.term -> FStar_Ident.ident -> Prims.bool)
  =
  fun t  ->
    fun x  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Var y ->
          x.FStar_Ident.idText = (FStar_Ident.text_of_lid y)
      | uu____680 -> false
  
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
        | FStar_Parser_AST.Construct (lid,uu____709::(e2,uu____711)::[]) ->
            (FStar_Ident.lid_equals lid cons_lid1) && (aux e2)
        | uu____734 -> false  in
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
    | FStar_Parser_AST.Construct (uu____746,[]) -> []
    | FStar_Parser_AST.Construct
        (uu____757,(e1,FStar_Parser_AST.Nothing )::(e2,FStar_Parser_AST.Nothing
                                                    )::[])
        -> let uu____778 = extract_from_list e2  in e1 :: uu____778
    | uu____781 ->
        let uu____782 =
          let uu____783 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a list %s" uu____783  in
        failwith uu____782
  
let (is_array : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var lid;
           FStar_Parser_AST.range = uu____790;
           FStar_Parser_AST.level = uu____791;_},l,FStar_Parser_AST.Nothing
         )
        ->
        (FStar_Ident.lid_equals lid FStar_Parser_Const.array_mk_array_lid) &&
          (is_list l)
    | uu____793 -> false
  
let rec (is_ref_set : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var maybe_empty_lid ->
        FStar_Ident.lid_equals maybe_empty_lid FStar_Parser_Const.set_empty
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var maybe_singleton_lid;
           FStar_Parser_AST.range = uu____799;
           FStar_Parser_AST.level = uu____800;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          maybe_addr_of_lid;
                                                        FStar_Parser_AST.range
                                                          = uu____802;
                                                        FStar_Parser_AST.level
                                                          = uu____803;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____805;
                                                   FStar_Parser_AST.level =
                                                     uu____806;_},FStar_Parser_AST.Nothing
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
                FStar_Parser_AST.range = uu____808;
                FStar_Parser_AST.level = uu____809;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____811;
           FStar_Parser_AST.level = uu____812;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        ((FStar_Ident.lid_equals maybe_union_lid FStar_Parser_Const.set_union)
           && (is_ref_set e1))
          && (is_ref_set e2)
    | uu____814 -> false
  
let rec (extract_from_ref_set :
  FStar_Parser_AST.term -> FStar_Parser_AST.term Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var uu____822 -> []
    | FStar_Parser_AST.App
        ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____823;
           FStar_Parser_AST.range = uu____824;
           FStar_Parser_AST.level = uu____825;_},{
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.App
                                                     ({
                                                        FStar_Parser_AST.tm =
                                                          FStar_Parser_AST.Var
                                                          uu____826;
                                                        FStar_Parser_AST.range
                                                          = uu____827;
                                                        FStar_Parser_AST.level
                                                          = uu____828;_},e1,FStar_Parser_AST.Nothing
                                                      );
                                                   FStar_Parser_AST.range =
                                                     uu____830;
                                                   FStar_Parser_AST.level =
                                                     uu____831;_},FStar_Parser_AST.Nothing
         )
        -> [e1]
    | FStar_Parser_AST.App
        ({
           FStar_Parser_AST.tm = FStar_Parser_AST.App
             ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var uu____832;
                FStar_Parser_AST.range = uu____833;
                FStar_Parser_AST.level = uu____834;_},e1,FStar_Parser_AST.Nothing
              );
           FStar_Parser_AST.range = uu____836;
           FStar_Parser_AST.level = uu____837;_},e2,FStar_Parser_AST.Nothing
         )
        ->
        let uu____839 = extract_from_ref_set e1  in
        let uu____842 = extract_from_ref_set e2  in
        FStar_List.append uu____839 uu____842
    | uu____845 ->
        let uu____846 =
          let uu____847 = FStar_Parser_AST.term_to_string e  in
          FStar_Util.format1 "Not a ref set %s" uu____847  in
        failwith uu____846
  
let (is_general_application : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____853 = (is_array e) || (is_ref_set e)  in
    Prims.op_Negation uu____853
  
let (is_general_construction : FStar_Parser_AST.term -> Prims.bool) =
  fun e  ->
    let uu____857 = (is_list e) || (is_lex_list e)  in
    Prims.op_Negation uu____857
  
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
      | uu____924 -> (e1, acc)  in
    aux e []
  
type associativity =
  | Left 
  | Right 
  | NonAssoc [@@deriving show]
let (uu___is_Left : associativity -> Prims.bool) =
  fun projectee  -> match projectee with | Left  -> true | uu____938 -> false 
let (uu___is_Right : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | Right  -> true | uu____942 -> false
  
let (uu___is_NonAssoc : associativity -> Prims.bool) =
  fun projectee  ->
    match projectee with | NonAssoc  -> true | uu____946 -> false
  
type token = (FStar_Char.char,Prims.string) FStar_Util.either[@@deriving
                                                               show]
type associativity_level =
  (associativity,token Prims.list) FStar_Pervasives_Native.tuple2[@@deriving
                                                                   show]
let (token_to_string :
  (FStar_BaseTypes.char,Prims.string) FStar_Util.either -> Prims.string) =
  fun uu___50_964  ->
    match uu___50_964 with
    | FStar_Util.Inl c -> Prims.strcat (FStar_Util.string_of_char c) ".*"
    | FStar_Util.Inr s -> s
  
let (matches_token :
  Prims.string ->
    (FStar_Char.char,Prims.string) FStar_Util.either -> Prims.bool)
  =
  fun s  ->
    fun uu___51_981  ->
      match uu___51_981 with
      | FStar_Util.Inl c ->
          let uu____990 = FStar_String.get s (Prims.parse_int "0")  in
          uu____990 = c
      | FStar_Util.Inr s' -> s = s'
  
let matches_level :
  'Auu____998 .
    Prims.string ->
      ('Auu____998,(FStar_Char.char,Prims.string) FStar_Util.either
                     Prims.list)
        FStar_Pervasives_Native.tuple2 -> Prims.bool
  =
  fun s  ->
    fun uu____1017  ->
      match uu____1017 with
      | (assoc_levels,tokens) ->
          let uu____1045 = FStar_List.tryFind (matches_token s) tokens  in
          uu____1045 <> FStar_Pervasives_Native.None
  
let opinfix4 :
  'Auu____1071 .
    Prims.unit ->
      (associativity,('Auu____1071,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1082  -> (Right, [FStar_Util.Inr "**"]) 
let opinfix3 :
  'Auu____1098 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1098) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1110  ->
    (Left, [FStar_Util.Inl 42; FStar_Util.Inl 47; FStar_Util.Inl 37])
  
let opinfix2 :
  'Auu____1145 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1145) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1157  -> (Left, [FStar_Util.Inl 43; FStar_Util.Inl 45]) 
let minus_lvl :
  'Auu____1185 .
    Prims.unit ->
      (associativity,('Auu____1185,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1196  -> (Left, [FStar_Util.Inr "-"]) 
let opinfix1 :
  'Auu____1212 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1212) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1224  -> (Right, [FStar_Util.Inl 64; FStar_Util.Inl 94]) 
let pipe_right :
  'Auu____1252 .
    Prims.unit ->
      (associativity,('Auu____1252,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1263  -> (Left, [FStar_Util.Inr "|>"]) 
let opinfix0d :
  'Auu____1279 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1279) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1291  -> (Left, [FStar_Util.Inl 36]) 
let opinfix0c :
  'Auu____1312 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1312) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun uu____1324  ->
    (Left, [FStar_Util.Inl 61; FStar_Util.Inl 60; FStar_Util.Inl 62])
  
let equal :
  'Auu____1359 .
    Prims.unit ->
      (associativity,('Auu____1359,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1370  -> (Left, [FStar_Util.Inr "="]) 
let opinfix0b :
  'Auu____1386 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1386) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1398  -> (Left, [FStar_Util.Inl 38]) 
let opinfix0a :
  'Auu____1419 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____1419) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1431  -> (Left, [FStar_Util.Inl 124]) 
let colon_equals :
  'Auu____1452 .
    Prims.unit ->
      (associativity,('Auu____1452,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1463  -> (NonAssoc, [FStar_Util.Inr ":="]) 
let amp :
  'Auu____1479 .
    Prims.unit ->
      (associativity,('Auu____1479,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1490  -> (Right, [FStar_Util.Inr "&"]) 
let colon_colon :
  'Auu____1506 .
    Prims.unit ->
      (associativity,('Auu____1506,Prims.string) FStar_Util.either Prims.list)
        FStar_Pervasives_Native.tuple2
  = fun uu____1517  -> (Right, [FStar_Util.Inr "::"]) 
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
  let levels_from_associativity l uu___52_1724 =
    match uu___52_1724 with
    | Left  -> (l, l, (l - (Prims.parse_int "1")))
    | Right  -> ((l - (Prims.parse_int "1")), l, l)
    | NonAssoc  ->
        ((l - (Prims.parse_int "1")), l, (l - (Prims.parse_int "1")))
     in
  FStar_List.mapi
    (fun i  ->
       fun uu____1764  ->
         match uu____1764 with
         | (assoc1,tokens) -> ((levels_from_associativity i assoc1), tokens))
    level_associativity_spec
  
let (assign_levels :
  associativity_level Prims.list ->
    Prims.string ->
      (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun token_associativity_spec  ->
    fun s  ->
      let uu____1844 = FStar_List.tryFind (matches_level s) level_table  in
      match uu____1844 with
      | FStar_Pervasives_Native.Some (assoc_levels,uu____1894) ->
          assoc_levels
      | uu____1938 -> failwith (Prims.strcat "Unrecognized operator " s)
  
let (max : Prims.int -> Prims.int -> Prims.int) =
  fun k1  -> fun k2  -> if k1 > k2 then k1 else k2 
let max_level :
  'Auu____1973 .
    ('Auu____1973,(FStar_Char.char,Prims.string) FStar_Util.either Prims.list)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.int
  =
  fun l  ->
    let find_level_and_max n1 level =
      let uu____2033 =
        FStar_List.tryFind
          (fun uu____2073  ->
             match uu____2073 with
             | (uu____2091,tokens) ->
                 tokens = (FStar_Pervasives_Native.snd level)) level_table
         in
      match uu____2033 with
      | FStar_Pervasives_Native.Some ((uu____2133,l1,uu____2135),uu____2136)
          -> max n1 l1
      | FStar_Pervasives_Native.None  ->
          let uu____2191 =
            let uu____2192 =
              let uu____2193 =
                FStar_List.map token_to_string
                  (FStar_Pervasives_Native.snd level)
                 in
              FStar_String.concat "," uu____2193  in
            FStar_Util.format1 "Undefined associativity level %s" uu____2192
             in
          failwith uu____2191
       in
    FStar_List.fold_left find_level_and_max (Prims.parse_int "0") l
  
let (levels :
  Prims.string ->
    (Prims.int,Prims.int,Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun op  ->
    let uu____2227 = assign_levels level_associativity_spec op  in
    match uu____2227 with
    | (left1,mine,right1) ->
        if op = "*"
        then ((left1 - (Prims.parse_int "1")), mine, right1)
        else (left1, mine, right1)
  
let operatorInfix0ad12 :
  'Auu____2251 .
    Prims.unit ->
      (associativity,(FStar_Char.char,'Auu____2251) FStar_Util.either
                       Prims.list)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun uu____2265  ->
    [opinfix0a ();
    opinfix0b ();
    opinfix0c ();
    opinfix0d ();
    opinfix1 ();
    opinfix2 ()]
  
let (is_operatorInfix0ad12 : FStar_Ident.ident -> Prims.bool) =
  fun op  ->
    let uu____2346 =
      let uu____2360 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2360 (operatorInfix0ad12 ())  in
    uu____2346 <> FStar_Pervasives_Native.None
  
let (is_operatorInfix34 : FStar_Ident.ident -> Prims.bool) =
  let opinfix34 = [opinfix3 (); opinfix4 ()]  in
  fun op  ->
    let uu____2473 =
      let uu____2487 =
        FStar_All.pipe_left matches_level (FStar_Ident.text_of_id op)  in
      FStar_List.tryFind uu____2487 opinfix34  in
    uu____2473 <> FStar_Pervasives_Native.None
  
let (handleable_args_length : FStar_Ident.ident -> Prims.int) =
  fun op  ->
    let op_s = FStar_Ident.text_of_id op  in
    let uu____2553 =
      (is_general_prefix_op op) || (FStar_List.mem op_s ["-"; "~"])  in
    if uu____2553
    then (Prims.parse_int "1")
    else
      (let uu____2555 =
         ((is_operatorInfix0ad12 op) || (is_operatorInfix34 op)) ||
           (FStar_List.mem op_s
              ["<==>"; "==>"; "\\/"; "/\\"; "="; "|>"; ":="; ".()"; ".[]"])
          in
       if uu____2555
       then (Prims.parse_int "2")
       else
         if FStar_List.mem op_s [".()<-"; ".[]<-"]
         then (Prims.parse_int "3")
         else (Prims.parse_int "0"))
  
let handleable_op :
  'Auu____2561 . FStar_Ident.ident -> 'Auu____2561 Prims.list -> Prims.bool =
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
      | uu____2574 -> false
  
let (comment_stack :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    FStar_ST.ref)
  = FStar_Util.mk_ref [] 
let with_comment :
  'Auu____2608 .
    ('Auu____2608 -> FStar_Pprint.document) ->
      'Auu____2608 -> FStar_Range.range -> FStar_Pprint.document
  =
  fun printer  ->
    fun tm  ->
      fun tmrange  ->
        let rec comments_before_pos acc print_pos lookahead_pos =
          let uu____2640 = FStar_ST.op_Bang comment_stack  in
          match uu____2640 with
          | [] -> (acc, false)
          | (comment,crange)::cs ->
              let uu____2699 = FStar_Range.range_before_pos crange print_pos
                 in
              if uu____2699
              then
                (FStar_ST.op_Colon_Equals comment_stack cs;
                 (let uu____2736 =
                    let uu____2737 =
                      let uu____2738 = str comment  in
                      FStar_Pprint.op_Hat_Hat uu____2738
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat acc uu____2737  in
                  comments_before_pos uu____2736 print_pos lookahead_pos))
              else
                (let uu____2740 =
                   FStar_Range.range_before_pos crange lookahead_pos  in
                 (acc, uu____2740))
           in
        let uu____2741 =
          let uu____2746 =
            let uu____2747 = FStar_Range.start_of_range tmrange  in
            FStar_Range.end_of_line uu____2747  in
          let uu____2748 = FStar_Range.end_of_range tmrange  in
          comments_before_pos FStar_Pprint.empty uu____2746 uu____2748  in
        match uu____2741 with
        | (comments,has_lookahead) ->
            let printed_e = printer tm  in
            let comments1 =
              if has_lookahead
              then
                let pos = FStar_Range.end_of_range tmrange  in
                let uu____2754 = comments_before_pos comments pos pos  in
                FStar_Pervasives_Native.fst uu____2754
              else comments  in
            let uu____2760 = FStar_Pprint.op_Hat_Hat comments1 printed_e  in
            FStar_Pprint.group uu____2760
  
let rec (place_comments_until_pos :
  Prims.int ->
    Prims.int ->
      FStar_Range.pos -> FStar_Pprint.document -> FStar_Pprint.document)
  =
  fun k  ->
    fun lbegin  ->
      fun pos_end  ->
        fun doc1  ->
          let uu____2773 = FStar_ST.op_Bang comment_stack  in
          match uu____2773 with
          | (comment,crange)::cs when
              FStar_Range.range_before_pos crange pos_end ->
              (FStar_ST.op_Colon_Equals comment_stack cs;
               (let lnum =
                  let uu____2857 =
                    let uu____2858 =
                      let uu____2859 = FStar_Range.start_of_range crange  in
                      FStar_Range.line_of_pos uu____2859  in
                    uu____2858 - lbegin  in
                  max k uu____2857  in
                let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                let doc2 =
                  let uu____2862 =
                    let uu____2863 =
                      FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                    let uu____2864 = str comment  in
                    FStar_Pprint.op_Hat_Hat uu____2863 uu____2864  in
                  FStar_Pprint.op_Hat_Hat doc1 uu____2862  in
                let uu____2865 =
                  let uu____2866 = FStar_Range.end_of_range crange  in
                  FStar_Range.line_of_pos uu____2866  in
                place_comments_until_pos (Prims.parse_int "1") uu____2865
                  pos_end doc2))
          | uu____2867 ->
              if doc1 = FStar_Pprint.empty
              then FStar_Pprint.empty
              else
                (let lnum =
                   let uu____2876 =
                     let uu____2877 = FStar_Range.line_of_pos pos_end  in
                     uu____2877 - lbegin  in
                   max (Prims.parse_int "1") uu____2876  in
                 let lnum1 = Prims.min (Prims.parse_int "2") lnum  in
                 let uu____2879 =
                   FStar_Pprint.repeat lnum1 FStar_Pprint.hardline  in
                 FStar_Pprint.op_Hat_Hat doc1 uu____2879)
  
let separate_map_with_comments :
  'Auu____2886 .
    FStar_Pprint.document ->
      FStar_Pprint.document ->
        ('Auu____2886 -> FStar_Pprint.document) ->
          'Auu____2886 Prims.list ->
            ('Auu____2886 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____2934 x =
              match uu____2934 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____2948 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____2948 doc1
                     in
                  let uu____2949 =
                    let uu____2950 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____2950  in
                  let uu____2951 =
                    let uu____2952 =
                      let uu____2953 = f x  in
                      FStar_Pprint.op_Hat_Hat sep uu____2953  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____2952  in
                  (uu____2949, uu____2951)
               in
            let uu____2954 =
              let uu____2961 = FStar_List.hd xs  in
              let uu____2962 = FStar_List.tl xs  in (uu____2961, uu____2962)
               in
            match uu____2954 with
            | (x,xs1) ->
                let init1 =
                  let uu____2978 =
                    let uu____2979 =
                      let uu____2980 = extract_range x  in
                      FStar_Range.end_of_range uu____2980  in
                    FStar_Range.line_of_pos uu____2979  in
                  let uu____2981 =
                    let uu____2982 = f x  in
                    FStar_Pprint.op_Hat_Hat prefix1 uu____2982  in
                  (uu____2978, uu____2981)  in
                let uu____2983 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____2983
  
let separate_map_with_comments_kw :
  'Auu____2999 'Auu____3000 .
    'Auu____2999 ->
      'Auu____2999 ->
        ('Auu____2999 -> 'Auu____3000 -> FStar_Pprint.document) ->
          'Auu____3000 Prims.list ->
            ('Auu____3000 -> FStar_Range.range) -> FStar_Pprint.document
  =
  fun prefix1  ->
    fun sep  ->
      fun f  ->
        fun xs  ->
          fun extract_range  ->
            let fold_fun uu____3053 x =
              match uu____3053 with
              | (last_line,doc1) ->
                  let r = extract_range x  in
                  let doc2 =
                    let uu____3067 = FStar_Range.start_of_range r  in
                    place_comments_until_pos (Prims.parse_int "1") last_line
                      uu____3067 doc1
                     in
                  let uu____3068 =
                    let uu____3069 = FStar_Range.end_of_range r  in
                    FStar_Range.line_of_pos uu____3069  in
                  let uu____3070 =
                    let uu____3071 = f sep x  in
                    FStar_Pprint.op_Hat_Hat doc2 uu____3071  in
                  (uu____3068, uu____3070)
               in
            let uu____3072 =
              let uu____3079 = FStar_List.hd xs  in
              let uu____3080 = FStar_List.tl xs  in (uu____3079, uu____3080)
               in
            match uu____3072 with
            | (x,xs1) ->
                let init1 =
                  let uu____3096 =
                    let uu____3097 =
                      let uu____3098 = extract_range x  in
                      FStar_Range.end_of_range uu____3098  in
                    FStar_Range.line_of_pos uu____3097  in
                  let uu____3099 = f prefix1 x  in (uu____3096, uu____3099)
                   in
                let uu____3100 = FStar_List.fold_left fold_fun init1 xs1  in
                FStar_Pervasives_Native.snd uu____3100
  
let rec (p_decl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    let qualifiers =
      match ((d.FStar_Parser_AST.quals), (d.FStar_Parser_AST.d)) with
      | ((FStar_Parser_AST.Assumption )::[],FStar_Parser_AST.Assume
         (id1,uu____3515)) ->
          let uu____3518 =
            let uu____3519 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3519 FStar_Util.is_upper  in
          if uu____3518
          then
            let uu____3520 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3520 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3522 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3527 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3528 =
      let uu____3529 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3530 =
        let uu____3531 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3531  in
      FStar_Pprint.op_Hat_Hat uu____3529 uu____3530  in
    FStar_Pprint.op_Hat_Hat uu____3527 uu____3528

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3533 ->
        let uu____3534 =
          let uu____3535 = str "@ "  in
          let uu____3536 =
            let uu____3537 =
              let uu____3538 =
                let uu____3539 =
                  let uu____3540 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3540  in
                FStar_Pprint.op_Hat_Hat uu____3539 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3538  in
            FStar_Pprint.op_Hat_Hat uu____3537 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3535 uu____3536  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3534

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3543  ->
    match uu____3543 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3577 =
                match uu____3577 with
                | (kwd,arg) ->
                    let uu____3584 = str "@"  in
                    let uu____3585 =
                      let uu____3586 = str kwd  in
                      let uu____3587 =
                        let uu____3588 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3588
                         in
                      FStar_Pprint.op_Hat_Hat uu____3586 uu____3587  in
                    FStar_Pprint.op_Hat_Hat uu____3584 uu____3585
                 in
              let uu____3589 =
                let uu____3590 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3590 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3589
           in
        let uu____3595 =
          let uu____3596 =
            let uu____3597 =
              let uu____3598 =
                let uu____3599 = str doc1  in
                let uu____3600 =
                  let uu____3601 =
                    let uu____3602 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3602  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3601  in
                FStar_Pprint.op_Hat_Hat uu____3599 uu____3600  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3598  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3597  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3596  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3595

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3606 =
          let uu____3607 = str "val"  in
          let uu____3608 =
            let uu____3609 =
              let uu____3610 = p_lident lid  in
              let uu____3611 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3610 uu____3611  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3609  in
          FStar_Pprint.op_Hat_Hat uu____3607 uu____3608  in
        let uu____3612 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3606 uu____3612
    | FStar_Parser_AST.TopLevelLet (uu____3613,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3638 =
               let uu____3639 = str "let"  in p_letlhs uu____3639 lb  in
             FStar_Pprint.group uu____3638) lbs
    | uu____3640 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3643 =
          let uu____3644 = str "open"  in
          let uu____3645 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3644 uu____3645  in
        FStar_Pprint.group uu____3643
    | FStar_Parser_AST.Include uid ->
        let uu____3647 =
          let uu____3648 = str "include"  in
          let uu____3649 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3648 uu____3649  in
        FStar_Pprint.group uu____3647
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3652 =
          let uu____3653 = str "module"  in
          let uu____3654 =
            let uu____3655 =
              let uu____3656 = p_uident uid1  in
              let uu____3657 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3656 uu____3657  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3655  in
          FStar_Pprint.op_Hat_Hat uu____3653 uu____3654  in
        let uu____3658 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3652 uu____3658
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3660 =
          let uu____3661 = str "module"  in
          let uu____3662 =
            let uu____3663 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3663  in
          FStar_Pprint.op_Hat_Hat uu____3661 uu____3662  in
        FStar_Pprint.group uu____3660
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3696 = str "effect"  in
          let uu____3697 =
            let uu____3698 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3698  in
          FStar_Pprint.op_Hat_Hat uu____3696 uu____3697  in
        let uu____3699 =
          let uu____3700 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3700 FStar_Pprint.equals
           in
        let uu____3701 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3699 uu____3701
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3719 =
          let uu____3720 = str "type"  in
          let uu____3721 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3720 uu____3721  in
        let uu____3734 =
          let uu____3735 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3773 =
                    let uu____3774 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3774 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3773)) uu____3735
           in
        FStar_Pprint.op_Hat_Hat uu____3719 uu____3734
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3790 = str "let"  in
          let uu____3791 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3790 uu____3791  in
        let uu____3792 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3792 p_letbinding lbs
          (fun uu____3800  ->
             match uu____3800 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3809 = str "val"  in
        let uu____3810 =
          let uu____3811 =
            let uu____3812 = p_lident lid  in
            let uu____3813 =
              let uu____3814 =
                let uu____3815 =
                  let uu____3816 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3816  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3815  in
              FStar_Pprint.group uu____3814  in
            FStar_Pprint.op_Hat_Hat uu____3812 uu____3813  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3811  in
        FStar_Pprint.op_Hat_Hat uu____3809 uu____3810
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3820 =
            let uu____3821 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3821 FStar_Util.is_upper  in
          if uu____3820
          then FStar_Pprint.empty
          else
            (let uu____3823 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3823 FStar_Pprint.space)
           in
        let uu____3824 =
          let uu____3825 = p_ident id1  in
          let uu____3826 =
            let uu____3827 =
              let uu____3828 =
                let uu____3829 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3829  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3828  in
            FStar_Pprint.group uu____3827  in
          FStar_Pprint.op_Hat_Hat uu____3825 uu____3826  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3824
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3836 = str "exception"  in
        let uu____3837 =
          let uu____3838 =
            let uu____3839 = p_uident uid  in
            let uu____3840 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3844 =
                     let uu____3845 = str "of"  in
                     let uu____3846 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3845 uu____3846  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3844) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3839 uu____3840  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3838  in
        FStar_Pprint.op_Hat_Hat uu____3836 uu____3837
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3848 = str "new_effect"  in
        let uu____3849 =
          let uu____3850 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3850  in
        FStar_Pprint.op_Hat_Hat uu____3848 uu____3849
    | FStar_Parser_AST.SubEffect se ->
        let uu____3852 = str "sub_effect"  in
        let uu____3853 =
          let uu____3854 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3854  in
        FStar_Pprint.op_Hat_Hat uu____3852 uu____3853
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3857 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3857 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3858 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3859) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3877 = str "%splice"  in
        let uu____3878 =
          let uu____3879 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3879  in
        FStar_Pprint.op_Hat_Hat uu____3877 uu____3878

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___53_3880  ->
    match uu___53_3880 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3882 = str "#set-options"  in
        let uu____3883 =
          let uu____3884 =
            let uu____3885 = str s  in FStar_Pprint.dquotes uu____3885  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3884  in
        FStar_Pprint.op_Hat_Hat uu____3882 uu____3883
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3889 = str "#reset-options"  in
        let uu____3890 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3894 =
                 let uu____3895 = str s  in FStar_Pprint.dquotes uu____3895
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3894) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3889 uu____3890
    | FStar_Parser_AST.LightOff  ->
        (FStar_ST.op_Colon_Equals should_print_fs_typ_app true;
         str "#light \"off\"")

and (p_typars : FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  = fun bs  -> p_binders true bs

and (p_fsdocTypeDeclPairs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.tycon,FStar_Parser_AST.fsdoc
                              FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____3920  ->
      match uu____3920 with
      | (typedecl,fsdoc_opt) ->
          let uu____3933 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3933 with
           | (decl,body) ->
               let uu____3948 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3948)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___54_3950  ->
      match uu___54_3950 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3977 = FStar_Pprint.empty  in
          let uu____3978 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3978, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3996 =
            let uu____3997 = p_typ false false t  in jump2 uu____3997  in
          let uu____3998 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____3998, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4047 =
            match uu____4047 with
            | (lid1,t,doc_opt) ->
                let uu____4063 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4063
             in
          let p_fields uu____4077 =
            let uu____4078 =
              let uu____4079 =
                let uu____4080 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4080 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4079  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4078  in
          let uu____4089 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4089, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4147 =
            match uu____4147 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4173 =
                    let uu____4174 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4174  in
                  FStar_Range.extend_to_end_of_line uu____4173  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4198 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4211 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4211,
            ((fun uu____4216  ->
                let uu____4217 = datacon_doc ()  in jump2 uu____4217)))

and (p_typeDeclPrefix :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    Prims.bool ->
      FStar_Ident.ident ->
        FStar_Parser_AST.binder Prims.list ->
          FStar_Parser_AST.knd FStar_Pervasives_Native.option ->
            FStar_Pprint.document)
  =
  fun uu____4218  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4218 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4250 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4250  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4252 =
                        let uu____4255 =
                          let uu____4258 = p_fsdoc fsdoc  in
                          let uu____4259 =
                            let uu____4262 = cont lid_doc  in [uu____4262]
                             in
                          uu____4258 :: uu____4259  in
                        kw :: uu____4255  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4252
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4267 =
                        let uu____4268 =
                          let uu____4269 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4269 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4268
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4267
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4284 =
                          let uu____4285 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4285  in
                        prefix2 uu____4284 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4287  ->
      match uu____4287 with
      | (lid,t,doc_opt) ->
          let uu____4303 =
            let uu____4304 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4305 =
              let uu____4306 = p_lident lid  in
              let uu____4307 =
                let uu____4308 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4308  in
              FStar_Pprint.op_Hat_Hat uu____4306 uu____4307  in
            FStar_Pprint.op_Hat_Hat uu____4304 uu____4305  in
          FStar_Pprint.group uu____4303

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4309  ->
    match uu____4309 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4337 =
            let uu____4338 =
              let uu____4339 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4339  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4338  in
          FStar_Pprint.group uu____4337  in
        let uu____4340 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4341 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4345 =
                 let uu____4346 =
                   let uu____4347 =
                     let uu____4348 =
                       let uu____4349 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4349
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4348  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4347  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4346  in
               FStar_Pprint.group uu____4345) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4340 uu____4341

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4351  ->
      match uu____4351 with
      | (pat,uu____4357) ->
          let uu____4358 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4377 =
                  let uu____4378 =
                    let uu____4379 =
                      let uu____4380 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4380
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4379  in
                  FStar_Pprint.group uu____4378  in
                (pat1, uu____4377)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4392 =
                  let uu____4393 =
                    let uu____4394 =
                      let uu____4395 =
                        let uu____4396 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4396
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4395
                       in
                    FStar_Pprint.group uu____4394  in
                  let uu____4397 =
                    let uu____4398 =
                      let uu____4399 = str "by"  in
                      let uu____4400 =
                        let uu____4401 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4401
                         in
                      FStar_Pprint.op_Hat_Hat uu____4399 uu____4400  in
                    FStar_Pprint.group uu____4398  in
                  FStar_Pprint.op_Hat_Hat uu____4393 uu____4397  in
                (pat1, uu____4392)
            | uu____4402 -> (pat, FStar_Pprint.empty)  in
          (match uu____4358 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4406);
                       FStar_Parser_AST.prange = uu____4407;_},pats)
                    ->
                    let uu____4417 =
                      let uu____4418 =
                        let uu____4419 =
                          let uu____4420 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4420  in
                        FStar_Pprint.group uu____4419  in
                      let uu____4421 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4418 uu____4421  in
                    prefix2_nonempty uu____4417 ascr_doc
                | uu____4422 ->
                    let uu____4423 =
                      let uu____4424 =
                        let uu____4425 =
                          let uu____4426 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4426  in
                        FStar_Pprint.group uu____4425  in
                      FStar_Pprint.op_Hat_Hat uu____4424 ascr_doc  in
                    FStar_Pprint.group uu____4423))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4428  ->
      match uu____4428 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4437 =
            let uu____4438 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4438  in
          let uu____4439 =
            let uu____4440 =
              let uu____4441 =
                let uu____4442 =
                  let uu____4443 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4443  in
                FStar_Pprint.group uu____4442  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4441  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4440  in
          FStar_Pprint.ifflat uu____4437 uu____4439

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___55_4444  ->
    match uu___55_4444 with
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
        let uu____4469 = p_uident uid  in
        let uu____4470 = p_binders true bs  in
        let uu____4471 =
          let uu____4472 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4472  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4469 uu____4470 uu____4471

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
          let uu____4481 =
            let uu____4482 =
              let uu____4483 =
                let uu____4484 = p_uident uid  in
                let uu____4485 = p_binders true bs  in
                let uu____4486 =
                  let uu____4487 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4487  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4484 uu____4485 uu____4486
                 in
              FStar_Pprint.group uu____4483  in
            let uu____4488 =
              let uu____4489 = str "with"  in
              let uu____4490 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4489 uu____4490  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4482 uu____4488  in
          braces_with_nesting uu____4481

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
          let uu____4521 =
            let uu____4522 = p_lident lid  in
            let uu____4523 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4522 uu____4523  in
          let uu____4524 = p_simpleTerm ps false e  in
          prefix2 uu____4521 uu____4524
      | uu____4525 ->
          let uu____4526 =
            let uu____4527 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4527
             in
          failwith uu____4526

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4585 =
        match uu____4585 with
        | (kwd,t) ->
            let uu____4592 =
              let uu____4593 = str kwd  in
              let uu____4594 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4593 uu____4594  in
            let uu____4595 = p_simpleTerm ps false t  in
            prefix2 uu____4592 uu____4595
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4600 =
      let uu____4601 =
        let uu____4602 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4603 =
          let uu____4604 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4604  in
        FStar_Pprint.op_Hat_Hat uu____4602 uu____4603  in
      let uu____4605 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4601 uu____4605  in
    let uu____4606 =
      let uu____4607 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4607  in
    FStar_Pprint.op_Hat_Hat uu____4600 uu____4606

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___56_4608  ->
    match uu___56_4608 with
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
    | uu____4610 ->
        let uu____4611 =
          let uu____4612 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4612  in
        FStar_Pprint.op_Hat_Hat uu____4611 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___57_4615  ->
    match uu___57_4615 with
    | FStar_Parser_AST.Rec  ->
        let uu____4616 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4616
    | FStar_Parser_AST.Mutable  ->
        let uu____4617 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4617
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___58_4618  ->
    match uu___58_4618 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4623 =
          let uu____4624 =
            let uu____4625 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4625  in
          FStar_Pprint.separate_map uu____4624 p_tuplePattern pats  in
        FStar_Pprint.group uu____4623
    | uu____4626 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4633 =
          let uu____4634 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4634 p_constructorPattern pats  in
        FStar_Pprint.group uu____4633
    | uu____4635 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4638;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4643 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4644 = p_constructorPattern hd1  in
        let uu____4645 = p_constructorPattern tl1  in
        infix0 uu____4643 uu____4644 uu____4645
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4647;_},pats)
        ->
        let uu____4653 = p_quident uid  in
        let uu____4654 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4653 uu____4654
    | uu____4655 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4671;
               FStar_Parser_AST.blevel = uu____4672;
               FStar_Parser_AST.aqual = uu____4673;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4679 =
               let uu____4680 = p_ident lid  in
               p_refinement aqual uu____4680 t1 phi  in
             soft_parens_with_nesting uu____4679
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4682;
               FStar_Parser_AST.blevel = uu____4683;
               FStar_Parser_AST.aqual = uu____4684;_},phi))
             ->
             let uu____4686 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4686
         | uu____4687 ->
             let uu____4692 =
               let uu____4693 = p_tuplePattern pat  in
               let uu____4694 =
                 let uu____4695 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4695
                  in
               FStar_Pprint.op_Hat_Hat uu____4693 uu____4694  in
             soft_parens_with_nesting uu____4692)
    | FStar_Parser_AST.PatList pats ->
        let uu____4699 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4699 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4714 =
          match uu____4714 with
          | (lid,pat) ->
              let uu____4721 = p_qlident lid  in
              let uu____4722 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4721 uu____4722
           in
        let uu____4723 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4723
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4733 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4734 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4735 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4733 uu____4734 uu____4735
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4746 =
          let uu____4747 =
            let uu____4748 = str (FStar_Ident.text_of_id op)  in
            let uu____4749 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4748 uu____4749  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4747  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4746
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4757 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4758 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4757 uu____4758
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4760 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4763;
           FStar_Parser_AST.prange = uu____4764;_},uu____4765)
        ->
        let uu____4770 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4770
    | FStar_Parser_AST.PatTuple (uu____4771,false ) ->
        let uu____4776 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4776
    | uu____4777 ->
        let uu____4778 =
          let uu____4779 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4779  in
        failwith uu____4778

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4783 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4784 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4783 uu____4784
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4791;
                   FStar_Parser_AST.blevel = uu____4792;
                   FStar_Parser_AST.aqual = uu____4793;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4795 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4795 t1 phi
            | uu____4796 ->
                let uu____4797 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4798 =
                  let uu____4799 = p_lident lid  in
                  let uu____4800 =
                    let uu____4801 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____4801
                     in
                  FStar_Pprint.op_Hat_Hat uu____4799 uu____4800  in
                FStar_Pprint.op_Hat_Hat uu____4797 uu____4798
             in
          if is_atomic
          then
            let uu____4802 =
              let uu____4803 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4803  in
            FStar_Pprint.group uu____4802
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4805 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4812;
                  FStar_Parser_AST.blevel = uu____4813;
                  FStar_Parser_AST.aqual = uu____4814;_},phi)
               ->
               if is_atomic
               then
                 let uu____4816 =
                   let uu____4817 =
                     let uu____4818 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4818 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4817  in
                 FStar_Pprint.group uu____4816
               else
                 (let uu____4820 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4820)
           | uu____4821 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4830 -> false
            | FStar_Parser_AST.App uu____4841 -> false
            | FStar_Parser_AST.Op uu____4848 -> false
            | uu____4855 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4859 =
            let uu____4860 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4861 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4860 uu____4861  in
          let uu____4862 =
            let uu____4863 = p_appTerm t  in
            let uu____4864 =
              let uu____4865 =
                let uu____4866 =
                  let uu____4867 = soft_braces_with_nesting_tight phi1  in
                  let uu____4868 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4867 uu____4868  in
                FStar_Pprint.group uu____4866  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4865
               in
            FStar_Pprint.op_Hat_Hat uu____4863 uu____4864  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4859 uu____4862

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4879 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4879

and (text_of_id_or_underscore : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  ->
    if
      FStar_Util.starts_with lid.FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else str (FStar_Ident.text_of_id lid)

and (text_of_lid_or_underscore : FStar_Ident.lident -> FStar_Pprint.document)
  =
  fun lid  ->
    if
      FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
        FStar_Ident.reserved_prefix
    then FStar_Pprint.underscore
    else str (FStar_Ident.text_of_lid lid)

and (p_qlident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_quident : FStar_Ident.lid -> FStar_Pprint.document) =
  fun lid  -> text_of_lid_or_underscore lid

and (p_ident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_lident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_uident : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

and (p_tvar : FStar_Ident.ident -> FStar_Pprint.document) =
  fun lid  -> text_of_id_or_underscore lid

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
            let uu____4902 =
              let uu____4903 =
                let uu____4904 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4904 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4903  in
            let uu____4905 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4902 uu____4905
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4909 =
              let uu____4910 =
                let uu____4911 =
                  let uu____4912 = p_lident x  in
                  let uu____4913 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4912 uu____4913  in
                let uu____4914 =
                  let uu____4915 = p_noSeqTerm true false e1  in
                  let uu____4916 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4915 uu____4916  in
                op_Hat_Slash_Plus_Hat uu____4911 uu____4914  in
              FStar_Pprint.group uu____4910  in
            let uu____4917 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4909 uu____4917
        | uu____4918 ->
            let uu____4919 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4919

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
            let uu____4930 =
              let uu____4931 = p_tmIff e1  in
              let uu____4932 =
                let uu____4933 =
                  let uu____4934 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4934
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4933  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4931 uu____4932  in
            FStar_Pprint.group uu____4930
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4940 =
              let uu____4941 = p_tmIff e1  in
              let uu____4942 =
                let uu____4943 =
                  let uu____4944 =
                    let uu____4945 = p_typ false false t  in
                    let uu____4946 =
                      let uu____4947 = str "by"  in
                      let uu____4948 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4947 uu____4948  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4945 uu____4946  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4944
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4943  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4941 uu____4942  in
            FStar_Pprint.group uu____4940
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4949;_},e1::e2::e3::[])
            ->
            let uu____4955 =
              let uu____4956 =
                let uu____4957 =
                  let uu____4958 = p_atomicTermNotQUident e1  in
                  let uu____4959 =
                    let uu____4960 =
                      let uu____4961 =
                        let uu____4962 = p_term false false e2  in
                        soft_parens_with_nesting uu____4962  in
                      let uu____4963 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4961 uu____4963  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4960  in
                  FStar_Pprint.op_Hat_Hat uu____4958 uu____4959  in
                FStar_Pprint.group uu____4957  in
              let uu____4964 =
                let uu____4965 = p_noSeqTerm ps pb e3  in jump2 uu____4965
                 in
              FStar_Pprint.op_Hat_Hat uu____4956 uu____4964  in
            FStar_Pprint.group uu____4955
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4966;_},e1::e2::e3::[])
            ->
            let uu____4972 =
              let uu____4973 =
                let uu____4974 =
                  let uu____4975 = p_atomicTermNotQUident e1  in
                  let uu____4976 =
                    let uu____4977 =
                      let uu____4978 =
                        let uu____4979 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4979  in
                      let uu____4980 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4978 uu____4980  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4977  in
                  FStar_Pprint.op_Hat_Hat uu____4975 uu____4976  in
                FStar_Pprint.group uu____4974  in
              let uu____4981 =
                let uu____4982 = p_noSeqTerm ps pb e3  in jump2 uu____4982
                 in
              FStar_Pprint.op_Hat_Hat uu____4973 uu____4981  in
            FStar_Pprint.group uu____4972
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4992 =
              let uu____4993 = str "requires"  in
              let uu____4994 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4993 uu____4994  in
            FStar_Pprint.group uu____4992
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5004 =
              let uu____5005 = str "ensures"  in
              let uu____5006 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5005 uu____5006  in
            FStar_Pprint.group uu____5004
        | FStar_Parser_AST.Attributes es ->
            let uu____5010 =
              let uu____5011 = str "attributes"  in
              let uu____5012 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5011 uu____5012  in
            FStar_Pprint.group uu____5010
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5016 =
                let uu____5017 =
                  let uu____5018 = str "if"  in
                  let uu____5019 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5018 uu____5019  in
                let uu____5020 =
                  let uu____5021 = str "then"  in
                  let uu____5022 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5021 uu____5022  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5017 uu____5020  in
              FStar_Pprint.group uu____5016
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5025,uu____5026,e31) when
                     is_unit e31 ->
                     let uu____5028 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5028
                 | uu____5029 -> p_noSeqTerm false false e2  in
               let uu____5030 =
                 let uu____5031 =
                   let uu____5032 = str "if"  in
                   let uu____5033 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5032 uu____5033  in
                 let uu____5034 =
                   let uu____5035 =
                     let uu____5036 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5036 e2_doc  in
                   let uu____5037 =
                     let uu____5038 = str "else"  in
                     let uu____5039 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5038 uu____5039  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5035 uu____5037  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5031 uu____5034  in
               FStar_Pprint.group uu____5030)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5062 =
              let uu____5063 =
                let uu____5064 =
                  let uu____5065 = str "try"  in
                  let uu____5066 = p_noSeqTerm false false e1  in
                  prefix2 uu____5065 uu____5066  in
                let uu____5067 =
                  let uu____5068 = str "with"  in
                  let uu____5069 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5068 uu____5069  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5064 uu____5067  in
              FStar_Pprint.group uu____5063  in
            let uu____5078 = paren_if (ps || pb)  in uu____5078 uu____5062
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5103 =
              let uu____5104 =
                let uu____5105 =
                  let uu____5106 = str "match"  in
                  let uu____5107 = p_noSeqTerm false false e1  in
                  let uu____5108 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5106 uu____5107 uu____5108
                   in
                let uu____5109 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5105 uu____5109  in
              FStar_Pprint.group uu____5104  in
            let uu____5118 = paren_if (ps || pb)  in uu____5118 uu____5103
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5123 =
              let uu____5124 =
                let uu____5125 =
                  let uu____5126 = str "let open"  in
                  let uu____5127 = p_quident uid  in
                  let uu____5128 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5126 uu____5127 uu____5128
                   in
                let uu____5129 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5125 uu____5129  in
              FStar_Pprint.group uu____5124  in
            let uu____5130 = paren_if ps  in uu____5130 uu____5123
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5186 is_last =
              match uu____5186 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5219 =
                          let uu____5220 = str "let"  in
                          let uu____5221 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5220 uu____5221
                           in
                        FStar_Pprint.group uu____5219
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5222 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5227 =
                    if is_last
                    then
                      let uu____5228 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5229 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5228 doc_expr uu____5229
                    else
                      (let uu____5231 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5231)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5227
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5277 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5277
                     else
                       (let uu____5285 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5285)) lbs
               in
            let lbs_doc =
              let uu____5293 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5293  in
            let uu____5294 =
              let uu____5295 =
                let uu____5296 =
                  let uu____5297 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5297
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5296  in
              FStar_Pprint.group uu____5295  in
            let uu____5298 = paren_if ps  in uu____5298 uu____5294
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5303;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5306;
                                                             FStar_Parser_AST.level
                                                               = uu____5307;_})
            when matches_var maybe_x x ->
            let uu____5334 =
              let uu____5335 =
                let uu____5336 = str "function"  in
                let uu____5337 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5336 uu____5337  in
              FStar_Pprint.group uu____5335  in
            let uu____5346 = paren_if (ps || pb)  in uu____5346 uu____5334
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5350 =
              let uu____5351 = str "quote"  in
              let uu____5352 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5351 uu____5352  in
            FStar_Pprint.group uu____5350
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5354 =
              let uu____5355 = str "`"  in
              let uu____5356 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5355 uu____5356  in
            FStar_Pprint.group uu____5354
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5358 =
              let uu____5359 = str "%`"  in
              let uu____5360 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5359 uu____5360  in
            FStar_Pprint.group uu____5358
        | uu____5361 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_5362  ->
    match uu___59_5362 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5374 =
          let uu____5375 = str "[@"  in
          let uu____5376 =
            let uu____5377 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5378 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5377 uu____5378  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5375 uu____5376  in
        FStar_Pprint.group uu____5374

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
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5404 =
                   let uu____5405 =
                     let uu____5406 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5406 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5405 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5404 term_doc
             | pats ->
                 let uu____5412 =
                   let uu____5413 =
                     let uu____5414 =
                       let uu____5415 =
                         let uu____5416 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5416
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5415 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5417 = p_trigger trigger  in
                     prefix2 uu____5414 uu____5417  in
                   FStar_Pprint.group uu____5413  in
                 prefix2 uu____5412 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5437 =
                   let uu____5438 =
                     let uu____5439 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5439 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5438 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5437 term_doc
             | pats ->
                 let uu____5445 =
                   let uu____5446 =
                     let uu____5447 =
                       let uu____5448 =
                         let uu____5449 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5449
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5448 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5450 = p_trigger trigger  in
                     prefix2 uu____5447 uu____5450  in
                   FStar_Pprint.group uu____5446  in
                 prefix2 uu____5445 term_doc)
        | uu____5451 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5453 -> str "forall"
    | FStar_Parser_AST.QExists uu____5466 -> str "exists"
    | uu____5479 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___60_5480  ->
    match uu___60_5480 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5492 =
          let uu____5493 =
            let uu____5494 =
              let uu____5495 = str "pattern"  in
              let uu____5496 =
                let uu____5497 =
                  let uu____5498 = p_disjunctivePats pats  in
                  jump2 uu____5498  in
                FStar_Pprint.op_Hat_Hat uu____5497 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5495 uu____5496  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5494  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5493  in
        FStar_Pprint.group uu____5492

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5504 = str "\\/"  in
    FStar_Pprint.separate_map uu____5504 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5510 =
      let uu____5511 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5511 p_appTerm pats  in
    FStar_Pprint.group uu____5510

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5521 =
              let uu____5522 =
                let uu____5523 = str "fun"  in
                let uu____5524 =
                  let uu____5525 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5525
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5523 uu____5524  in
              let uu____5526 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5522 uu____5526  in
            let uu____5527 = paren_if ps  in uu____5527 uu____5521
        | uu____5530 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5534  ->
      match uu____5534 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5555 =
                    let uu____5556 =
                      let uu____5557 =
                        let uu____5558 = p_tuplePattern p  in
                        let uu____5559 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5558 uu____5559  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5557
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5556  in
                  FStar_Pprint.group uu____5555
              | FStar_Pervasives_Native.Some f ->
                  let uu____5561 =
                    let uu____5562 =
                      let uu____5563 =
                        let uu____5564 =
                          let uu____5565 =
                            let uu____5566 = p_tuplePattern p  in
                            let uu____5567 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5566
                              uu____5567
                             in
                          FStar_Pprint.group uu____5565  in
                        let uu____5568 =
                          let uu____5569 =
                            let uu____5572 = p_tmFormula f  in
                            [uu____5572; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5569  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5564 uu____5568
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5563
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5562  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5561
               in
            let uu____5573 =
              let uu____5574 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5574  in
            FStar_Pprint.group uu____5573  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5583 =
                      let uu____5584 =
                        let uu____5585 =
                          let uu____5586 =
                            let uu____5587 =
                              let uu____5588 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5588  in
                            FStar_Pprint.separate_map uu____5587
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5586
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5585
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5584  in
                    FStar_Pprint.group uu____5583
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5589 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5591;_},e1::e2::[])
        ->
        let uu____5596 = str "<==>"  in
        let uu____5597 = p_tmImplies e1  in
        let uu____5598 = p_tmIff e2  in
        infix0 uu____5596 uu____5597 uu____5598
    | uu____5599 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5601;_},e1::e2::[])
        ->
        let uu____5606 = str "==>"  in
        let uu____5607 = p_tmArrow p_tmFormula e1  in
        let uu____5608 = p_tmImplies e2  in
        infix0 uu____5606 uu____5607 uu____5608
    | uu____5609 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5617 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5617 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_31 when _0_31 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5638 ->
               let uu____5639 =
                 let uu____5640 =
                   let uu____5641 =
                     let uu____5642 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5642
                      in
                   FStar_Pprint.separate uu____5641 terms  in
                 let uu____5643 =
                   let uu____5644 =
                     let uu____5645 =
                       let uu____5646 =
                         let uu____5647 =
                           let uu____5648 =
                             let uu____5649 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5649
                              in
                           FStar_Pprint.separate uu____5648 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5647 last_op  in
                       let uu____5650 =
                         let uu____5651 =
                           let uu____5652 =
                             let uu____5653 =
                               let uu____5654 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5654
                                in
                             FStar_Pprint.separate uu____5653 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5652 last_op  in
                         jump2 uu____5651  in
                       FStar_Pprint.ifflat uu____5646 uu____5650  in
                     FStar_Pprint.group uu____5645  in
                   let uu____5655 = FStar_List.hd last1  in
                   prefix2 uu____5644 uu____5655  in
                 FStar_Pprint.ifflat uu____5640 uu____5643  in
               FStar_Pprint.group uu____5639)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5668 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5673 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5668 uu____5673
      | uu____5676 -> let uu____5677 = p_Tm e  in [uu____5677]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5680 =
        let uu____5681 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5681 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5680  in
    let disj =
      let uu____5683 =
        let uu____5684 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5684 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5683  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5703;_},e1::e2::[])
        ->
        let uu____5708 = p_tmDisjunction e1  in
        let uu____5713 = let uu____5718 = p_tmConjunction e2  in [uu____5718]
           in
        FStar_List.append uu____5708 uu____5713
    | uu____5727 -> let uu____5728 = p_tmConjunction e  in [uu____5728]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5738;_},e1::e2::[])
        ->
        let uu____5743 = p_tmConjunction e1  in
        let uu____5746 = let uu____5749 = p_tmTuple e2  in [uu____5749]  in
        FStar_List.append uu____5743 uu____5746
    | uu____5750 -> let uu____5751 = p_tmTuple e  in [uu____5751]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5768 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5768
          (fun uu____5776  ->
             match uu____5776 with | (e1,uu____5782) -> p_tmEq e1) args
    | uu____5783 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5788 =
             let uu____5789 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5789  in
           FStar_Pprint.group uu____5788)

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
            let uu____5852 = levels op1  in
            (match uu____5852 with
             | (left1,mine,right1) ->
                 let uu____5862 =
                   let uu____5863 = FStar_All.pipe_left str op1  in
                   let uu____5864 = p_tmEqWith' p_X left1 e1  in
                   let uu____5865 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5863 uu____5864 uu____5865  in
                 paren_if_gt curr mine uu____5862)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5866;_},e1::e2::[])
            ->
            let uu____5871 =
              let uu____5872 = p_tmEqWith p_X e1  in
              let uu____5873 =
                let uu____5874 =
                  let uu____5875 =
                    let uu____5876 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5876  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5875  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5874  in
              FStar_Pprint.op_Hat_Hat uu____5872 uu____5873  in
            FStar_Pprint.group uu____5871
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5877;_},e1::[])
            ->
            let uu____5881 = levels "-"  in
            (match uu____5881 with
             | (left1,mine,right1) ->
                 let uu____5891 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5891)
        | uu____5892 -> p_tmNoEqWith p_X e

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
            (lid,(e1,uu____5963)::(e2,uu____5965)::[]) when
            (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
              (let uu____5985 = is_list e  in Prims.op_Negation uu____5985)
            ->
            let op = "::"  in
            let uu____5987 = levels op  in
            (match uu____5987 with
             | (left1,mine,right1) ->
                 let uu____5997 =
                   let uu____5998 = str op  in
                   let uu____5999 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6000 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____5998 uu____5999 uu____6000  in
                 paren_if_gt curr mine uu____5997)
        | FStar_Parser_AST.Sum (binders,res) ->
            let op = "&"  in
            let uu____6008 = levels op  in
            (match uu____6008 with
             | (left1,mine,right1) ->
                 let p_dsumfst b =
                   let uu____6022 = p_binder false b  in
                   let uu____6023 =
                     let uu____6024 =
                       let uu____6025 = str op  in
                       FStar_Pprint.op_Hat_Hat uu____6025 break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6024
                      in
                   FStar_Pprint.op_Hat_Hat uu____6022 uu____6023  in
                 let uu____6026 =
                   let uu____6027 = FStar_Pprint.concat_map p_dsumfst binders
                      in
                   let uu____6028 = p_tmNoEqWith' p_X right1 res  in
                   FStar_Pprint.op_Hat_Hat uu____6027 uu____6028  in
                 paren_if_gt curr mine uu____6026)
        | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
            let op1 = FStar_Ident.text_of_id op  in
            let uu____6035 = levels op1  in
            (match uu____6035 with
             | (left1,mine,right1) ->
                 let uu____6045 =
                   let uu____6046 = str op1  in
                   let uu____6047 = p_tmNoEqWith' p_X left1 e1  in
                   let uu____6048 = p_tmNoEqWith' p_X right1 e2  in
                   infix0 uu____6046 uu____6047 uu____6048  in
                 paren_if_gt curr mine uu____6045)
        | FStar_Parser_AST.Record (with_opt,record_fields) ->
            let uu____6067 =
              let uu____6068 =
                default_or_map FStar_Pprint.empty p_with_clause with_opt  in
              let uu____6069 =
                let uu____6070 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____6070 p_simpleDef record_fields  in
              FStar_Pprint.op_Hat_Hat uu____6068 uu____6069  in
            braces_with_nesting uu____6067
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "~"; FStar_Ident.idRange = uu____6075;_},e1::[])
            ->
            let uu____6079 =
              let uu____6080 = str "~"  in
              let uu____6081 = p_atomicTerm e1  in
              FStar_Pprint.op_Hat_Hat uu____6080 uu____6081  in
            FStar_Pprint.group uu____6079
        | uu____6082 -> p_X e

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
        let uu____6089 =
          let uu____6090 = p_lident lid  in
          let uu____6091 =
            let uu____6092 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6092  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6090 uu____6091  in
        FStar_Pprint.group uu____6089
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6095 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6097 = p_appTerm e  in
    let uu____6098 =
      let uu____6099 =
        let uu____6100 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6100 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6099  in
    FStar_Pprint.op_Hat_Hat uu____6097 uu____6098

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6105 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6105 t phi
      | FStar_Parser_AST.TAnnotated uu____6106 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6111 ->
          let uu____6112 =
            let uu____6113 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6113
             in
          failwith uu____6112
      | FStar_Parser_AST.TVariable uu____6114 ->
          let uu____6115 =
            let uu____6116 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6116
             in
          failwith uu____6115
      | FStar_Parser_AST.NoName uu____6117 ->
          let uu____6118 =
            let uu____6119 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6119
             in
          failwith uu____6118

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6121  ->
      match uu____6121 with
      | (lid,e) ->
          let uu____6128 =
            let uu____6129 = p_qlident lid  in
            let uu____6130 =
              let uu____6131 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6131
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6129 uu____6130  in
          FStar_Pprint.group uu____6128

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6133 when is_general_application e ->
        let uu____6140 = head_and_args e  in
        (match uu____6140 with
         | (head1,args) ->
             let uu____6165 =
               let uu____6176 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6176
               then
                 let uu____6206 =
                   FStar_Util.take
                     (fun uu____6230  ->
                        match uu____6230 with
                        | (uu____6235,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6206 with
                 | (fs_typ_args,args1) ->
                     let uu____6273 =
                       let uu____6274 = p_indexingTerm head1  in
                       let uu____6275 =
                         let uu____6276 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6276 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6274 uu____6275  in
                     (uu____6273, args1)
               else
                 (let uu____6288 = p_indexingTerm head1  in
                  (uu____6288, args))
                in
             (match uu____6165 with
              | (head_doc,args1) ->
                  let uu____6309 =
                    let uu____6310 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6310 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6309))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6330 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6330)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6348 =
               let uu____6349 = p_quident lid  in
               let uu____6350 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6349 uu____6350  in
             FStar_Pprint.group uu____6348
         | hd1::tl1 ->
             let uu____6367 =
               let uu____6368 =
                 let uu____6369 =
                   let uu____6370 = p_quident lid  in
                   let uu____6371 = p_argTerm hd1  in
                   prefix2 uu____6370 uu____6371  in
                 FStar_Pprint.group uu____6369  in
               let uu____6372 =
                 let uu____6373 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6373  in
               FStar_Pprint.op_Hat_Hat uu____6368 uu____6372  in
             FStar_Pprint.group uu____6367)
    | uu____6378 -> p_indexingTerm e

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
         (let uu____6387 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6387 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6389 = str "#"  in
        let uu____6390 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6389 uu____6390
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6392  ->
    match uu____6392 with | (e,uu____6398) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6403;_},e1::e2::[])
          ->
          let uu____6408 =
            let uu____6409 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6410 =
              let uu____6411 =
                let uu____6412 = p_term false false e2  in
                soft_parens_with_nesting uu____6412  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6411  in
            FStar_Pprint.op_Hat_Hat uu____6409 uu____6410  in
          FStar_Pprint.group uu____6408
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6413;_},e1::e2::[])
          ->
          let uu____6418 =
            let uu____6419 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6420 =
              let uu____6421 =
                let uu____6422 = p_term false false e2  in
                soft_brackets_with_nesting uu____6422  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6421  in
            FStar_Pprint.op_Hat_Hat uu____6419 uu____6420  in
          FStar_Pprint.group uu____6418
      | uu____6423 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6428 = p_quident lid  in
        let uu____6429 =
          let uu____6430 =
            let uu____6431 = p_term false false e1  in
            soft_parens_with_nesting uu____6431  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6430  in
        FStar_Pprint.op_Hat_Hat uu____6428 uu____6429
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6437 = str (FStar_Ident.text_of_id op)  in
        let uu____6438 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6437 uu____6438
    | uu____6439 -> p_atomicTermNotQUident e

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
         | uu____6446 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6453 = str (FStar_Ident.text_of_id op)  in
        let uu____6454 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6453 uu____6454
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6458 =
          let uu____6459 =
            let uu____6460 = str (FStar_Ident.text_of_id op)  in
            let uu____6461 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6460 uu____6461  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6459  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6458
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6476 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6477 =
          let uu____6478 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6479 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6478 p_tmEq uu____6479  in
        let uu____6486 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6476 uu____6477 uu____6486
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6489 =
          let uu____6490 = p_atomicTermNotQUident e1  in
          let uu____6491 =
            let uu____6492 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6492  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6490 uu____6491
           in
        FStar_Pprint.group uu____6489
    | uu____6493 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6498 = p_quident constr_lid  in
        let uu____6499 =
          let uu____6500 =
            let uu____6501 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6501  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6500  in
        FStar_Pprint.op_Hat_Hat uu____6498 uu____6499
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6503 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6503 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6505 = p_term false false e1  in
        soft_parens_with_nesting uu____6505
    | uu____6506 when is_array e ->
        let es = extract_from_list e  in
        let uu____6510 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6511 =
          let uu____6512 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6512
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6515 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6510 uu____6511 uu____6515
    | uu____6516 when is_list e ->
        let uu____6517 =
          let uu____6518 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6519 = extract_from_list e  in
          separate_map_or_flow_last uu____6518
            (fun ps  -> p_noSeqTerm ps false) uu____6519
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6517 FStar_Pprint.rbracket
    | uu____6524 when is_lex_list e ->
        let uu____6525 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6526 =
          let uu____6527 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6528 = extract_from_list e  in
          separate_map_or_flow_last uu____6527
            (fun ps  -> p_noSeqTerm ps false) uu____6528
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6525 uu____6526 FStar_Pprint.rbracket
    | uu____6533 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6537 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6538 =
          let uu____6539 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6539 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6537 uu____6538 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6543 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6544 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6543 uu____6544
    | FStar_Parser_AST.Op (op,args) when
        let uu____6551 = handleable_op op args  in
        Prims.op_Negation uu____6551 ->
        let uu____6552 =
          let uu____6553 =
            let uu____6554 =
              let uu____6555 =
                let uu____6556 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6556
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6555  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6554  in
          Prims.strcat "Operation " uu____6553  in
        failwith uu____6552
    | FStar_Parser_AST.Uvar uu____6557 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6558 = p_term false false e  in
        soft_parens_with_nesting uu____6558
    | FStar_Parser_AST.Const uu____6559 ->
        let uu____6560 = p_term false false e  in
        soft_parens_with_nesting uu____6560
    | FStar_Parser_AST.Op uu____6561 ->
        let uu____6568 = p_term false false e  in
        soft_parens_with_nesting uu____6568
    | FStar_Parser_AST.Tvar uu____6569 ->
        let uu____6570 = p_term false false e  in
        soft_parens_with_nesting uu____6570
    | FStar_Parser_AST.Var uu____6571 ->
        let uu____6572 = p_term false false e  in
        soft_parens_with_nesting uu____6572
    | FStar_Parser_AST.Name uu____6573 ->
        let uu____6574 = p_term false false e  in
        soft_parens_with_nesting uu____6574
    | FStar_Parser_AST.Construct uu____6575 ->
        let uu____6586 = p_term false false e  in
        soft_parens_with_nesting uu____6586
    | FStar_Parser_AST.Abs uu____6587 ->
        let uu____6594 = p_term false false e  in
        soft_parens_with_nesting uu____6594
    | FStar_Parser_AST.App uu____6595 ->
        let uu____6602 = p_term false false e  in
        soft_parens_with_nesting uu____6602
    | FStar_Parser_AST.Let uu____6603 ->
        let uu____6624 = p_term false false e  in
        soft_parens_with_nesting uu____6624
    | FStar_Parser_AST.LetOpen uu____6625 ->
        let uu____6630 = p_term false false e  in
        soft_parens_with_nesting uu____6630
    | FStar_Parser_AST.Seq uu____6631 ->
        let uu____6636 = p_term false false e  in
        soft_parens_with_nesting uu____6636
    | FStar_Parser_AST.Bind uu____6637 ->
        let uu____6644 = p_term false false e  in
        soft_parens_with_nesting uu____6644
    | FStar_Parser_AST.If uu____6645 ->
        let uu____6652 = p_term false false e  in
        soft_parens_with_nesting uu____6652
    | FStar_Parser_AST.Match uu____6653 ->
        let uu____6668 = p_term false false e  in
        soft_parens_with_nesting uu____6668
    | FStar_Parser_AST.TryWith uu____6669 ->
        let uu____6684 = p_term false false e  in
        soft_parens_with_nesting uu____6684
    | FStar_Parser_AST.Ascribed uu____6685 ->
        let uu____6694 = p_term false false e  in
        soft_parens_with_nesting uu____6694
    | FStar_Parser_AST.Record uu____6695 ->
        let uu____6708 = p_term false false e  in
        soft_parens_with_nesting uu____6708
    | FStar_Parser_AST.Project uu____6709 ->
        let uu____6714 = p_term false false e  in
        soft_parens_with_nesting uu____6714
    | FStar_Parser_AST.Product uu____6715 ->
        let uu____6722 = p_term false false e  in
        soft_parens_with_nesting uu____6722
    | FStar_Parser_AST.Sum uu____6723 ->
        let uu____6730 = p_term false false e  in
        soft_parens_with_nesting uu____6730
    | FStar_Parser_AST.QForall uu____6731 ->
        let uu____6744 = p_term false false e  in
        soft_parens_with_nesting uu____6744
    | FStar_Parser_AST.QExists uu____6745 ->
        let uu____6758 = p_term false false e  in
        soft_parens_with_nesting uu____6758
    | FStar_Parser_AST.Refine uu____6759 ->
        let uu____6764 = p_term false false e  in
        soft_parens_with_nesting uu____6764
    | FStar_Parser_AST.NamedTyp uu____6765 ->
        let uu____6770 = p_term false false e  in
        soft_parens_with_nesting uu____6770
    | FStar_Parser_AST.Requires uu____6771 ->
        let uu____6778 = p_term false false e  in
        soft_parens_with_nesting uu____6778
    | FStar_Parser_AST.Ensures uu____6779 ->
        let uu____6786 = p_term false false e  in
        soft_parens_with_nesting uu____6786
    | FStar_Parser_AST.Attributes uu____6787 ->
        let uu____6790 = p_term false false e  in
        soft_parens_with_nesting uu____6790
    | FStar_Parser_AST.Quote uu____6791 ->
        let uu____6796 = p_term false false e  in
        soft_parens_with_nesting uu____6796
    | FStar_Parser_AST.VQuote uu____6797 ->
        let uu____6798 = p_term false false e  in
        soft_parens_with_nesting uu____6798

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___63_6799  ->
    match uu___63_6799 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x ->
        let uu____6803 = FStar_Pprint.doc_of_char x  in
        FStar_Pprint.squotes uu____6803
    | FStar_Const.Const_string (s,uu____6805) ->
        let uu____6806 = str s  in FStar_Pprint.dquotes uu____6806
    | FStar_Const.Const_bytearray (bytes,uu____6808) ->
        let uu____6813 =
          let uu____6814 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6814  in
        let uu____6815 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6813 uu____6815
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___61_6833 =
          match uu___61_6833 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___62_6837 =
          match uu___62_6837 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6848  ->
               match uu____6848 with
               | (s,w) ->
                   let uu____6855 = signedness s  in
                   let uu____6856 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6855 uu____6856)
            sign_width_opt
           in
        let uu____6857 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6857 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6859 = FStar_Range.string_of_range r  in str uu____6859
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6861 = p_quident lid  in
        let uu____6862 =
          let uu____6863 =
            let uu____6864 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6864  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6863  in
        FStar_Pprint.op_Hat_Hat uu____6861 uu____6862

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6866 = str "u#"  in
    let uu____6867 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6866 uu____6867

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6869;_},u1::u2::[])
        ->
        let uu____6874 =
          let uu____6875 = p_universeFrom u1  in
          let uu____6876 =
            let uu____6877 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6877  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6875 uu____6876  in
        FStar_Pprint.group uu____6874
    | FStar_Parser_AST.App uu____6878 ->
        let uu____6885 = head_and_args u  in
        (match uu____6885 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6911 =
                    let uu____6912 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6913 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6921  ->
                           match uu____6921 with
                           | (u1,uu____6927) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6912 uu____6913  in
                  FStar_Pprint.group uu____6911
              | uu____6928 ->
                  let uu____6929 =
                    let uu____6930 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6930
                     in
                  failwith uu____6929))
    | uu____6931 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____6955 = p_universeFrom u1  in
        soft_parens_with_nesting uu____6955
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6956;_},uu____6957::uu____6958::[])
        ->
        let uu____6961 = p_universeFrom u  in
        soft_parens_with_nesting uu____6961
    | FStar_Parser_AST.App uu____6962 ->
        let uu____6969 = p_universeFrom u  in
        soft_parens_with_nesting uu____6969
    | uu____6970 ->
        let uu____6971 =
          let uu____6972 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____6972
           in
        failwith uu____6971

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
       | FStar_Parser_AST.Module (uu____7012,decls) ->
           let uu____7018 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7018
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7027,decls,uu____7029) ->
           let uu____7034 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7034
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7085  ->
         match uu____7085 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7125,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7131,decls,uu____7133) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7178 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7191;
                 FStar_Parser_AST.doc = uu____7192;
                 FStar_Parser_AST.quals = uu____7193;
                 FStar_Parser_AST.attrs = uu____7194;_}::uu____7195 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7201 =
                   let uu____7204 =
                     let uu____7207 = FStar_List.tl ds  in d :: uu____7207
                      in
                   d0 :: uu____7204  in
                 (uu____7201, (d0.FStar_Parser_AST.drange))
             | uu____7212 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7178 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7270 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7270 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7366 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7366, comments1))))))
  