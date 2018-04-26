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
         (id1,uu____3517)) ->
          let uu____3520 =
            let uu____3521 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3521 FStar_Util.is_upper  in
          if uu____3520
          then
            let uu____3522 = p_qualifier FStar_Parser_AST.Assumption  in
            FStar_Pprint.op_Hat_Hat uu____3522 FStar_Pprint.space
          else p_qualifiers d.FStar_Parser_AST.quals
      | uu____3524 -> p_qualifiers d.FStar_Parser_AST.quals  in
    let uu____3529 = FStar_Pprint.optional p_fsdoc d.FStar_Parser_AST.doc  in
    let uu____3530 =
      let uu____3531 = p_attributes d.FStar_Parser_AST.attrs  in
      let uu____3532 =
        let uu____3533 = p_rawDecl d  in
        FStar_Pprint.op_Hat_Hat qualifiers uu____3533  in
      FStar_Pprint.op_Hat_Hat uu____3531 uu____3532  in
    FStar_Pprint.op_Hat_Hat uu____3529 uu____3530

and (p_attributes : FStar_Parser_AST.attributes_ -> FStar_Pprint.document) =
  fun attrs  ->
    match attrs with
    | [] -> FStar_Pprint.empty
    | uu____3535 ->
        let uu____3536 =
          let uu____3537 = str "@ "  in
          let uu____3538 =
            let uu____3539 =
              let uu____3540 =
                let uu____3541 =
                  let uu____3542 = FStar_List.map p_atomicTerm attrs  in
                  FStar_Pprint.flow break1 uu____3542  in
                FStar_Pprint.op_Hat_Hat uu____3541 FStar_Pprint.rbracket  in
              FStar_Pprint.align uu____3540  in
            FStar_Pprint.op_Hat_Hat uu____3539 FStar_Pprint.hardline  in
          FStar_Pprint.op_Hat_Hat uu____3537 uu____3538  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket uu____3536

and (p_fsdoc : FStar_Parser_AST.fsdoc -> FStar_Pprint.document) =
  fun uu____3545  ->
    match uu____3545 with
    | (doc1,kwd_args) ->
        let kwd_args_doc =
          match kwd_args with
          | [] -> FStar_Pprint.empty
          | kwd_args1 ->
              let process_kwd_arg uu____3579 =
                match uu____3579 with
                | (kwd,arg) ->
                    let uu____3586 = str "@"  in
                    let uu____3587 =
                      let uu____3588 = str kwd  in
                      let uu____3589 =
                        let uu____3590 = str arg  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3590
                         in
                      FStar_Pprint.op_Hat_Hat uu____3588 uu____3589  in
                    FStar_Pprint.op_Hat_Hat uu____3586 uu____3587
                 in
              let uu____3591 =
                let uu____3592 =
                  FStar_Pprint.separate_map FStar_Pprint.hardline
                    process_kwd_arg kwd_args1
                   in
                FStar_Pprint.op_Hat_Hat uu____3592 FStar_Pprint.hardline  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3591
           in
        let uu____3597 =
          let uu____3598 =
            let uu____3599 =
              let uu____3600 =
                let uu____3601 = str doc1  in
                let uu____3602 =
                  let uu____3603 =
                    let uu____3604 =
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.rparen
                        FStar_Pprint.hardline
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3604  in
                  FStar_Pprint.op_Hat_Hat kwd_args_doc uu____3603  in
                FStar_Pprint.op_Hat_Hat uu____3601 uu____3602  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3600  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.star uu____3599  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____3598  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____3597

and (p_justSig : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3608 =
          let uu____3609 = str "val"  in
          let uu____3610 =
            let uu____3611 =
              let uu____3612 = p_lident lid  in
              let uu____3613 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.colon
                 in
              FStar_Pprint.op_Hat_Hat uu____3612 uu____3613  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3611  in
          FStar_Pprint.op_Hat_Hat uu____3609 uu____3610  in
        let uu____3614 = p_typ false false t  in
        FStar_Pprint.op_Hat_Hat uu____3608 uu____3614
    | FStar_Parser_AST.TopLevelLet (uu____3615,lbs) ->
        FStar_Pprint.separate_map FStar_Pprint.hardline
          (fun lb  ->
             let uu____3640 =
               let uu____3641 = str "let"  in p_letlhs uu____3641 lb  in
             FStar_Pprint.group uu____3640) lbs
    | uu____3642 -> FStar_Pprint.empty

and (p_rawDecl : FStar_Parser_AST.decl -> FStar_Pprint.document) =
  fun d  ->
    match d.FStar_Parser_AST.d with
    | FStar_Parser_AST.Open uid ->
        let uu____3645 =
          let uu____3646 = str "open"  in
          let uu____3647 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3646 uu____3647  in
        FStar_Pprint.group uu____3645
    | FStar_Parser_AST.Include uid ->
        let uu____3649 =
          let uu____3650 = str "include"  in
          let uu____3651 = p_quident uid  in
          FStar_Pprint.op_Hat_Slash_Hat uu____3650 uu____3651  in
        FStar_Pprint.group uu____3649
    | FStar_Parser_AST.ModuleAbbrev (uid1,uid2) ->
        let uu____3654 =
          let uu____3655 = str "module"  in
          let uu____3656 =
            let uu____3657 =
              let uu____3658 = p_uident uid1  in
              let uu____3659 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____3658 uu____3659  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3657  in
          FStar_Pprint.op_Hat_Hat uu____3655 uu____3656  in
        let uu____3660 = p_quident uid2  in
        op_Hat_Slash_Plus_Hat uu____3654 uu____3660
    | FStar_Parser_AST.TopLevelModule uid ->
        let uu____3662 =
          let uu____3663 = str "module"  in
          let uu____3664 =
            let uu____3665 = p_quident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3665  in
          FStar_Pprint.op_Hat_Hat uu____3663 uu____3664  in
        FStar_Pprint.group uu____3662
    | FStar_Parser_AST.Tycon
        (true
         ,(FStar_Parser_AST.TyconAbbrev
           (uid,tpars,FStar_Pervasives_Native.None ,t),FStar_Pervasives_Native.None
           )::[])
        ->
        let effect_prefix_doc =
          let uu____3698 = str "effect"  in
          let uu____3699 =
            let uu____3700 = p_uident uid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3700  in
          FStar_Pprint.op_Hat_Hat uu____3698 uu____3699  in
        let uu____3701 =
          let uu____3702 = p_typars tpars  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            effect_prefix_doc uu____3702 FStar_Pprint.equals
           in
        let uu____3703 = p_typ false false t  in
        op_Hat_Slash_Plus_Hat uu____3701 uu____3703
    | FStar_Parser_AST.Tycon (false ,tcdefs) ->
        let uu____3721 =
          let uu____3722 = str "type"  in
          let uu____3723 = FStar_List.hd tcdefs  in
          p_fsdocTypeDeclPairs uu____3722 uu____3723  in
        let uu____3736 =
          let uu____3737 = FStar_List.tl tcdefs  in
          FStar_All.pipe_left
            (FStar_Pprint.concat_map
               (fun x  ->
                  let uu____3775 =
                    let uu____3776 = str "and"  in
                    p_fsdocTypeDeclPairs uu____3776 x  in
                  FStar_Pprint.op_Hat_Hat break1 uu____3775)) uu____3737
           in
        FStar_Pprint.op_Hat_Hat uu____3721 uu____3736
    | FStar_Parser_AST.TopLevelLet (q,lbs) ->
        let let_doc =
          let uu____3792 = str "let"  in
          let uu____3793 = p_letqualifier q  in
          FStar_Pprint.op_Hat_Hat uu____3792 uu____3793  in
        let uu____3794 = str "and"  in
        separate_map_with_comments_kw let_doc uu____3794 p_letbinding lbs
          (fun uu____3802  ->
             match uu____3802 with
             | (p,t) ->
                 FStar_Range.union_ranges p.FStar_Parser_AST.prange
                   t.FStar_Parser_AST.range)
    | FStar_Parser_AST.Val (lid,t) ->
        let uu____3811 = str "val"  in
        let uu____3812 =
          let uu____3813 =
            let uu____3814 = p_lident lid  in
            let uu____3815 =
              let uu____3816 =
                let uu____3817 =
                  let uu____3818 = p_typ false false t  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3818  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3817  in
              FStar_Pprint.group uu____3816  in
            FStar_Pprint.op_Hat_Hat uu____3814 uu____3815  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3813  in
        FStar_Pprint.op_Hat_Hat uu____3811 uu____3812
    | FStar_Parser_AST.Assume (id1,t) ->
        let decl_keyword =
          let uu____3822 =
            let uu____3823 =
              FStar_Util.char_at id1.FStar_Ident.idText (Prims.parse_int "0")
               in
            FStar_All.pipe_right uu____3823 FStar_Util.is_upper  in
          if uu____3822
          then FStar_Pprint.empty
          else
            (let uu____3825 = str "val"  in
             FStar_Pprint.op_Hat_Hat uu____3825 FStar_Pprint.space)
           in
        let uu____3826 =
          let uu____3827 = p_ident id1  in
          let uu____3828 =
            let uu____3829 =
              let uu____3830 =
                let uu____3831 = p_typ false false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3831  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____3830  in
            FStar_Pprint.group uu____3829  in
          FStar_Pprint.op_Hat_Hat uu____3827 uu____3828  in
        FStar_Pprint.op_Hat_Hat decl_keyword uu____3826
    | FStar_Parser_AST.Exception (uid,t_opt) ->
        let uu____3838 = str "exception"  in
        let uu____3839 =
          let uu____3840 =
            let uu____3841 = p_uident uid  in
            let uu____3842 =
              FStar_Pprint.optional
                (fun t  ->
                   let uu____3846 =
                     let uu____3847 = str "of"  in
                     let uu____3848 = p_typ false false t  in
                     op_Hat_Slash_Plus_Hat uu____3847 uu____3848  in
                   FStar_Pprint.op_Hat_Hat break1 uu____3846) t_opt
               in
            FStar_Pprint.op_Hat_Hat uu____3841 uu____3842  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3840  in
        FStar_Pprint.op_Hat_Hat uu____3838 uu____3839
    | FStar_Parser_AST.NewEffect ne ->
        let uu____3850 = str "new_effect"  in
        let uu____3851 =
          let uu____3852 = p_newEffect ne  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3852  in
        FStar_Pprint.op_Hat_Hat uu____3850 uu____3851
    | FStar_Parser_AST.SubEffect se ->
        let uu____3854 = str "sub_effect"  in
        let uu____3855 =
          let uu____3856 = p_subEffect se  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3856  in
        FStar_Pprint.op_Hat_Hat uu____3854 uu____3855
    | FStar_Parser_AST.Pragma p -> p_pragma p
    | FStar_Parser_AST.Fsdoc doc1 ->
        let uu____3859 = p_fsdoc doc1  in
        FStar_Pprint.op_Hat_Hat uu____3859 FStar_Pprint.hardline
    | FStar_Parser_AST.Main uu____3860 ->
        failwith "*Main declaration* : Is that really still in use ??"
    | FStar_Parser_AST.Tycon (true ,uu____3861) ->
        failwith
          "Effect abbreviation is expected to be defined by an abbreviation"
    | FStar_Parser_AST.Splice t ->
        let uu____3879 = str "%splice"  in
        let uu____3880 =
          let uu____3881 = p_term false false t  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3881  in
        FStar_Pprint.op_Hat_Hat uu____3879 uu____3880

and (p_pragma : FStar_Parser_AST.pragma -> FStar_Pprint.document) =
  fun uu___53_3882  ->
    match uu___53_3882 with
    | FStar_Parser_AST.SetOptions s ->
        let uu____3884 = str "#set-options"  in
        let uu____3885 =
          let uu____3886 =
            let uu____3887 = str s  in FStar_Pprint.dquotes uu____3887  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3886  in
        FStar_Pprint.op_Hat_Hat uu____3884 uu____3885
    | FStar_Parser_AST.ResetOptions s_opt ->
        let uu____3891 = str "#reset-options"  in
        let uu____3892 =
          FStar_Pprint.optional
            (fun s  ->
               let uu____3896 =
                 let uu____3897 = str s  in FStar_Pprint.dquotes uu____3897
                  in
               FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____3896) s_opt
           in
        FStar_Pprint.op_Hat_Hat uu____3891 uu____3892
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
    fun uu____3922  ->
      match uu____3922 with
      | (typedecl,fsdoc_opt) ->
          let uu____3935 = p_typeDecl (kw, fsdoc_opt) typedecl  in
          (match uu____3935 with
           | (decl,body) ->
               let uu____3950 = body ()  in
               FStar_Pprint.op_Hat_Hat decl uu____3950)

and (p_typeDecl :
  (FStar_Pprint.document,FStar_Parser_AST.fsdoc
                           FStar_Pervasives_Native.option)
    FStar_Pervasives_Native.tuple2 ->
    FStar_Parser_AST.tycon ->
      (FStar_Pprint.document,Prims.unit -> FStar_Pprint.document)
        FStar_Pervasives_Native.tuple2)
  =
  fun pre  ->
    fun uu___54_3952  ->
      match uu___54_3952 with
      | FStar_Parser_AST.TyconAbstract (lid,bs,typ_opt) ->
          let empty' uu____3979 = FStar_Pprint.empty  in
          let uu____3980 = p_typeDeclPrefix pre false lid bs typ_opt  in
          (uu____3980, empty')
      | FStar_Parser_AST.TyconAbbrev (lid,bs,typ_opt,t) ->
          let f uu____3998 =
            let uu____3999 = p_typ false false t  in jump2 uu____3999  in
          let uu____4000 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4000, f)
      | FStar_Parser_AST.TyconRecord (lid,bs,typ_opt,record_field_decls) ->
          let p_recordFieldAndComments ps uu____4049 =
            match uu____4049 with
            | (lid1,t,doc_opt) ->
                let uu____4065 =
                  FStar_Range.extend_to_end_of_line t.FStar_Parser_AST.range
                   in
                with_comment (p_recordFieldDecl ps) (lid1, t, doc_opt)
                  uu____4065
             in
          let p_fields uu____4079 =
            let uu____4080 =
              let uu____4081 =
                let uu____4082 =
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                separate_map_last uu____4082 p_recordFieldAndComments
                  record_field_decls
                 in
              braces_with_nesting uu____4081  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4080  in
          let uu____4091 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4091, p_fields)
      | FStar_Parser_AST.TyconVariant (lid,bs,typ_opt,ct_decls) ->
          let p_constructorBranchAndComments uu____4149 =
            match uu____4149 with
            | (uid,t_opt,doc_opt,use_of) ->
                let range =
                  let uu____4175 =
                    let uu____4176 =
                      FStar_Util.map_opt t_opt
                        (fun t  -> t.FStar_Parser_AST.range)
                       in
                    FStar_Util.dflt uid.FStar_Ident.idRange uu____4176  in
                  FStar_Range.extend_to_end_of_line uu____4175  in
                with_comment p_constructorBranch
                  (uid, t_opt, doc_opt, use_of) range
             in
          let datacon_doc uu____4200 =
            FStar_Pprint.separate_map FStar_Pprint.hardline
              p_constructorBranchAndComments ct_decls
             in
          let uu____4213 = p_typeDeclPrefix pre true lid bs typ_opt  in
          (uu____4213,
            ((fun uu____4218  ->
                let uu____4219 = datacon_doc ()  in jump2 uu____4219)))

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
  fun uu____4220  ->
    fun eq1  ->
      fun lid  ->
        fun bs  ->
          fun typ_opt  ->
            match uu____4220 with
            | (kw,fsdoc_opt) ->
                let maybe_with_fsdoc cont =
                  let lid_doc = p_ident lid  in
                  let kw_lid =
                    let uu____4252 = FStar_Pprint.op_Hat_Slash_Hat kw lid_doc
                       in
                    FStar_Pprint.group uu____4252  in
                  match fsdoc_opt with
                  | FStar_Pervasives_Native.None  -> cont kw_lid
                  | FStar_Pervasives_Native.Some fsdoc ->
                      let uu____4254 =
                        let uu____4257 =
                          let uu____4260 = p_fsdoc fsdoc  in
                          let uu____4261 =
                            let uu____4264 = cont lid_doc  in [uu____4264]
                             in
                          uu____4260 :: uu____4261  in
                        kw :: uu____4257  in
                      FStar_Pprint.separate FStar_Pprint.hardline uu____4254
                   in
                let typ =
                  let maybe_eq =
                    if eq1 then FStar_Pprint.equals else FStar_Pprint.empty
                     in
                  match typ_opt with
                  | FStar_Pervasives_Native.None  -> maybe_eq
                  | FStar_Pervasives_Native.Some t ->
                      let uu____4269 =
                        let uu____4270 =
                          let uu____4271 = p_typ false false t  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____4271 maybe_eq
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4270
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4269
                   in
                if bs = []
                then maybe_with_fsdoc (fun n1  -> prefix2 n1 typ)
                else
                  (let binders = p_binders_list true bs  in
                   maybe_with_fsdoc
                     (fun n1  ->
                        let uu____4286 =
                          let uu____4287 = FStar_Pprint.flow break1 binders
                             in
                          prefix2 n1 uu____4287  in
                        prefix2 uu____4286 typ))

and (p_recordFieldDecl :
  Prims.bool ->
    (FStar_Ident.ident,FStar_Parser_AST.term,FStar_Parser_AST.fsdoc
                                               FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____4289  ->
      match uu____4289 with
      | (lid,t,doc_opt) ->
          let uu____4305 =
            let uu____4306 = FStar_Pprint.optional p_fsdoc doc_opt  in
            let uu____4307 =
              let uu____4308 = p_lident lid  in
              let uu____4309 =
                let uu____4310 = p_typ ps false t  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4310  in
              FStar_Pprint.op_Hat_Hat uu____4308 uu____4309  in
            FStar_Pprint.op_Hat_Hat uu____4306 uu____4307  in
          FStar_Pprint.group uu____4305

and (p_constructorBranch :
  (FStar_Ident.ident,FStar_Parser_AST.term FStar_Pervasives_Native.option,
    FStar_Parser_AST.fsdoc FStar_Pervasives_Native.option,Prims.bool)
    FStar_Pervasives_Native.tuple4 -> FStar_Pprint.document)
  =
  fun uu____4311  ->
    match uu____4311 with
    | (uid,t_opt,doc_opt,use_of) ->
        let sep = if use_of then str "of" else FStar_Pprint.colon  in
        let uid_doc =
          let uu____4339 =
            let uu____4340 =
              let uu____4341 = p_uident uid  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4341  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____4340  in
          FStar_Pprint.group uu____4339  in
        let uu____4342 = FStar_Pprint.optional p_fsdoc doc_opt  in
        let uu____4343 =
          default_or_map uid_doc
            (fun t  ->
               let uu____4347 =
                 let uu____4348 =
                   let uu____4349 =
                     let uu____4350 =
                       let uu____4351 = p_typ false false t  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4351
                        in
                     FStar_Pprint.op_Hat_Hat sep uu____4350  in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4349  in
                 FStar_Pprint.op_Hat_Hat uid_doc uu____4348  in
               FStar_Pprint.group uu____4347) t_opt
           in
        FStar_Pprint.op_Hat_Hat uu____4342 uu____4343

and (p_letlhs :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4353  ->
      match uu____4353 with
      | (pat,uu____4359) ->
          let uu____4360 =
            match pat.FStar_Parser_AST.pat with
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.None )) ->
                let uu____4379 =
                  let uu____4380 =
                    let uu____4381 =
                      let uu____4382 = p_tmArrow p_tmNoEq t  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4382
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4381  in
                  FStar_Pprint.group uu____4380  in
                (pat1, uu____4379)
            | FStar_Parser_AST.PatAscribed
                (pat1,(t,FStar_Pervasives_Native.Some tac)) ->
                let uu____4394 =
                  let uu____4395 =
                    let uu____4396 =
                      let uu____4397 =
                        let uu____4398 = p_tmArrow p_tmNoEq t  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4398
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____4397
                       in
                    FStar_Pprint.group uu____4396  in
                  let uu____4399 =
                    let uu____4400 =
                      let uu____4401 = str "by"  in
                      let uu____4402 =
                        let uu____4403 = p_atomicTerm tac  in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4403
                         in
                      FStar_Pprint.op_Hat_Hat uu____4401 uu____4402  in
                    FStar_Pprint.group uu____4400  in
                  FStar_Pprint.op_Hat_Hat uu____4395 uu____4399  in
                (pat1, uu____4394)
            | uu____4404 -> (pat, FStar_Pprint.empty)  in
          (match uu____4360 with
           | (pat1,ascr_doc) ->
               (match pat1.FStar_Parser_AST.pat with
                | FStar_Parser_AST.PatApp
                    ({
                       FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                         (x,uu____4408);
                       FStar_Parser_AST.prange = uu____4409;_},pats)
                    ->
                    let uu____4419 =
                      let uu____4420 =
                        let uu____4421 =
                          let uu____4422 = p_lident x  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4422  in
                        FStar_Pprint.group uu____4421  in
                      let uu____4423 =
                        FStar_Pprint.flow_map break1 p_atomicPattern pats  in
                      prefix2 uu____4420 uu____4423  in
                    prefix2_nonempty uu____4419 ascr_doc
                | uu____4424 ->
                    let uu____4425 =
                      let uu____4426 =
                        let uu____4427 =
                          let uu____4428 = p_tuplePattern pat1  in
                          FStar_Pprint.op_Hat_Slash_Hat kw uu____4428  in
                        FStar_Pprint.group uu____4427  in
                      FStar_Pprint.op_Hat_Hat uu____4426 ascr_doc  in
                    FStar_Pprint.group uu____4425))

and (p_letbinding :
  FStar_Pprint.document ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple2 -> FStar_Pprint.document)
  =
  fun kw  ->
    fun uu____4430  ->
      match uu____4430 with
      | (pat,e) ->
          let doc_pat = p_letlhs kw (pat, e)  in
          let doc_expr = p_term false false e  in
          let uu____4439 =
            let uu____4440 =
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals doc_expr  in
            FStar_Pprint.op_Hat_Slash_Hat doc_pat uu____4440  in
          let uu____4441 =
            let uu____4442 =
              let uu____4443 =
                let uu____4444 =
                  let uu____4445 = jump2 doc_expr  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.equals uu____4445  in
                FStar_Pprint.group uu____4444  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4443  in
            FStar_Pprint.op_Hat_Hat doc_pat uu____4442  in
          FStar_Pprint.ifflat uu____4439 uu____4441

and (p_newEffect : FStar_Parser_AST.effect_decl -> FStar_Pprint.document) =
  fun uu___55_4446  ->
    match uu___55_4446 with
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
        let uu____4471 = p_uident uid  in
        let uu____4472 = p_binders true bs  in
        let uu____4473 =
          let uu____4474 = p_simpleTerm false false t  in
          prefix2 FStar_Pprint.equals uu____4474  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4471 uu____4472 uu____4473

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
          let uu____4483 =
            let uu____4484 =
              let uu____4485 =
                let uu____4486 = p_uident uid  in
                let uu____4487 = p_binders true bs  in
                let uu____4488 =
                  let uu____4489 = p_typ false false t  in
                  prefix2 FStar_Pprint.colon uu____4489  in
                FStar_Pprint.surround (Prims.parse_int "2")
                  (Prims.parse_int "1") uu____4486 uu____4487 uu____4488
                 in
              FStar_Pprint.group uu____4485  in
            let uu____4490 =
              let uu____4491 = str "with"  in
              let uu____4492 =
                separate_break_map_last FStar_Pprint.semi p_effectDecl
                  eff_decls
                 in
              prefix2 uu____4491 uu____4492  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4484 uu____4490  in
          braces_with_nesting uu____4483

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
          let uu____4523 =
            let uu____4524 = p_lident lid  in
            let uu____4525 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.equals
               in
            FStar_Pprint.op_Hat_Hat uu____4524 uu____4525  in
          let uu____4526 = p_simpleTerm ps false e  in
          prefix2 uu____4523 uu____4526
      | uu____4527 ->
          let uu____4528 =
            let uu____4529 = FStar_Parser_AST.decl_to_string d  in
            FStar_Util.format1
              "Not a declaration of an effect member... or at least I hope so : %s"
              uu____4529
             in
          failwith uu____4528

and (p_subEffect : FStar_Parser_AST.lift -> FStar_Pprint.document) =
  fun lift  ->
    let lift_op_doc =
      let lifts =
        match lift.FStar_Parser_AST.lift_op with
        | FStar_Parser_AST.NonReifiableLift t -> [("lift_wp", t)]
        | FStar_Parser_AST.ReifiableLift (t1,t2) ->
            [("lift_wp", t1); ("lift", t2)]
        | FStar_Parser_AST.LiftForFree t -> [("lift", t)]  in
      let p_lift ps uu____4587 =
        match uu____4587 with
        | (kwd,t) ->
            let uu____4594 =
              let uu____4595 = str kwd  in
              let uu____4596 =
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                  FStar_Pprint.equals
                 in
              FStar_Pprint.op_Hat_Hat uu____4595 uu____4596  in
            let uu____4597 = p_simpleTerm ps false t  in
            prefix2 uu____4594 uu____4597
         in
      separate_break_map_last FStar_Pprint.semi p_lift lifts  in
    let uu____4602 =
      let uu____4603 =
        let uu____4604 = p_quident lift.FStar_Parser_AST.msource  in
        let uu____4605 =
          let uu____4606 = str "~>"  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4606  in
        FStar_Pprint.op_Hat_Hat uu____4604 uu____4605  in
      let uu____4607 = p_quident lift.FStar_Parser_AST.mdest  in
      prefix2 uu____4603 uu____4607  in
    let uu____4608 =
      let uu____4609 = braces_with_nesting lift_op_doc  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4609  in
    FStar_Pprint.op_Hat_Hat uu____4602 uu____4608

and (p_qualifier : FStar_Parser_AST.qualifier -> FStar_Pprint.document) =
  fun uu___56_4610  ->
    match uu___56_4610 with
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
    | uu____4612 ->
        let uu____4613 =
          let uu____4614 = FStar_List.map p_qualifier qs  in
          FStar_Pprint.flow break1 uu____4614  in
        FStar_Pprint.op_Hat_Hat uu____4613 FStar_Pprint.hardline

and (p_letqualifier :
  FStar_Parser_AST.let_qualifier -> FStar_Pprint.document) =
  fun uu___57_4617  ->
    match uu___57_4617 with
    | FStar_Parser_AST.Rec  ->
        let uu____4618 = str "rec"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4618
    | FStar_Parser_AST.Mutable  ->
        let uu____4619 = str "mutable"  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4619
    | FStar_Parser_AST.NoLetQualifier  -> FStar_Pprint.empty

and (p_aqual : FStar_Parser_AST.arg_qualifier -> FStar_Pprint.document) =
  fun uu___58_4620  ->
    match uu___58_4620 with
    | FStar_Parser_AST.Implicit  -> str "#"
    | FStar_Parser_AST.Equality  -> str "$"

and (p_disjunctivePattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatOr pats ->
        let uu____4625 =
          let uu____4626 =
            let uu____4627 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.space  in
            FStar_Pprint.op_Hat_Hat break1 uu____4627  in
          FStar_Pprint.separate_map uu____4626 p_tuplePattern pats  in
        FStar_Pprint.group uu____4625
    | uu____4628 -> p_tuplePattern p

and (p_tuplePattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatTuple (pats,false ) ->
        let uu____4635 =
          let uu____4636 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          FStar_Pprint.separate_map uu____4636 p_constructorPattern pats  in
        FStar_Pprint.group uu____4635
    | uu____4637 -> p_constructorPattern p

and (p_constructorPattern :
  FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName maybe_cons_lid;
           FStar_Parser_AST.prange = uu____4640;_},hd1::tl1::[])
        when
        FStar_Ident.lid_equals maybe_cons_lid FStar_Parser_Const.cons_lid ->
        let uu____4645 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.colon FStar_Pprint.colon  in
        let uu____4646 = p_constructorPattern hd1  in
        let uu____4647 = p_constructorPattern tl1  in
        infix0 uu____4645 uu____4646 uu____4647
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uid;
           FStar_Parser_AST.prange = uu____4649;_},pats)
        ->
        let uu____4655 = p_quident uid  in
        let uu____4656 =
          FStar_Pprint.separate_map break1 p_atomicPattern pats  in
        prefix2 uu____4655 uu____4656
    | uu____4657 -> p_atomicPattern p

and (p_atomicPattern : FStar_Parser_AST.pattern -> FStar_Pprint.document) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (pat,(t,FStar_Pervasives_Native.None )) ->
        (match ((pat.FStar_Parser_AST.pat), (t.FStar_Parser_AST.tm)) with
         | (FStar_Parser_AST.PatVar (lid,aqual),FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
               FStar_Parser_AST.brange = uu____4673;
               FStar_Parser_AST.blevel = uu____4674;
               FStar_Parser_AST.aqual = uu____4675;_},phi))
             when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
             let uu____4681 =
               let uu____4682 = p_ident lid  in
               p_refinement aqual uu____4682 t1 phi  in
             soft_parens_with_nesting uu____4681
         | (FStar_Parser_AST.PatWild ,FStar_Parser_AST.Refine
            ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
               FStar_Parser_AST.brange = uu____4684;
               FStar_Parser_AST.blevel = uu____4685;
               FStar_Parser_AST.aqual = uu____4686;_},phi))
             ->
             let uu____4688 =
               p_refinement FStar_Pervasives_Native.None
                 FStar_Pprint.underscore t1 phi
                in
             soft_parens_with_nesting uu____4688
         | uu____4689 ->
             let uu____4694 =
               let uu____4695 = p_tuplePattern pat  in
               let uu____4696 =
                 let uu____4697 = p_tmEqNoRefinement t  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4697
                  in
               FStar_Pprint.op_Hat_Hat uu____4695 uu____4696  in
             soft_parens_with_nesting uu____4694)
    | FStar_Parser_AST.PatList pats ->
        let uu____4701 =
          separate_break_map FStar_Pprint.semi p_tuplePattern pats  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____4701 FStar_Pprint.rbracket
    | FStar_Parser_AST.PatRecord pats ->
        let p_recordFieldPat uu____4716 =
          match uu____4716 with
          | (lid,pat) ->
              let uu____4723 = p_qlident lid  in
              let uu____4724 = p_tuplePattern pat  in
              infix2 FStar_Pprint.equals uu____4723 uu____4724
           in
        let uu____4725 =
          separate_break_map FStar_Pprint.semi p_recordFieldPat pats  in
        soft_braces_with_nesting uu____4725
    | FStar_Parser_AST.PatTuple (pats,true ) ->
        let uu____4735 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____4736 =
          separate_break_map FStar_Pprint.comma p_constructorPattern pats  in
        let uu____4737 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____4735 uu____4736 uu____4737
    | FStar_Parser_AST.PatTvar (tv,arg_qualifier_opt) -> p_tvar tv
    | FStar_Parser_AST.PatOp op ->
        let uu____4748 =
          let uu____4749 =
            let uu____4750 = str (FStar_Ident.text_of_id op)  in
            let uu____4751 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____4750 uu____4751  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____4749  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4748
    | FStar_Parser_AST.PatWild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.PatConst c -> p_constant c
    | FStar_Parser_AST.PatVar (lid,aqual) ->
        let uu____4759 = FStar_Pprint.optional p_aqual aqual  in
        let uu____4760 = p_lident lid  in
        FStar_Pprint.op_Hat_Hat uu____4759 uu____4760
    | FStar_Parser_AST.PatName uid -> p_quident uid
    | FStar_Parser_AST.PatOr uu____4762 -> failwith "Inner or pattern !"
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName uu____4765;
           FStar_Parser_AST.prange = uu____4766;_},uu____4767)
        ->
        let uu____4772 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4772
    | FStar_Parser_AST.PatTuple (uu____4773,false ) ->
        let uu____4778 = p_tuplePattern p  in
        soft_parens_with_nesting uu____4778
    | uu____4779 ->
        let uu____4780 =
          let uu____4781 = FStar_Parser_AST.pat_to_string p  in
          FStar_Util.format1 "Invalid pattern %s" uu____4781  in
        failwith uu____4780

and (p_binder :
  Prims.bool -> FStar_Parser_AST.binder -> FStar_Pprint.document) =
  fun is_atomic  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable lid ->
          let uu____4785 =
            FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
          let uu____4786 = p_lident lid  in
          FStar_Pprint.op_Hat_Hat uu____4785 uu____4786
      | FStar_Parser_AST.TVariable lid -> p_lident lid
      | FStar_Parser_AST.Annotated (lid,t) ->
          let doc1 =
            match t.FStar_Parser_AST.tm with
            | FStar_Parser_AST.Refine
                ({ FStar_Parser_AST.b = FStar_Parser_AST.Annotated (lid',t1);
                   FStar_Parser_AST.brange = uu____4793;
                   FStar_Parser_AST.blevel = uu____4794;
                   FStar_Parser_AST.aqual = uu____4795;_},phi)
                when lid.FStar_Ident.idText = lid'.FStar_Ident.idText ->
                let uu____4797 = p_lident lid  in
                p_refinement b.FStar_Parser_AST.aqual uu____4797 t1 phi
            | uu____4798 ->
                let uu____4799 =
                  FStar_Pprint.optional p_aqual b.FStar_Parser_AST.aqual  in
                let uu____4800 =
                  let uu____4801 = p_lident lid  in
                  let uu____4802 =
                    let uu____4803 = p_tmFormula t  in
                    FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon
                      uu____4803
                     in
                  FStar_Pprint.op_Hat_Hat uu____4801 uu____4802  in
                FStar_Pprint.op_Hat_Hat uu____4799 uu____4800
             in
          if is_atomic
          then
            let uu____4804 =
              let uu____4805 =
                FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4805  in
            FStar_Pprint.group uu____4804
          else FStar_Pprint.group doc1
      | FStar_Parser_AST.TAnnotated uu____4807 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.NoName t ->
          (match t.FStar_Parser_AST.tm with
           | FStar_Parser_AST.Refine
               ({ FStar_Parser_AST.b = FStar_Parser_AST.NoName t1;
                  FStar_Parser_AST.brange = uu____4814;
                  FStar_Parser_AST.blevel = uu____4815;
                  FStar_Parser_AST.aqual = uu____4816;_},phi)
               ->
               if is_atomic
               then
                 let uu____4818 =
                   let uu____4819 =
                     let uu____4820 =
                       p_refinement b.FStar_Parser_AST.aqual
                         FStar_Pprint.underscore t1 phi
                        in
                     FStar_Pprint.op_Hat_Hat uu____4820 FStar_Pprint.rparen
                      in
                   FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____4819  in
                 FStar_Pprint.group uu____4818
               else
                 (let uu____4822 =
                    p_refinement b.FStar_Parser_AST.aqual
                      FStar_Pprint.underscore t1 phi
                     in
                  FStar_Pprint.group uu____4822)
           | uu____4823 -> if is_atomic then p_atomicTerm t else p_appTerm t)

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
            | FStar_Parser_AST.Construct uu____4832 -> false
            | FStar_Parser_AST.App uu____4843 -> false
            | FStar_Parser_AST.Op uu____4850 -> false
            | uu____4857 -> true  in
          let phi1 = p_noSeqTerm false false phi  in
          let jump_break =
            if is_t_atomic
            then (Prims.parse_int "0")
            else (Prims.parse_int "1")  in
          let uu____4861 =
            let uu____4862 = FStar_Pprint.optional p_aqual aqual_opt  in
            let uu____4863 =
              FStar_Pprint.op_Hat_Hat binder FStar_Pprint.colon  in
            FStar_Pprint.op_Hat_Hat uu____4862 uu____4863  in
          let uu____4864 =
            let uu____4865 = p_appTerm t  in
            let uu____4866 =
              let uu____4867 =
                let uu____4868 =
                  let uu____4869 = soft_braces_with_nesting_tight phi1  in
                  let uu____4870 = soft_braces_with_nesting phi1  in
                  FStar_Pprint.ifflat uu____4869 uu____4870  in
                FStar_Pprint.group uu____4868  in
              FStar_Pprint.jump (Prims.parse_int "2") jump_break uu____4867
               in
            FStar_Pprint.op_Hat_Hat uu____4865 uu____4866  in
          FStar_Pprint.op_Hat_Slash_Hat uu____4861 uu____4864

and (p_binders_list :
  Prims.bool ->
    FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document Prims.list)
  = fun is_atomic  -> fun bs  -> FStar_List.map (p_binder is_atomic) bs

and (p_binders :
  Prims.bool -> FStar_Parser_AST.binder Prims.list -> FStar_Pprint.document)
  =
  fun is_atomic  ->
    fun bs  ->
      let uu____4881 = p_binders_list is_atomic bs  in
      separate_or_flow break1 uu____4881

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
            let uu____4904 =
              let uu____4905 =
                let uu____4906 = p_noSeqTerm true false e1  in
                FStar_Pprint.op_Hat_Hat uu____4906 FStar_Pprint.semi  in
              FStar_Pprint.group uu____4905  in
            let uu____4907 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4904 uu____4907
        | FStar_Parser_AST.Bind (x,e1,e2) ->
            let uu____4911 =
              let uu____4912 =
                let uu____4913 =
                  let uu____4914 = p_lident x  in
                  let uu____4915 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.long_left_arrow
                     in
                  FStar_Pprint.op_Hat_Hat uu____4914 uu____4915  in
                let uu____4916 =
                  let uu____4917 = p_noSeqTerm true false e1  in
                  let uu____4918 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                      FStar_Pprint.semi
                     in
                  FStar_Pprint.op_Hat_Hat uu____4917 uu____4918  in
                op_Hat_Slash_Plus_Hat uu____4913 uu____4916  in
              FStar_Pprint.group uu____4912  in
            let uu____4919 = p_term ps pb e2  in
            FStar_Pprint.op_Hat_Slash_Hat uu____4911 uu____4919
        | uu____4920 ->
            let uu____4921 = p_noSeqTerm ps pb e  in
            FStar_Pprint.group uu____4921

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
            let uu____4932 =
              let uu____4933 = p_tmIff e1  in
              let uu____4934 =
                let uu____4935 =
                  let uu____4936 = p_typ ps pb t  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4936
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4935  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4933 uu____4934  in
            FStar_Pprint.group uu____4932
        | FStar_Parser_AST.Ascribed (e1,t,FStar_Pervasives_Native.Some tac)
            ->
            let uu____4942 =
              let uu____4943 = p_tmIff e1  in
              let uu____4944 =
                let uu____4945 =
                  let uu____4946 =
                    let uu____4947 = p_typ false false t  in
                    let uu____4948 =
                      let uu____4949 = str "by"  in
                      let uu____4950 = p_typ ps pb tac  in
                      FStar_Pprint.op_Hat_Slash_Hat uu____4949 uu____4950  in
                    FStar_Pprint.op_Hat_Slash_Hat uu____4947 uu____4948  in
                  FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____4946
                   in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.langle uu____4945  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4943 uu____4944  in
            FStar_Pprint.group uu____4942
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".()<-";
               FStar_Ident.idRange = uu____4951;_},e1::e2::e3::[])
            ->
            let uu____4957 =
              let uu____4958 =
                let uu____4959 =
                  let uu____4960 = p_atomicTermNotQUident e1  in
                  let uu____4961 =
                    let uu____4962 =
                      let uu____4963 =
                        let uu____4964 = p_term false false e2  in
                        soft_parens_with_nesting uu____4964  in
                      let uu____4965 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4963 uu____4965  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4962  in
                  FStar_Pprint.op_Hat_Hat uu____4960 uu____4961  in
                FStar_Pprint.group uu____4959  in
              let uu____4966 =
                let uu____4967 = p_noSeqTerm ps pb e3  in jump2 uu____4967
                 in
              FStar_Pprint.op_Hat_Hat uu____4958 uu____4966  in
            FStar_Pprint.group uu____4957
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ".[]<-";
               FStar_Ident.idRange = uu____4968;_},e1::e2::e3::[])
            ->
            let uu____4974 =
              let uu____4975 =
                let uu____4976 =
                  let uu____4977 = p_atomicTermNotQUident e1  in
                  let uu____4978 =
                    let uu____4979 =
                      let uu____4980 =
                        let uu____4981 = p_term false false e2  in
                        soft_brackets_with_nesting uu____4981  in
                      let uu____4982 =
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                          FStar_Pprint.larrow
                         in
                      FStar_Pprint.op_Hat_Hat uu____4980 uu____4982  in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____4979  in
                  FStar_Pprint.op_Hat_Hat uu____4977 uu____4978  in
                FStar_Pprint.group uu____4976  in
              let uu____4983 =
                let uu____4984 = p_noSeqTerm ps pb e3  in jump2 uu____4984
                 in
              FStar_Pprint.op_Hat_Hat uu____4975 uu____4983  in
            FStar_Pprint.group uu____4974
        | FStar_Parser_AST.Requires (e1,wtf) ->
            let uu____4994 =
              let uu____4995 = str "requires"  in
              let uu____4996 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____4995 uu____4996  in
            FStar_Pprint.group uu____4994
        | FStar_Parser_AST.Ensures (e1,wtf) ->
            let uu____5006 =
              let uu____5007 = str "ensures"  in
              let uu____5008 = p_typ ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5007 uu____5008  in
            FStar_Pprint.group uu____5006
        | FStar_Parser_AST.Attributes es ->
            let uu____5012 =
              let uu____5013 = str "attributes"  in
              let uu____5014 =
                FStar_Pprint.separate_map break1 p_atomicTerm es  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5013 uu____5014  in
            FStar_Pprint.group uu____5012
        | FStar_Parser_AST.If (e1,e2,e3) ->
            if is_unit e3
            then
              let uu____5018 =
                let uu____5019 =
                  let uu____5020 = str "if"  in
                  let uu____5021 = p_noSeqTerm false false e1  in
                  op_Hat_Slash_Plus_Hat uu____5020 uu____5021  in
                let uu____5022 =
                  let uu____5023 = str "then"  in
                  let uu____5024 = p_noSeqTerm ps pb e2  in
                  op_Hat_Slash_Plus_Hat uu____5023 uu____5024  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5019 uu____5022  in
              FStar_Pprint.group uu____5018
            else
              (let e2_doc =
                 match e2.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.If (uu____5027,uu____5028,e31) when
                     is_unit e31 ->
                     let uu____5030 = p_noSeqTerm false false e2  in
                     soft_parens_with_nesting uu____5030
                 | uu____5031 -> p_noSeqTerm false false e2  in
               let uu____5032 =
                 let uu____5033 =
                   let uu____5034 = str "if"  in
                   let uu____5035 = p_noSeqTerm false false e1  in
                   op_Hat_Slash_Plus_Hat uu____5034 uu____5035  in
                 let uu____5036 =
                   let uu____5037 =
                     let uu____5038 = str "then"  in
                     op_Hat_Slash_Plus_Hat uu____5038 e2_doc  in
                   let uu____5039 =
                     let uu____5040 = str "else"  in
                     let uu____5041 = p_noSeqTerm ps pb e3  in
                     op_Hat_Slash_Plus_Hat uu____5040 uu____5041  in
                   FStar_Pprint.op_Hat_Slash_Hat uu____5037 uu____5039  in
                 FStar_Pprint.op_Hat_Slash_Hat uu____5033 uu____5036  in
               FStar_Pprint.group uu____5032)
        | FStar_Parser_AST.TryWith (e1,branches) ->
            let uu____5064 =
              let uu____5065 =
                let uu____5066 =
                  let uu____5067 = str "try"  in
                  let uu____5068 = p_noSeqTerm false false e1  in
                  prefix2 uu____5067 uu____5068  in
                let uu____5069 =
                  let uu____5070 = str "with"  in
                  let uu____5071 =
                    separate_map_last FStar_Pprint.hardline p_patternBranch
                      branches
                     in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5070 uu____5071  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5066 uu____5069  in
              FStar_Pprint.group uu____5065  in
            let uu____5080 = paren_if (ps || pb)  in uu____5080 uu____5064
        | FStar_Parser_AST.Match (e1,branches) ->
            let uu____5105 =
              let uu____5106 =
                let uu____5107 =
                  let uu____5108 = str "match"  in
                  let uu____5109 = p_noSeqTerm false false e1  in
                  let uu____5110 = str "with"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5108 uu____5109 uu____5110
                   in
                let uu____5111 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5107 uu____5111  in
              FStar_Pprint.group uu____5106  in
            let uu____5120 = paren_if (ps || pb)  in uu____5120 uu____5105
        | FStar_Parser_AST.LetOpen (uid,e1) ->
            let uu____5125 =
              let uu____5126 =
                let uu____5127 =
                  let uu____5128 = str "let open"  in
                  let uu____5129 = p_quident uid  in
                  let uu____5130 = str "in"  in
                  FStar_Pprint.surround (Prims.parse_int "2")
                    (Prims.parse_int "1") uu____5128 uu____5129 uu____5130
                   in
                let uu____5131 = p_term false pb e1  in
                FStar_Pprint.op_Hat_Slash_Hat uu____5127 uu____5131  in
              FStar_Pprint.group uu____5126  in
            let uu____5132 = paren_if ps  in uu____5132 uu____5125
        | FStar_Parser_AST.Let (q,lbs,e1) ->
            let p_lb q1 uu____5188 is_last =
              match uu____5188 with
              | (a,(pat,e2)) ->
                  let attrs = p_attrs_opt a  in
                  let doc_let_or_and =
                    match q1 with
                    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Rec ) ->
                        let uu____5221 =
                          let uu____5222 = str "let"  in
                          let uu____5223 = str "rec"  in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5222 uu____5223
                           in
                        FStar_Pprint.group uu____5221
                    | FStar_Pervasives_Native.Some
                        (FStar_Parser_AST.NoLetQualifier ) -> str "let"
                    | uu____5224 -> str "and"  in
                  let doc_pat = p_letlhs doc_let_or_and (pat, e2)  in
                  let doc_expr = p_term false false e2  in
                  let uu____5229 =
                    if is_last
                    then
                      let uu____5230 =
                        FStar_Pprint.flow break1
                          [doc_pat; FStar_Pprint.equals]
                         in
                      let uu____5231 = str "in"  in
                      FStar_Pprint.surround (Prims.parse_int "2")
                        (Prims.parse_int "1") uu____5230 doc_expr uu____5231
                    else
                      (let uu____5233 =
                         FStar_Pprint.flow break1
                           [doc_pat; FStar_Pprint.equals; doc_expr]
                          in
                       FStar_Pprint.hang (Prims.parse_int "2") uu____5233)
                     in
                  FStar_Pprint.op_Hat_Hat attrs uu____5229
               in
            let l = FStar_List.length lbs  in
            let lbs_docs =
              FStar_List.mapi
                (fun i  ->
                   fun lb  ->
                     if i = (Prims.parse_int "0")
                     then
                       let uu____5279 =
                         p_lb (FStar_Pervasives_Native.Some q) lb
                           (i = (l - (Prims.parse_int "1")))
                          in
                       FStar_Pprint.group uu____5279
                     else
                       (let uu____5287 =
                          p_lb FStar_Pervasives_Native.None lb
                            (i = (l - (Prims.parse_int "1")))
                           in
                        FStar_Pprint.group uu____5287)) lbs
               in
            let lbs_doc =
              let uu____5295 = FStar_Pprint.separate break1 lbs_docs  in
              FStar_Pprint.group uu____5295  in
            let uu____5296 =
              let uu____5297 =
                let uu____5298 =
                  let uu____5299 = p_term false pb e1  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline uu____5299
                   in
                FStar_Pprint.op_Hat_Hat lbs_doc uu____5298  in
              FStar_Pprint.group uu____5297  in
            let uu____5300 = paren_if ps  in uu____5300 uu____5296
        | FStar_Parser_AST.Abs
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x,typ_opt);
               FStar_Parser_AST.prange = uu____5305;_}::[],{
                                                             FStar_Parser_AST.tm
                                                               =
                                                               FStar_Parser_AST.Match
                                                               (maybe_x,branches);
                                                             FStar_Parser_AST.range
                                                               = uu____5308;
                                                             FStar_Parser_AST.level
                                                               = uu____5309;_})
            when matches_var maybe_x x ->
            let uu____5336 =
              let uu____5337 =
                let uu____5338 = str "function"  in
                let uu____5339 =
                  separate_map_last FStar_Pprint.hardline p_patternBranch
                    branches
                   in
                FStar_Pprint.op_Hat_Slash_Hat uu____5338 uu____5339  in
              FStar_Pprint.group uu____5337  in
            let uu____5348 = paren_if (ps || pb)  in uu____5348 uu____5336
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Dynamic ) ->
            let uu____5352 =
              let uu____5353 = str "quote"  in
              let uu____5354 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5353 uu____5354  in
            FStar_Pprint.group uu____5352
        | FStar_Parser_AST.Quote (e1,FStar_Parser_AST.Static ) ->
            let uu____5356 =
              let uu____5357 = str "`"  in
              let uu____5358 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5357 uu____5358  in
            FStar_Pprint.group uu____5356
        | FStar_Parser_AST.VQuote e1 ->
            let uu____5360 =
              let uu____5361 = str "%`"  in
              let uu____5362 = p_noSeqTerm ps pb e1  in
              FStar_Pprint.op_Hat_Hat uu____5361 uu____5362  in
            FStar_Pprint.group uu____5360
        | uu____5363 -> p_typ ps pb e

and (p_attrs_opt :
  FStar_Parser_AST.term Prims.list FStar_Pervasives_Native.option ->
    FStar_Pprint.document)
  =
  fun uu___59_5364  ->
    match uu___59_5364 with
    | FStar_Pervasives_Native.None  -> FStar_Pprint.empty
    | FStar_Pervasives_Native.Some terms ->
        let uu____5376 =
          let uu____5377 = str "[@"  in
          let uu____5378 =
            let uu____5379 =
              FStar_Pprint.separate_map break1 p_atomicTerm terms  in
            let uu____5380 = str "]"  in
            FStar_Pprint.op_Hat_Slash_Hat uu____5379 uu____5380  in
          FStar_Pprint.op_Hat_Slash_Hat uu____5377 uu____5378  in
        FStar_Pprint.group uu____5376

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
                 let uu____5406 =
                   let uu____5407 =
                     let uu____5408 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5408 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5407 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5406 term_doc
             | pats ->
                 let uu____5414 =
                   let uu____5415 =
                     let uu____5416 =
                       let uu____5417 =
                         let uu____5418 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5418
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5417 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5419 = p_trigger trigger  in
                     prefix2 uu____5416 uu____5419  in
                   FStar_Pprint.group uu____5415  in
                 prefix2 uu____5414 term_doc)
        | FStar_Parser_AST.QExists (bs,trigger,e1) ->
            let binders_doc = p_binders true bs  in
            let term_doc = p_noSeqTerm ps pb e1  in
            (match trigger with
             | [] ->
                 let uu____5439 =
                   let uu____5440 =
                     let uu____5441 = p_quantifier e  in
                     FStar_Pprint.op_Hat_Hat uu____5441 FStar_Pprint.space
                      in
                   FStar_Pprint.soft_surround (Prims.parse_int "2")
                     (Prims.parse_int "0") uu____5440 binders_doc
                     FStar_Pprint.dot
                    in
                 prefix2 uu____5439 term_doc
             | pats ->
                 let uu____5447 =
                   let uu____5448 =
                     let uu____5449 =
                       let uu____5450 =
                         let uu____5451 = p_quantifier e  in
                         FStar_Pprint.op_Hat_Hat uu____5451
                           FStar_Pprint.space
                          in
                       FStar_Pprint.soft_surround (Prims.parse_int "2")
                         (Prims.parse_int "0") uu____5450 binders_doc
                         FStar_Pprint.dot
                        in
                     let uu____5452 = p_trigger trigger  in
                     prefix2 uu____5449 uu____5452  in
                   FStar_Pprint.group uu____5448  in
                 prefix2 uu____5447 term_doc)
        | uu____5453 -> p_simpleTerm ps pb e

and (p_quantifier : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.QForall uu____5455 -> str "forall"
    | FStar_Parser_AST.QExists uu____5468 -> str "exists"
    | uu____5481 ->
        failwith "Imposible : p_quantifier called on a non-quantifier term"

and (p_trigger :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun uu___60_5482  ->
    match uu___60_5482 with
    | [] -> FStar_Pprint.empty
    | pats ->
        let uu____5494 =
          let uu____5495 =
            let uu____5496 =
              let uu____5497 = str "pattern"  in
              let uu____5498 =
                let uu____5499 =
                  let uu____5500 = p_disjunctivePats pats  in
                  jump2 uu____5500  in
                FStar_Pprint.op_Hat_Hat uu____5499 FStar_Pprint.rbrace  in
              FStar_Pprint.op_Hat_Slash_Hat uu____5497 uu____5498  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5496  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbrace uu____5495  in
        FStar_Pprint.group uu____5494

and (p_disjunctivePats :
  FStar_Parser_AST.term Prims.list Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5506 = str "\\/"  in
    FStar_Pprint.separate_map uu____5506 p_conjunctivePats pats

and (p_conjunctivePats :
  FStar_Parser_AST.term Prims.list -> FStar_Pprint.document) =
  fun pats  ->
    let uu____5512 =
      let uu____5513 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
      FStar_Pprint.separate_map uu____5513 p_appTerm pats  in
    FStar_Pprint.group uu____5512

and (p_simpleTerm :
  Prims.bool -> Prims.bool -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun ps  ->
    fun pb  ->
      fun e  ->
        match e.FStar_Parser_AST.tm with
        | FStar_Parser_AST.Abs (pats,e1) ->
            let uu____5523 =
              let uu____5524 =
                let uu____5525 = str "fun"  in
                let uu____5526 =
                  let uu____5527 =
                    FStar_Pprint.separate_map break1 p_atomicPattern pats  in
                  FStar_Pprint.op_Hat_Slash_Hat uu____5527
                    FStar_Pprint.rarrow
                   in
                op_Hat_Slash_Plus_Hat uu____5525 uu____5526  in
              let uu____5528 = p_term false pb e1  in
              op_Hat_Slash_Plus_Hat uu____5524 uu____5528  in
            let uu____5529 = paren_if ps  in uu____5529 uu____5523
        | uu____5532 -> p_tmIff e

and (p_maybeFocusArrow : Prims.bool -> FStar_Pprint.document) =
  fun b  -> if b then str "~>" else FStar_Pprint.rarrow

and (p_patternBranch :
  Prims.bool ->
    (FStar_Parser_AST.pattern,FStar_Parser_AST.term
                                FStar_Pervasives_Native.option,FStar_Parser_AST.term)
      FStar_Pervasives_Native.tuple3 -> FStar_Pprint.document)
  =
  fun pb  ->
    fun uu____5536  ->
      match uu____5536 with
      | (pat,when_opt,e) ->
          let one_pattern_branch p =
            let branch =
              match when_opt with
              | FStar_Pervasives_Native.None  ->
                  let uu____5557 =
                    let uu____5558 =
                      let uu____5559 =
                        let uu____5560 = p_tuplePattern p  in
                        let uu____5561 =
                          FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                            FStar_Pprint.rarrow
                           in
                        FStar_Pprint.op_Hat_Hat uu____5560 uu____5561  in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5559
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5558  in
                  FStar_Pprint.group uu____5557
              | FStar_Pervasives_Native.Some f ->
                  let uu____5563 =
                    let uu____5564 =
                      let uu____5565 =
                        let uu____5566 =
                          let uu____5567 =
                            let uu____5568 = p_tuplePattern p  in
                            let uu____5569 = str "when"  in
                            FStar_Pprint.op_Hat_Slash_Hat uu____5568
                              uu____5569
                             in
                          FStar_Pprint.group uu____5567  in
                        let uu____5570 =
                          let uu____5571 =
                            let uu____5574 = p_tmFormula f  in
                            [uu____5574; FStar_Pprint.rarrow]  in
                          FStar_Pprint.flow break1 uu____5571  in
                        FStar_Pprint.op_Hat_Slash_Hat uu____5566 uu____5570
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5565
                       in
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5564  in
                  FStar_Pprint.hang (Prims.parse_int "2") uu____5563
               in
            let uu____5575 =
              let uu____5576 = p_term false pb e  in
              op_Hat_Slash_Plus_Hat branch uu____5576  in
            FStar_Pprint.group uu____5575  in
          (match pat.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatOr pats ->
               (match FStar_List.rev pats with
                | hd1::tl1 ->
                    let last_pat_branch = one_pattern_branch hd1  in
                    let uu____5585 =
                      let uu____5586 =
                        let uu____5587 =
                          let uu____5588 =
                            let uu____5589 =
                              let uu____5590 =
                                FStar_Pprint.op_Hat_Hat FStar_Pprint.bar
                                  FStar_Pprint.space
                                 in
                              FStar_Pprint.op_Hat_Hat break1 uu____5590  in
                            FStar_Pprint.separate_map uu____5589
                              p_tuplePattern (FStar_List.rev tl1)
                             in
                          FStar_Pprint.op_Hat_Slash_Hat uu____5588
                            last_pat_branch
                           in
                        FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5587
                         in
                      FStar_Pprint.op_Hat_Hat FStar_Pprint.bar uu____5586  in
                    FStar_Pprint.group uu____5585
                | [] ->
                    failwith "Impossible: disjunctive pattern can't be empty")
           | uu____5591 -> one_pattern_branch pat)

and (p_tmIff : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "<==>"; FStar_Ident.idRange = uu____5593;_},e1::e2::[])
        ->
        let uu____5598 = str "<==>"  in
        let uu____5599 = p_tmImplies e1  in
        let uu____5600 = p_tmIff e2  in
        infix0 uu____5598 uu____5599 uu____5600
    | uu____5601 -> p_tmImplies e

and (p_tmImplies : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "==>"; FStar_Ident.idRange = uu____5603;_},e1::e2::[])
        ->
        let uu____5608 = str "==>"  in
        let uu____5609 = p_tmArrow p_tmFormula e1  in
        let uu____5610 = p_tmImplies e2  in
        infix0 uu____5608 uu____5609 uu____5610
    | uu____5611 -> p_tmArrow p_tmFormula e

and (p_tmArrow :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_Tm  ->
    fun e  ->
      let terms = p_tmArrow' p_Tm e  in
      let uu____5619 =
        FStar_List.splitAt
          ((FStar_List.length terms) - (Prims.parse_int "1")) terms
         in
      match uu____5619 with
      | (terms',last1) ->
          let last_op =
            if (FStar_List.length terms) > (Prims.parse_int "1")
            then
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rarrow
            else FStar_Pprint.empty  in
          (match FStar_List.length terms with
           | _0_31 when _0_31 = (Prims.parse_int "1") -> FStar_List.hd terms
           | uu____5640 ->
               let uu____5641 =
                 let uu____5642 =
                   let uu____5643 =
                     let uu____5644 =
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow break1  in
                     FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5644
                      in
                   FStar_Pprint.separate uu____5643 terms  in
                 let uu____5645 =
                   let uu____5646 =
                     let uu____5647 =
                       let uu____5648 =
                         let uu____5649 =
                           let uu____5650 =
                             let uu____5651 =
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                 break1
                                in
                             FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                               uu____5651
                              in
                           FStar_Pprint.separate uu____5650 terms'  in
                         FStar_Pprint.op_Hat_Hat uu____5649 last_op  in
                       let uu____5652 =
                         let uu____5653 =
                           let uu____5654 =
                             let uu____5655 =
                               let uu____5656 =
                                 FStar_Pprint.op_Hat_Hat FStar_Pprint.rarrow
                                   break1
                                  in
                               FStar_Pprint.op_Hat_Hat FStar_Pprint.space
                                 uu____5656
                                in
                             FStar_Pprint.separate uu____5655 terms'  in
                           FStar_Pprint.op_Hat_Hat uu____5654 last_op  in
                         jump2 uu____5653  in
                       FStar_Pprint.ifflat uu____5648 uu____5652  in
                     FStar_Pprint.group uu____5647  in
                   let uu____5657 = FStar_List.hd last1  in
                   prefix2 uu____5646 uu____5657  in
                 FStar_Pprint.ifflat uu____5642 uu____5645  in
               FStar_Pprint.group uu____5641)

and (p_tmArrow' :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document Prims.list)
  =
  fun p_Tm  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (bs,tgt) ->
          let uu____5670 = FStar_List.map (fun b  -> p_binder false b) bs  in
          let uu____5675 = p_tmArrow' p_Tm tgt  in
          FStar_List.append uu____5670 uu____5675
      | uu____5678 -> let uu____5679 = p_Tm e  in [uu____5679]

and (p_tmFormula : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let conj =
      let uu____5682 =
        let uu____5683 = str "/\\"  in
        FStar_Pprint.op_Hat_Hat uu____5683 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5682  in
    let disj =
      let uu____5685 =
        let uu____5686 = str "\\/"  in
        FStar_Pprint.op_Hat_Hat uu____5686 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5685  in
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
        ({ FStar_Ident.idText = "\\/"; FStar_Ident.idRange = uu____5705;_},e1::e2::[])
        ->
        let uu____5710 = p_tmDisjunction e1  in
        let uu____5715 = let uu____5720 = p_tmConjunction e2  in [uu____5720]
           in
        FStar_List.append uu____5710 uu____5715
    | uu____5729 -> let uu____5730 = p_tmConjunction e  in [uu____5730]

and (p_tmConjunction :
  FStar_Parser_AST.term -> FStar_Pprint.document Prims.list) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "/\\"; FStar_Ident.idRange = uu____5740;_},e1::e2::[])
        ->
        let uu____5745 = p_tmConjunction e1  in
        let uu____5748 = let uu____5751 = p_tmTuple e2  in [uu____5751]  in
        FStar_List.append uu____5745 uu____5748
    | uu____5752 -> let uu____5753 = p_tmTuple e  in [uu____5753]

and (p_tmTuple : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> with_comment p_tmTuple' e e.FStar_Parser_AST.range

and (p_tmTuple' : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Construct (lid,args) when is_tuple_constructor lid ->
        let uu____5770 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
           in
        FStar_Pprint.separate_map uu____5770
          (fun uu____5778  ->
             match uu____5778 with | (e1,uu____5784) -> p_tmEq e1) args
    | uu____5785 -> p_tmEq e

and (paren_if_gt :
  Prims.int -> Prims.int -> FStar_Pprint.document -> FStar_Pprint.document) =
  fun curr  ->
    fun mine  ->
      fun doc1  ->
        if mine <= curr
        then doc1
        else
          (let uu____5790 =
             let uu____5791 =
               FStar_Pprint.op_Hat_Hat doc1 FStar_Pprint.rparen  in
             FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____5791  in
           FStar_Pprint.group uu____5790)

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
            let uu____5854 = levels op1  in
            (match uu____5854 with
             | (left1,mine,right1) ->
                 let uu____5864 =
                   let uu____5865 = FStar_All.pipe_left str op1  in
                   let uu____5866 = p_tmEqWith' p_X left1 e1  in
                   let uu____5867 = p_tmEqWith' p_X right1 e2  in
                   infix0 uu____5865 uu____5866 uu____5867  in
                 paren_if_gt curr mine uu____5864)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = ":="; FStar_Ident.idRange = uu____5868;_},e1::e2::[])
            ->
            let uu____5873 =
              let uu____5874 = p_tmEqWith p_X e1  in
              let uu____5875 =
                let uu____5876 =
                  let uu____5877 =
                    let uu____5878 = p_tmEqWith p_X e2  in
                    op_Hat_Slash_Plus_Hat FStar_Pprint.equals uu____5878  in
                  FStar_Pprint.op_Hat_Hat FStar_Pprint.colon uu____5877  in
                FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____5876  in
              FStar_Pprint.op_Hat_Hat uu____5874 uu____5875  in
            FStar_Pprint.group uu____5873
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "-"; FStar_Ident.idRange = uu____5879;_},e1::[])
            ->
            let uu____5883 = levels "-"  in
            (match uu____5883 with
             | (left1,mine,right1) ->
                 let uu____5893 = p_tmEqWith' p_X mine e1  in
                 FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.minus uu____5893)
        | uu____5894 -> p_tmNoEqWith p_X e

and (p_tmNoEqWith :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun p_X  ->
    fun e  ->
      let n1 = max_level [colon_colon (); amp (); opinfix3 (); opinfix4 ()]
         in
      p_tmNoEqWith' false p_X n1 e

and (p_tmNoEqWith' :
  Prims.bool ->
    (FStar_Parser_AST.term -> FStar_Pprint.document) ->
      Prims.int -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun inside_tuple  ->
    fun p_X  ->
      fun curr  ->
        fun e  ->
          match e.FStar_Parser_AST.tm with
          | FStar_Parser_AST.Construct
              (lid,(e1,uu____5966)::(e2,uu____5968)::[]) when
              (FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid) &&
                (let uu____5988 = is_list e  in Prims.op_Negation uu____5988)
              ->
              let op = "::"  in
              let uu____5990 = levels op  in
              (match uu____5990 with
               | (left1,mine,right1) ->
                   let uu____6000 =
                     let uu____6001 = str op  in
                     let uu____6002 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6003 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6001 uu____6002 uu____6003  in
                   paren_if_gt curr mine uu____6000)
          | FStar_Parser_AST.Sum (binders,res) ->
              let op = "&"  in
              let uu____6011 = levels op  in
              (match uu____6011 with
               | (left1,mine,right1) ->
                   let p_dsumfst b =
                     let uu____6025 = p_binder false b  in
                     let uu____6026 =
                       let uu____6027 =
                         let uu____6028 = str op  in
                         FStar_Pprint.op_Hat_Hat uu____6028 break1  in
                       FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6027
                        in
                     FStar_Pprint.op_Hat_Hat uu____6025 uu____6026  in
                   let uu____6029 =
                     let uu____6030 =
                       FStar_Pprint.concat_map p_dsumfst binders  in
                     let uu____6031 = p_tmNoEqWith' false p_X right1 res  in
                     FStar_Pprint.op_Hat_Hat uu____6030 uu____6031  in
                   paren_if_gt curr mine uu____6029)
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "*";
                 FStar_Ident.idRange = uu____6032;_},e1::e2::[])
              ->
              let op = "*"  in
              let uu____6038 = levels op  in
              (match uu____6038 with
               | (left1,mine,right1) ->
                   if inside_tuple
                   then
                     let uu____6048 = str op  in
                     let uu____6049 = p_tmNoEqWith' true p_X left1 e1  in
                     let uu____6050 = p_tmNoEqWith' true p_X right1 e2  in
                     infix0 uu____6048 uu____6049 uu____6050
                   else
                     (let uu____6051 =
                        let uu____6052 = str op  in
                        let uu____6053 = p_tmNoEqWith' true p_X left1 e1  in
                        let uu____6054 = p_tmNoEqWith' true p_X right1 e2  in
                        infix0 uu____6052 uu____6053 uu____6054  in
                      paren_if_gt curr mine uu____6051))
          | FStar_Parser_AST.Op (op,e1::e2::[]) when is_operatorInfix34 op ->
              let op1 = FStar_Ident.text_of_id op  in
              let uu____6061 = levels op1  in
              (match uu____6061 with
               | (left1,mine,right1) ->
                   let uu____6071 =
                     let uu____6072 = str op1  in
                     let uu____6073 = p_tmNoEqWith' false p_X left1 e1  in
                     let uu____6074 = p_tmNoEqWith' false p_X right1 e2  in
                     infix0 uu____6072 uu____6073 uu____6074  in
                   paren_if_gt curr mine uu____6071)
          | FStar_Parser_AST.Record (with_opt,record_fields) ->
              let uu____6093 =
                let uu____6094 =
                  default_or_map FStar_Pprint.empty p_with_clause with_opt
                   in
                let uu____6095 =
                  let uu____6096 =
                    FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1  in
                  separate_map_last uu____6096 p_simpleDef record_fields  in
                FStar_Pprint.op_Hat_Hat uu____6094 uu____6095  in
              braces_with_nesting uu____6093
          | FStar_Parser_AST.Op
              ({ FStar_Ident.idText = "~";
                 FStar_Ident.idRange = uu____6101;_},e1::[])
              ->
              let uu____6105 =
                let uu____6106 = str "~"  in
                let uu____6107 = p_atomicTerm e1  in
                FStar_Pprint.op_Hat_Hat uu____6106 uu____6107  in
              FStar_Pprint.group uu____6105
          | FStar_Parser_AST.Paren p when inside_tuple ->
              (match p.FStar_Parser_AST.tm with
               | FStar_Parser_AST.Op
                   ({ FStar_Ident.idText = "*";
                      FStar_Ident.idRange = uu____6109;_},e1::e2::[])
                   ->
                   let op = "*"  in
                   let uu____6115 = levels op  in
                   (match uu____6115 with
                    | (left1,mine,right1) ->
                        let uu____6125 =
                          let uu____6126 = str op  in
                          let uu____6127 = p_tmNoEqWith' true p_X left1 e1
                             in
                          let uu____6128 = p_tmNoEqWith' true p_X right1 e2
                             in
                          infix0 uu____6126 uu____6127 uu____6128  in
                        paren_if_gt curr mine uu____6125)
               | uu____6129 -> p_X e)
          | uu____6130 -> p_X e

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
        let uu____6137 =
          let uu____6138 = p_lident lid  in
          let uu____6139 =
            let uu____6140 = p_appTerm e1  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.colon uu____6140  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6138 uu____6139  in
        FStar_Pprint.group uu____6137
    | FStar_Parser_AST.Refine (b,phi) -> p_refinedBinder b phi
    | uu____6143 -> p_appTerm e

and (p_with_clause : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    let uu____6145 = p_appTerm e  in
    let uu____6146 =
      let uu____6147 =
        let uu____6148 = str "with"  in
        FStar_Pprint.op_Hat_Hat uu____6148 break1  in
      FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6147  in
    FStar_Pprint.op_Hat_Hat uu____6145 uu____6146

and (p_refinedBinder :
  FStar_Parser_AST.binder -> FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun b  ->
    fun phi  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.Annotated (lid,t) ->
          let uu____6153 = p_lident lid  in
          p_refinement b.FStar_Parser_AST.aqual uu____6153 t phi
      | FStar_Parser_AST.TAnnotated uu____6154 ->
          failwith "Is this still used ?"
      | FStar_Parser_AST.Variable uu____6159 ->
          let uu____6160 =
            let uu____6161 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6161
             in
          failwith uu____6160
      | FStar_Parser_AST.TVariable uu____6162 ->
          let uu____6163 =
            let uu____6164 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6164
             in
          failwith uu____6163
      | FStar_Parser_AST.NoName uu____6165 ->
          let uu____6166 =
            let uu____6167 = FStar_Parser_AST.binder_to_string b  in
            FStar_Util.format1
              "Imposible : a refined binder ought to be annotated %s"
              uu____6167
             in
          failwith uu____6166

and (p_simpleDef :
  Prims.bool ->
    (FStar_Ident.lid,FStar_Parser_AST.term) FStar_Pervasives_Native.tuple2 ->
      FStar_Pprint.document)
  =
  fun ps  ->
    fun uu____6169  ->
      match uu____6169 with
      | (lid,e) ->
          let uu____6176 =
            let uu____6177 = p_qlident lid  in
            let uu____6178 =
              let uu____6179 = p_noSeqTerm ps false e  in
              FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.equals uu____6179
               in
            FStar_Pprint.op_Hat_Slash_Hat uu____6177 uu____6178  in
          FStar_Pprint.group uu____6176

and (p_appTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.App uu____6181 when is_general_application e ->
        let uu____6188 = head_and_args e  in
        (match uu____6188 with
         | (head1,args) ->
             let uu____6213 =
               let uu____6224 = FStar_ST.op_Bang should_print_fs_typ_app  in
               if uu____6224
               then
                 let uu____6254 =
                   FStar_Util.take
                     (fun uu____6278  ->
                        match uu____6278 with
                        | (uu____6283,aq) -> aq = FStar_Parser_AST.FsTypApp)
                     args
                    in
                 match uu____6254 with
                 | (fs_typ_args,args1) ->
                     let uu____6321 =
                       let uu____6322 = p_indexingTerm head1  in
                       let uu____6323 =
                         let uu____6324 =
                           FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
                            in
                         soft_surround_map_or_flow (Prims.parse_int "2")
                           (Prims.parse_int "0") FStar_Pprint.empty
                           FStar_Pprint.langle uu____6324 FStar_Pprint.rangle
                           p_fsTypArg fs_typ_args
                          in
                       FStar_Pprint.op_Hat_Hat uu____6322 uu____6323  in
                     (uu____6321, args1)
               else
                 (let uu____6336 = p_indexingTerm head1  in
                  (uu____6336, args))
                in
             (match uu____6213 with
              | (head_doc,args1) ->
                  let uu____6357 =
                    let uu____6358 =
                      FStar_Pprint.op_Hat_Hat head_doc FStar_Pprint.space  in
                    soft_surround_map_or_flow (Prims.parse_int "2")
                      (Prims.parse_int "0") head_doc uu____6358 break1
                      FStar_Pprint.empty p_argTerm args1
                     in
                  FStar_Pprint.group uu____6357))
    | FStar_Parser_AST.Construct (lid,args) when
        (is_general_construction e) &&
          (let uu____6378 = is_dtuple_constructor lid  in
           Prims.op_Negation uu____6378)
        ->
        (match args with
         | [] -> p_quident lid
         | arg::[] ->
             let uu____6396 =
               let uu____6397 = p_quident lid  in
               let uu____6398 = p_argTerm arg  in
               FStar_Pprint.op_Hat_Slash_Hat uu____6397 uu____6398  in
             FStar_Pprint.group uu____6396
         | hd1::tl1 ->
             let uu____6415 =
               let uu____6416 =
                 let uu____6417 =
                   let uu____6418 = p_quident lid  in
                   let uu____6419 = p_argTerm hd1  in
                   prefix2 uu____6418 uu____6419  in
                 FStar_Pprint.group uu____6417  in
               let uu____6420 =
                 let uu____6421 =
                   FStar_Pprint.separate_map break1 p_argTerm tl1  in
                 jump2 uu____6421  in
               FStar_Pprint.op_Hat_Hat uu____6416 uu____6420  in
             FStar_Pprint.group uu____6415)
    | uu____6426 -> p_indexingTerm e

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
         (let uu____6435 = p_indexingTerm e  in
          FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
            FStar_Pprint.langle uu____6435 FStar_Pprint.rangle))
    | (e,FStar_Parser_AST.Hash ) ->
        let uu____6437 = str "#"  in
        let uu____6438 = p_indexingTerm e  in
        FStar_Pprint.op_Hat_Hat uu____6437 uu____6438
    | (e,FStar_Parser_AST.Nothing ) -> p_indexingTerm e

and (p_fsTypArg :
  (FStar_Parser_AST.term,FStar_Parser_AST.imp) FStar_Pervasives_Native.tuple2
    -> FStar_Pprint.document)
  =
  fun uu____6440  ->
    match uu____6440 with | (e,uu____6446) -> p_indexingTerm e

and (p_indexingTerm_aux :
  (FStar_Parser_AST.term -> FStar_Pprint.document) ->
    FStar_Parser_AST.term -> FStar_Pprint.document)
  =
  fun exit1  ->
    fun e  ->
      match e.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".()"; FStar_Ident.idRange = uu____6451;_},e1::e2::[])
          ->
          let uu____6456 =
            let uu____6457 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6458 =
              let uu____6459 =
                let uu____6460 = p_term false false e2  in
                soft_parens_with_nesting uu____6460  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6459  in
            FStar_Pprint.op_Hat_Hat uu____6457 uu____6458  in
          FStar_Pprint.group uu____6456
      | FStar_Parser_AST.Op
          ({ FStar_Ident.idText = ".[]"; FStar_Ident.idRange = uu____6461;_},e1::e2::[])
          ->
          let uu____6466 =
            let uu____6467 = p_indexingTerm_aux p_atomicTermNotQUident e1  in
            let uu____6468 =
              let uu____6469 =
                let uu____6470 = p_term false false e2  in
                soft_brackets_with_nesting uu____6470  in
              FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6469  in
            FStar_Pprint.op_Hat_Hat uu____6467 uu____6468  in
          FStar_Pprint.group uu____6466
      | uu____6471 -> exit1 e

and (p_indexingTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  -> p_indexingTerm_aux p_atomicTerm e

and (p_atomicTerm : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.LetOpen (lid,e1) ->
        let uu____6476 = p_quident lid  in
        let uu____6477 =
          let uu____6478 =
            let uu____6479 = p_term false false e1  in
            soft_parens_with_nesting uu____6479  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6478  in
        FStar_Pprint.op_Hat_Hat uu____6476 uu____6477
    | FStar_Parser_AST.Name lid -> p_quident lid
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6485 = str (FStar_Ident.text_of_id op)  in
        let uu____6486 = p_atomicTerm e1  in
        FStar_Pprint.op_Hat_Hat uu____6485 uu____6486
    | uu____6487 -> p_atomicTermNotQUident e

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
         | uu____6494 -> p_constant c)
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.true_lid -> str "True"
    | FStar_Parser_AST.Name lid when
        FStar_Ident.lid_equals lid FStar_Parser_Const.false_lid ->
        str "False"
    | FStar_Parser_AST.Op (op,e1::[]) when is_general_prefix_op op ->
        let uu____6501 = str (FStar_Ident.text_of_id op)  in
        let uu____6502 = p_atomicTermNotQUident e1  in
        FStar_Pprint.op_Hat_Hat uu____6501 uu____6502
    | FStar_Parser_AST.Op (op,[]) ->
        let uu____6506 =
          let uu____6507 =
            let uu____6508 = str (FStar_Ident.text_of_id op)  in
            let uu____6509 =
              FStar_Pprint.op_Hat_Hat FStar_Pprint.space FStar_Pprint.rparen
               in
            FStar_Pprint.op_Hat_Hat uu____6508 uu____6509  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.space uu____6507  in
        FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen uu____6506
    | FStar_Parser_AST.Construct (lid,args) when is_dtuple_constructor lid ->
        let uu____6524 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lparen FStar_Pprint.bar  in
        let uu____6525 =
          let uu____6526 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          let uu____6527 = FStar_List.map FStar_Pervasives_Native.fst args
             in
          FStar_Pprint.separate_map uu____6526 p_tmEq uu____6527  in
        let uu____6534 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rparen  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6524 uu____6525 uu____6534
    | FStar_Parser_AST.Project (e1,lid) ->
        let uu____6537 =
          let uu____6538 = p_atomicTermNotQUident e1  in
          let uu____6539 =
            let uu____6540 = p_qlident lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6540  in
          FStar_Pprint.prefix (Prims.parse_int "2") (Prims.parse_int "0")
            uu____6538 uu____6539
           in
        FStar_Pprint.group uu____6537
    | uu____6541 -> p_projectionLHS e

and (p_projectionLHS : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun e  ->
    match e.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Var lid -> p_qlident lid
    | FStar_Parser_AST.Projector (constr_lid,field_lid) ->
        let uu____6546 = p_quident constr_lid  in
        let uu____6547 =
          let uu____6548 =
            let uu____6549 = p_lident field_lid  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6549  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6548  in
        FStar_Pprint.op_Hat_Hat uu____6546 uu____6547
    | FStar_Parser_AST.Discrim constr_lid ->
        let uu____6551 = p_quident constr_lid  in
        FStar_Pprint.op_Hat_Hat uu____6551 FStar_Pprint.qmark
    | FStar_Parser_AST.Paren e1 ->
        let uu____6553 = p_term false false e1  in
        soft_parens_with_nesting uu____6553
    | uu____6554 when is_array e ->
        let es = extract_from_list e  in
        let uu____6558 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.lbracket FStar_Pprint.bar  in
        let uu____6559 =
          let uu____6560 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          separate_map_or_flow_last uu____6560
            (fun ps  -> p_noSeqTerm ps false) es
           in
        let uu____6563 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bar FStar_Pprint.rbracket  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6558 uu____6559 uu____6563
    | uu____6564 when is_list e ->
        let uu____6565 =
          let uu____6566 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6567 = extract_from_list e  in
          separate_map_or_flow_last uu____6566
            (fun ps  -> p_noSeqTerm ps false) uu____6567
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          FStar_Pprint.lbracket uu____6565 FStar_Pprint.rbracket
    | uu____6572 when is_lex_list e ->
        let uu____6573 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.percent FStar_Pprint.lbracket
           in
        let uu____6574 =
          let uu____6575 = FStar_Pprint.op_Hat_Hat FStar_Pprint.semi break1
             in
          let uu____6576 = extract_from_list e  in
          separate_map_or_flow_last uu____6575
            (fun ps  -> p_noSeqTerm ps false) uu____6576
           in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "1")
          uu____6573 uu____6574 FStar_Pprint.rbracket
    | uu____6581 when is_ref_set e ->
        let es = extract_from_ref_set e  in
        let uu____6585 =
          FStar_Pprint.op_Hat_Hat FStar_Pprint.bang FStar_Pprint.lbrace  in
        let uu____6586 =
          let uu____6587 = FStar_Pprint.op_Hat_Hat FStar_Pprint.comma break1
             in
          separate_map_or_flow uu____6587 p_appTerm es  in
        FStar_Pprint.surround (Prims.parse_int "2") (Prims.parse_int "0")
          uu____6585 uu____6586 FStar_Pprint.rbrace
    | FStar_Parser_AST.Labeled (e1,s,b) ->
        let uu____6591 = str (Prims.strcat "(*" (Prims.strcat s "*)"))  in
        let uu____6592 = p_term false false e1  in
        FStar_Pprint.op_Hat_Slash_Hat uu____6591 uu____6592
    | FStar_Parser_AST.Op (op,args) when
        let uu____6599 = handleable_op op args  in
        Prims.op_Negation uu____6599 ->
        let uu____6600 =
          let uu____6601 =
            let uu____6602 =
              let uu____6603 =
                let uu____6604 =
                  FStar_Util.string_of_int (FStar_List.length args)  in
                Prims.strcat uu____6604
                  " arguments couldn't be handled by the pretty printer"
                 in
              Prims.strcat " with " uu____6603  in
            Prims.strcat (FStar_Ident.text_of_id op) uu____6602  in
          Prims.strcat "Operation " uu____6601  in
        failwith uu____6600
    | FStar_Parser_AST.Uvar uu____6605 ->
        failwith "Unexpected universe variable out of universe context"
    | FStar_Parser_AST.Wild  ->
        let uu____6606 = p_term false false e  in
        soft_parens_with_nesting uu____6606
    | FStar_Parser_AST.Const uu____6607 ->
        let uu____6608 = p_term false false e  in
        soft_parens_with_nesting uu____6608
    | FStar_Parser_AST.Op uu____6609 ->
        let uu____6616 = p_term false false e  in
        soft_parens_with_nesting uu____6616
    | FStar_Parser_AST.Tvar uu____6617 ->
        let uu____6618 = p_term false false e  in
        soft_parens_with_nesting uu____6618
    | FStar_Parser_AST.Var uu____6619 ->
        let uu____6620 = p_term false false e  in
        soft_parens_with_nesting uu____6620
    | FStar_Parser_AST.Name uu____6621 ->
        let uu____6622 = p_term false false e  in
        soft_parens_with_nesting uu____6622
    | FStar_Parser_AST.Construct uu____6623 ->
        let uu____6634 = p_term false false e  in
        soft_parens_with_nesting uu____6634
    | FStar_Parser_AST.Abs uu____6635 ->
        let uu____6642 = p_term false false e  in
        soft_parens_with_nesting uu____6642
    | FStar_Parser_AST.App uu____6643 ->
        let uu____6650 = p_term false false e  in
        soft_parens_with_nesting uu____6650
    | FStar_Parser_AST.Let uu____6651 ->
        let uu____6672 = p_term false false e  in
        soft_parens_with_nesting uu____6672
    | FStar_Parser_AST.LetOpen uu____6673 ->
        let uu____6678 = p_term false false e  in
        soft_parens_with_nesting uu____6678
    | FStar_Parser_AST.Seq uu____6679 ->
        let uu____6684 = p_term false false e  in
        soft_parens_with_nesting uu____6684
    | FStar_Parser_AST.Bind uu____6685 ->
        let uu____6692 = p_term false false e  in
        soft_parens_with_nesting uu____6692
    | FStar_Parser_AST.If uu____6693 ->
        let uu____6700 = p_term false false e  in
        soft_parens_with_nesting uu____6700
    | FStar_Parser_AST.Match uu____6701 ->
        let uu____6716 = p_term false false e  in
        soft_parens_with_nesting uu____6716
    | FStar_Parser_AST.TryWith uu____6717 ->
        let uu____6732 = p_term false false e  in
        soft_parens_with_nesting uu____6732
    | FStar_Parser_AST.Ascribed uu____6733 ->
        let uu____6742 = p_term false false e  in
        soft_parens_with_nesting uu____6742
    | FStar_Parser_AST.Record uu____6743 ->
        let uu____6756 = p_term false false e  in
        soft_parens_with_nesting uu____6756
    | FStar_Parser_AST.Project uu____6757 ->
        let uu____6762 = p_term false false e  in
        soft_parens_with_nesting uu____6762
    | FStar_Parser_AST.Product uu____6763 ->
        let uu____6770 = p_term false false e  in
        soft_parens_with_nesting uu____6770
    | FStar_Parser_AST.Sum uu____6771 ->
        let uu____6778 = p_term false false e  in
        soft_parens_with_nesting uu____6778
    | FStar_Parser_AST.QForall uu____6779 ->
        let uu____6792 = p_term false false e  in
        soft_parens_with_nesting uu____6792
    | FStar_Parser_AST.QExists uu____6793 ->
        let uu____6806 = p_term false false e  in
        soft_parens_with_nesting uu____6806
    | FStar_Parser_AST.Refine uu____6807 ->
        let uu____6812 = p_term false false e  in
        soft_parens_with_nesting uu____6812
    | FStar_Parser_AST.NamedTyp uu____6813 ->
        let uu____6818 = p_term false false e  in
        soft_parens_with_nesting uu____6818
    | FStar_Parser_AST.Requires uu____6819 ->
        let uu____6826 = p_term false false e  in
        soft_parens_with_nesting uu____6826
    | FStar_Parser_AST.Ensures uu____6827 ->
        let uu____6834 = p_term false false e  in
        soft_parens_with_nesting uu____6834
    | FStar_Parser_AST.Attributes uu____6835 ->
        let uu____6838 = p_term false false e  in
        soft_parens_with_nesting uu____6838
    | FStar_Parser_AST.Quote uu____6839 ->
        let uu____6844 = p_term false false e  in
        soft_parens_with_nesting uu____6844
    | FStar_Parser_AST.VQuote uu____6845 ->
        let uu____6846 = p_term false false e  in
        soft_parens_with_nesting uu____6846

and (p_constant : FStar_Const.sconst -> FStar_Pprint.document) =
  fun uu___63_6847  ->
    match uu___63_6847 with
    | FStar_Const.Const_effect  -> str "Effect"
    | FStar_Const.Const_unit  -> str "()"
    | FStar_Const.Const_bool b -> FStar_Pprint.doc_of_bool b
    | FStar_Const.Const_float x -> str (FStar_Util.string_of_float x)
    | FStar_Const.Const_char x -> FStar_Pprint.doc_of_char x
    | FStar_Const.Const_string (s,uu____6852) ->
        let uu____6853 = str s  in FStar_Pprint.dquotes uu____6853
    | FStar_Const.Const_bytearray (bytes,uu____6855) ->
        let uu____6860 =
          let uu____6861 = str (FStar_Util.string_of_bytes bytes)  in
          FStar_Pprint.dquotes uu____6861  in
        let uu____6862 = str "B"  in
        FStar_Pprint.op_Hat_Hat uu____6860 uu____6862
    | FStar_Const.Const_int (repr,sign_width_opt) ->
        let signedness uu___61_6880 =
          match uu___61_6880 with
          | FStar_Const.Unsigned  -> str "u"
          | FStar_Const.Signed  -> FStar_Pprint.empty  in
        let width uu___62_6884 =
          match uu___62_6884 with
          | FStar_Const.Int8  -> str "y"
          | FStar_Const.Int16  -> str "s"
          | FStar_Const.Int32  -> str "l"
          | FStar_Const.Int64  -> str "L"  in
        let ending =
          default_or_map FStar_Pprint.empty
            (fun uu____6895  ->
               match uu____6895 with
               | (s,w) ->
                   let uu____6902 = signedness s  in
                   let uu____6903 = width w  in
                   FStar_Pprint.op_Hat_Hat uu____6902 uu____6903)
            sign_width_opt
           in
        let uu____6904 = str repr  in
        FStar_Pprint.op_Hat_Hat uu____6904 ending
    | FStar_Const.Const_range_of  -> str "range_of"
    | FStar_Const.Const_set_range_of  -> str "set_range_of"
    | FStar_Const.Const_range r ->
        let uu____6906 = FStar_Range.string_of_range r  in str uu____6906
    | FStar_Const.Const_reify  -> str "reify"
    | FStar_Const.Const_reflect lid ->
        let uu____6908 = p_quident lid  in
        let uu____6909 =
          let uu____6910 =
            let uu____6911 = str "reflect"  in
            FStar_Pprint.op_Hat_Hat FStar_Pprint.dot uu____6911  in
          FStar_Pprint.op_Hat_Hat FStar_Pprint.qmark uu____6910  in
        FStar_Pprint.op_Hat_Hat uu____6908 uu____6909

and (p_universe : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    let uu____6913 = str "u#"  in
    let uu____6914 = p_atomicUniverse u  in
    FStar_Pprint.op_Hat_Hat uu____6913 uu____6914

and (p_universeFrom : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____6916;_},u1::u2::[])
        ->
        let uu____6921 =
          let uu____6922 = p_universeFrom u1  in
          let uu____6923 =
            let uu____6924 = p_universeFrom u2  in
            FStar_Pprint.op_Hat_Slash_Hat FStar_Pprint.plus uu____6924  in
          FStar_Pprint.op_Hat_Slash_Hat uu____6922 uu____6923  in
        FStar_Pprint.group uu____6921
    | FStar_Parser_AST.App uu____6925 ->
        let uu____6932 = head_and_args u  in
        (match uu____6932 with
         | (head1,args) ->
             (match head1.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Var maybe_max_lid when
                  FStar_Ident.lid_equals maybe_max_lid
                    FStar_Parser_Const.max_lid
                  ->
                  let uu____6958 =
                    let uu____6959 = p_qlident FStar_Parser_Const.max_lid  in
                    let uu____6960 =
                      FStar_Pprint.separate_map FStar_Pprint.space
                        (fun uu____6968  ->
                           match uu____6968 with
                           | (u1,uu____6974) -> p_atomicUniverse u1) args
                       in
                    op_Hat_Slash_Plus_Hat uu____6959 uu____6960  in
                  FStar_Pprint.group uu____6958
              | uu____6975 ->
                  let uu____6976 =
                    let uu____6977 = FStar_Parser_AST.term_to_string u  in
                    FStar_Util.format1 "Invalid term in universe context %s"
                      uu____6977
                     in
                  failwith uu____6976))
    | uu____6978 -> p_atomicUniverse u

and (p_atomicUniverse : FStar_Parser_AST.term -> FStar_Pprint.document) =
  fun u  ->
    match u.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Wild  -> FStar_Pprint.underscore
    | FStar_Parser_AST.Const (FStar_Const.Const_int (r,sw)) ->
        p_constant (FStar_Const.Const_int (r, sw))
    | FStar_Parser_AST.Uvar id1 -> str (FStar_Ident.text_of_id id1)
    | FStar_Parser_AST.Paren u1 ->
        let uu____7002 = p_universeFrom u1  in
        soft_parens_with_nesting uu____7002
    | FStar_Parser_AST.Op
        ({ FStar_Ident.idText = "+"; FStar_Ident.idRange = uu____7003;_},uu____7004::uu____7005::[])
        ->
        let uu____7008 = p_universeFrom u  in
        soft_parens_with_nesting uu____7008
    | FStar_Parser_AST.App uu____7009 ->
        let uu____7016 = p_universeFrom u  in
        soft_parens_with_nesting uu____7016
    | uu____7017 ->
        let uu____7018 =
          let uu____7019 = FStar_Parser_AST.term_to_string u  in
          FStar_Util.format1 "Invalid term in universe context %s" uu____7019
           in
        failwith uu____7018

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
       | FStar_Parser_AST.Module (uu____7059,decls) ->
           let uu____7065 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7065
             (FStar_Pprint.separate FStar_Pprint.hardline)
       | FStar_Parser_AST.Interface (uu____7074,decls,uu____7076) ->
           let uu____7081 =
             FStar_All.pipe_right decls (FStar_List.map decl_to_document)  in
           FStar_All.pipe_right uu____7081
             (FStar_Pprint.separate FStar_Pprint.hardline)
        in
     FStar_ST.op_Colon_Equals should_print_fs_typ_app false; res)
  
let (comments_to_document :
  (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2 Prims.list
    -> FStar_Pprint.document)
  =
  fun comments  ->
    FStar_Pprint.separate_map FStar_Pprint.hardline
      (fun uu____7132  ->
         match uu____7132 with | (comment,range) -> str comment) comments
  
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
        | FStar_Parser_AST.Module (uu____7172,decls) -> decls
        | FStar_Parser_AST.Interface (uu____7178,decls,uu____7180) -> decls
         in
      FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
      (match decls with
       | [] -> (FStar_Pprint.empty, comments)
       | d::ds ->
           let uu____7225 =
             match ds with
             | {
                 FStar_Parser_AST.d = FStar_Parser_AST.Pragma
                   (FStar_Parser_AST.LightOff );
                 FStar_Parser_AST.drange = uu____7238;
                 FStar_Parser_AST.doc = uu____7239;
                 FStar_Parser_AST.quals = uu____7240;
                 FStar_Parser_AST.attrs = uu____7241;_}::uu____7242 ->
                 let d0 = FStar_List.hd ds  in
                 let uu____7248 =
                   let uu____7251 =
                     let uu____7254 = FStar_List.tl ds  in d :: uu____7254
                      in
                   d0 :: uu____7251  in
                 (uu____7248, (d0.FStar_Parser_AST.drange))
             | uu____7259 -> ((d :: ds), (d.FStar_Parser_AST.drange))  in
           (match uu____7225 with
            | (decls1,first_range) ->
                let extract_decl_range d1 = d1.FStar_Parser_AST.drange  in
                (FStar_ST.op_Colon_Equals comment_stack comments;
                 (let initial_comment =
                    let uu____7317 = FStar_Range.start_of_range first_range
                       in
                    place_comments_until_pos (Prims.parse_int "0")
                      (Prims.parse_int "1") uu____7317 FStar_Pprint.empty
                     in
                  let doc1 =
                    separate_map_with_comments FStar_Pprint.empty
                      FStar_Pprint.empty decl_to_document decls1
                      extract_decl_range
                     in
                  let comments1 = FStar_ST.op_Bang comment_stack  in
                  FStar_ST.op_Colon_Equals comment_stack [];
                  FStar_ST.op_Colon_Equals should_print_fs_typ_app false;
                  (let uu____7413 =
                     FStar_Pprint.op_Hat_Hat initial_comment doc1  in
                   (uu____7413, comments1))))))
  